import Solcore.Frontend.SourceCore.Internal.Carriers
import Solcore.SourceSemantics.CoreLowering.Internal.Data.Equality
import Solcore.Core.Fuel
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.AncestryPaired
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.BasicExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.LiteralsAndStagedValues
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.AncestryWorklists
import Solcore.SourceSemantics.Dynamic.GeneralizedClosure
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.Ancestry
import Solcore.SourceSemantics.Dynamic.Evidence

/-!
# Applied views and context frames

Context frames, applied provenance and materialization, the ledger and substitution agreement.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableContextFrames
/-! Finite semantics of the ordinary Core callable-frame helpers. Reference
selection is restricted to heap-independent lexical projection paths. The next
frame and body run under their actual administrative binders; no exact-value
weakening theorem for arbitrary closure-producing code is assumed.

These laws authenticate native evaluation and restoration, not source ownership
of origin/view words, lexical capture metadata, or dynamic source ancestry. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableContextFrames
open Core Frontend.SourceCoreCallableContextFrames
open DataEquality (Selects)
abbrev ContextFrame := Frontend.SourceCoreCallableContextFrames.Frame

/-- The helper restores exactly its one administrative cell. All other writes
and allocations remain as the body left them, including language failures. -/
theorem withFrame_evaluates {environment : Environment} {before nextStore bodyStore : Store}
    {reference next body : Expr} {frameType : Ty} {location : Location}
    {saved installedValue result : Value}
    (referenceSelected : Selects environment reference (.cellRef frameType location))
    (savedRead : before.read? location = some saved)
    (nextEvaluation : Evaluates (saved :: environment) before (next.weakenAt 0) installedValue nextStore)
    (bodyEvaluation : Evaluates (.unit :: saved :: environment) (nextStore.set location installedValue)
      ((body.weakenAt 0).weakenAt 0) result bodyStore) :
    Evaluates environment before (withFrame reference next body) result (bodyStore.set location saved) := by
  have beforeBound : location < before.length := (List.getElem?_eq_some_iff.mp savedRead).choose
  have nextBound : location < nextStore.length := Nat.lt_of_lt_of_le beforeBound (evaluation_store_length_monotone nextEvaluation)
  have bodyBound : location < bodyStore.length := by
    have grows := evaluation_store_length_monotone bodyEvaluation
    simp only [List.length_set] at grows
    exact Nat.lt_of_lt_of_le nextBound grows
  apply Evaluates.letE (.loadCell (referenceSelected.evaluates before) savedRead)
  apply Evaluates.letE (.storeCell ((referenceSelected.weaken saved).evaluates before) savedRead nextEvaluation
    (Store.write?_eq_some_iff.mpr ⟨nextBound, rfl⟩))
  apply Evaluates.letE bodyEvaluation
  apply Evaluates.letE (.storeCell (oldValue := bodyStore[location]) (((referenceSelected.weaken saved).weaken .unit).weaken result |>.evaluates bodyStore)
    (by exact List.getElem?_eq_getElem bodyBound) (.var rfl)
    (Store.write?_eq_some_iff.mpr ⟨bodyBound, rfl⟩))
  exact .var rfl

/-- Inversion extracts actual child evaluations from a completed helper. It
never assumes that a shifted closure body is equal to an unshifted result. -/
theorem withFrame_reflects {environment : Environment} {before finalStore : Store}
    {reference next body : Expr} {frameType : Ty} {location : Location} {saved result : Value}
    (referenceSelected : Selects environment reference (.cellRef frameType location))
    (savedRead : before.read? location = some saved)
    (evaluation : Evaluates environment before (withFrame reference next body) result finalStore) :
    ∃ installedValue nextStore bodyStore,
      Evaluates (saved :: environment) before (next.weakenAt 0) installedValue nextStore ∧
      Evaluates (.unit :: saved :: environment) (nextStore.set location installedValue)
        ((body.weakenAt 0).weakenAt 0) result bodyStore ∧
      finalStore = bodyStore.set location saved := by
  cases evaluation with
  | letE save remaining =>
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic save (.loadCell (referenceSelected.evaluates before) savedRead)
    cases remaining with
    | letE install remaining =>
      cases install with
      | storeCell referenceEvaluation _ nextEvaluation written =>
        obtain ⟨referenceEqual, storeEqual⟩ := evaluation_deterministic referenceEvaluation ((referenceSelected.weaken _).evaluates _)
        cases storeEqual
        cases referenceEqual
        obtain ⟨_, rfl⟩ := Store.write?_eq_some_iff.mp written
        cases remaining with
        | letE bodyEvaluation restore =>
          cases restore with
          | letE restored returned =>
            cases restored with
            | storeCell selected _ oldEvaluation written =>
              obtain ⟨referenceEqual, storeEqual⟩ := evaluation_deterministic selected
                ((((referenceSelected.weaken _).weaken .unit).weaken _).evaluates _)
              cases storeEqual
              cases referenceEqual
              cases oldEvaluation with
              | var found =>
                simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at found
                cases found
                cases returned with
                | var found =>
                  simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at found
                  cases found
                  exact ⟨_, _, _, nextEvaluation, bodyEvaluation, (Store.write?_eq_some_iff.mp written).2⟩

theorem withFrame_iff {environment : Environment} {before finalStore : Store}
    {reference next body : Expr} {frameType : Ty} {location : Location} {saved result : Value}
    (referenceSelected : Selects environment reference (.cellRef frameType location))
    (savedRead : before.read? location = some saved) :
    Evaluates environment before (withFrame reference next body) result finalStore ↔
    ∃ installedValue nextStore bodyStore,
      Evaluates (saved :: environment) before (next.weakenAt 0) installedValue nextStore ∧
      Evaluates (.unit :: saved :: environment) (nextStore.set location installedValue)
        ((body.weakenAt 0).weakenAt 0) result bodyStore ∧
      finalStore = bodyStore.set location saved := by
  constructor
  · exact withFrame_reflects referenceSelected savedRead
  · rintro ⟨_, _, _, nextEvaluation, bodyEvaluation, rfl⟩
    exact withFrame_evaluates referenceSelected savedRead nextEvaluation bodyEvaluation

theorem withFrame_restores {environment : Environment} {before finalStore : Store}
    {reference next body : Expr} {frameType : Ty} {location : Location} {saved result : Value}
    (referenceSelected : Selects environment reference (.cellRef frameType location))
    (savedRead : before.read? location = some saved)
    (evaluation : Evaluates environment before (withFrame reference next body) result finalStore) :
    finalStore.read? location = some saved ∧
    ∃ bodyStore : Store, finalStore.length = bodyStore.length ∧
      (∀ other, other ≠ location → finalStore.read? other = bodyStore.read? other) := by
  obtain ⟨installedValue, nextStore, bodyStore, nextEvaluation, bodyEvaluation, rfl⟩ :=
    withFrame_reflects referenceSelected savedRead evaluation
  have beforeBound : location < before.length := (List.getElem?_eq_some_iff.mp savedRead).choose
  have nextBound := Nat.lt_of_lt_of_le beforeBound (evaluation_store_length_monotone nextEvaluation)
  have bodyBound : location < bodyStore.length := by
    have grows := evaluation_store_length_monotone bodyEvaluation
    simp only [List.length_set] at grows
    exact Nat.lt_of_lt_of_le nextBound grows
  have written : bodyStore.write? location saved = some (bodyStore.set location saved) :=
    Store.write?_eq_some_iff.mpr ⟨bodyBound, rfl⟩
  exact ⟨Store.write?_reads_written written, bodyStore, List.length_set,
    fun _ different => Store.write?_preserves_other written different⟩

theorem withFrame_run_done_iff {environment : Environment} {before finalStore : Store}
    {reference next body : Expr} {frameType : Ty} {location : Location} {saved result : Value}
    (referenceSelected : Selects environment reference (.cellRef frameType location))
    (savedRead : before.read? location = some saved) :
    (∃ fuel, runStateful fuel (.initial (withFrame reference next body) environment before) = .done result finalStore) ↔
    ∃ installedValue nextStore bodyStore,
      Evaluates (saved :: environment) before (next.weakenAt 0) installedValue nextStore ∧
      Evaluates (.unit :: saved :: environment) (nextStore.set location installedValue)
        ((body.weakenAt 0).weakenAt 0) result bodyStore ∧
      finalStore = bodyStore.set location saved := by
  constructor
  · rintro ⟨fuel, completed⟩
    exact withFrame_reflects referenceSelected savedRead (runStateful_evaluation_sound completed)
  · intro children
    exact evaluation_runStateful_complete ((withFrame_iff referenceSelected savedRead).mpr children)

theorem withFrame_run {environment : Environment} {before nextStore bodyStore : Store}
    {reference next body : Expr} {frameType : Ty} {location : Location}
    {saved installedValue result : Value}
    (referenceSelected : Selects environment reference (.cellRef frameType location))
    (savedRead : before.read? location = some saved)
    (nextEvaluation : Evaluates (saved :: environment) before (next.weakenAt 0) installedValue nextStore)
    (bodyEvaluation : Evaluates (.unit :: saved :: environment) (nextStore.set location installedValue)
      ((body.weakenAt 0).weakenAt 0) result bodyStore) :
    (∃ required, ∀ fuel, required ≤ fuel →
      runStateful fuel (.initial (withFrame reference next body) environment before) = .done result (bodyStore.set location saved)) ∧
    (∀ fuel actual after,
      runStateful fuel (.initial (withFrame reference next body) environment before) = .done actual after →
        actual = result ∧ after = bodyStore.set location saved) := by
  have evaluated := withFrame_evaluates referenceSelected savedRead nextEvaluation bodyEvaluation
  exact ⟨evaluation_runStateful_complete_with_sufficient_fuel evaluated,
    fun _ _ _ ran => evaluation_deterministic (runStateful_evaluation_sound ran) evaluated⟩

/-- The usual administrative frame allocation has an exact append-only cell. -/
theorem allocate_evaluates {layout : Layout} {environment : Environment} {before after : Store}
    {body : Expr} {result : Value}
    (evaluated : Evaluates (.cellRef layout.type before.length :: environment)
      (before ++ [encode layout .empty]) body result after) :
    Evaluates environment before (allocate layout body) result after :=
  .letE (.newCell (.construct .unit)) evaluated

theorem allocate_reflects {layout : Layout} {environment : Environment} {before after : Store}
    {body : Expr} {result : Value}
    (evaluated : Evaluates environment before (allocate layout body) result after) :
    Evaluates (.cellRef layout.type before.length :: environment)
      (before ++ [encode layout .empty]) body result after := by
  cases evaluated with
  | letE allocated body =>
    cases allocated with
    | newCell value =>
      cases value with
      | construct unit => cases unit; exact body

/-- Only an incoming leading view whose target is this lambda survives.
Its parent is rebased onto the lexically captured frame. -/
def selectedFrame (origin : Word) (captured : ContextFrame) : ContextFrame → ContextFrame
  | .view id target _ => if target = origin then .lambda origin (.view id origin captured) else .lambda origin captured
  | _ => .lambda origin captured

private theorem lambda_selected {layout : Layout} {environment : Environment} {captured : Expr}
    {frame : ContextFrame} (selected : Selects environment captured (encode layout frame))
    (origin : Word) (store : Store) :
    Evaluates environment store (lambda layout origin captured) (encode layout (.lambda origin frame)) store :=
  .construct (.pair .word (selected.evaluates store))

theorem lambdaFrame_evaluates {layout : Layout} {environment : Environment} {captured current : Expr}
    {capturedFrame currentFrame : ContextFrame} (origin : Word)
    (capturedSelected : Selects environment captured (encode layout capturedFrame))
    (currentSelected : Selects environment current (encode layout currentFrame)) (store : Store) :
    Evaluates environment store (lambdaFrame layout origin captured current)
      (encode layout (selectedFrame origin capturedFrame currentFrame)) store := by
  cases currentFrame with
  | empty =>
    exact .matchData (currentSelected.evaluates store) rfl rfl (by
      simpa [lambda, Expr.weakenAt, selectedFrame] using lambda_selected (capturedSelected.weaken .unit) origin store)
  | named id =>
    exact .matchData (currentSelected.evaluates store) rfl rfl (by
      simpa [lambda, Expr.weakenAt, selectedFrame] using lambda_selected (capturedSelected.weaken (.word id)) origin store)
  | lambda id parent =>
    exact .matchData (currentSelected.evaluates store) rfl rfl (by
      simpa [lambda, Expr.weakenAt, selectedFrame] using lambda_selected (capturedSelected.weaken (.pair (.word id) (encode layout parent))) origin store)
  | view id target parent =>
    apply Evaluates.matchData (currentSelected.evaluates store) rfl (by rfl)
    by_cases equal : target = origin
    · simp only [selectedFrame, if_pos equal]
      apply Evaluates.ifTrue (.binary (.first (.second (.var rfl))) .word ?_)
      · exact .construct (.pair .word (.construct (.pair (.first (.var rfl))
          (.pair .word ((capturedSelected.weaken _).evaluates store)))))
      · simp [BinaryOp.apply, equal]
    · simp only [selectedFrame, if_neg equal]
      apply Evaluates.ifFalse (.binary (.first (.second (.var rfl))) .word ?_)
      · simpa [lambda, Expr.weakenAt, selectedFrame] using lambda_selected (capturedSelected.weaken (.pair (.word id) (.pair (.word target) (encode layout parent)))) origin store
      · simp [BinaryOp.apply, equal]

/-- Reflection is unconditional on a successful source trace: lexical native
selection determines the exact finite result and unchanged native store. -/
theorem lambdaFrame_reflects {layout : Layout} {environment : Environment} {before after : Store}
    {captured current : Expr} {capturedFrame currentFrame : ContextFrame} {origin : Word} {result : Value}
    (capturedSelected : Selects environment captured (encode layout capturedFrame))
    (currentSelected : Selects environment current (encode layout currentFrame))
    (evaluated : Evaluates environment before (lambdaFrame layout origin captured current) result after) :
    result = encode layout (selectedFrame origin capturedFrame currentFrame) ∧ after = before :=
  evaluation_deterministic evaluated (lambdaFrame_evaluates origin capturedSelected currentSelected before)

theorem lambdaFrame_run {layout : Layout} {environment : Environment} {store : Store}
    {captured current : Expr} {capturedFrame currentFrame : ContextFrame} (origin : Word)
    (capturedSelected : Selects environment captured (encode layout capturedFrame))
    (currentSelected : Selects environment current (encode layout currentFrame)) :
    (∃ required, ∀ fuel, required ≤ fuel →
      runStateful fuel (.initial (lambdaFrame layout origin captured current) environment store) =
        .done (encode layout (selectedFrame origin capturedFrame currentFrame)) store) ∧
    (∀ fuel actual after,
      runStateful fuel (.initial (lambdaFrame layout origin captured current) environment store) = .done actual after →
        actual = encode layout (selectedFrame origin capturedFrame currentFrame) ∧ after = store) :=
  ⟨evaluation_runStateful_complete_with_sufficient_fuel (lambdaFrame_evaluates origin capturedSelected currentSelected store),
    fun _ _ _ ran => lambdaFrame_reflects capturedSelected currentSelected (runStateful_evaluation_sound ran)⟩

/-- Real exhaustion retains the continuation that performs restoration. A
checkpoint need not itself have the caller frame installed. -/
theorem withFrame_resume {environment : Environment} {before : Store} {reference next body : Expr}
    {spent : Nat} {checkpoint : State}
    (exhausted : runStateful spent (.initial (withFrame reference next body) environment before) = .outOfFuel checkpoint)
    (additional : Nat) :
    runStateful additional checkpoint = runStateful (spent + additional)
      (.initial (withFrame reference next body) environment before) := runStateful_resume exhausted additional

/-- A genuine suspended helper with finite child evaluations has enough
remaining fuel to finish restoration. Before completion the frame may still
be the callee's, and the checkpoint is retained unchanged. -/
theorem withFrame_resumed_finishes {environment : Environment} {before nextStore bodyStore : Store}
    {reference next body : Expr} {frameType : Ty} {location : Location}
    {saved installedValue result : Value} {spent : Nat} {checkpoint : State}
    (referenceSelected : Selects environment reference (.cellRef frameType location))
    (savedRead : before.read? location = some saved)
    (nextEvaluation : Evaluates (saved :: environment) before (next.weakenAt 0) installedValue nextStore)
    (bodyEvaluation : Evaluates (.unit :: saved :: environment) (nextStore.set location installedValue)
      ((body.weakenAt 0).weakenAt 0) result bodyStore)
    (exhausted : runStateful spent (.initial (withFrame reference next body) environment before) = .outOfFuel checkpoint) :
    ∃ remaining, ∀ additional, remaining ≤ additional →
      runStateful additional checkpoint = .done result (bodyStore.set location saved) := by
  obtain ⟨required, sufficient⟩ := (withFrame_run referenceSelected savedRead nextEvaluation bodyEvaluation).1
  refine ⟨required, fun additional enough => ?_⟩
  rw [withFrame_resume exhausted additional]
  exact sufficient _ (by omega)

end Solcore.SourceSemantics.CoreLowering.CallableContextFrames
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableAppliedViewProvenance
/-! Exact read and application recipes retain both parent histories. Their
semantic substitution and native compilation context stay separate. The
complete rewritten source, ordered witnesses and lexical header are preserved;
no body execution or source-table alignment is inferred from a native type. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableAppliedViewProvenance
open Frontend SourceInference TypeSystem
open SourceCoreCallableAncestryReadRecipes

abbrev MetadataState := SourceCoreCallableAncestryReadRecipes.State

abbrev Frame := SourceCoreCallablePairedFrames.Frame

/-- Two authenticated parent states and the actual metadata factories. -/
structure Recipe {checked : Checked} {base : Base checked} (inputs : Inputs base)
    (callerFrame lexicalFrame : Frame) (caller lexical : MetadataState) (id target : Core.Word) where
  callerHistory : CallableAncestryPairedLookup.Authenticates inputs callerFrame (some caller)
  lexicalHistory : CallableAncestryPairedLookup.Authenticates inputs lexicalFrame (some lexical)
  read : Read inputs caller id target
  readAccepted : prepareRead inputs caller id target = .ok read
  applied : Applied read lexical
  appliedAccepted : applyRead read lexical = .ok applied

namespace Recipe
variable {checked : Checked} {base : Base checked} {inputs : Inputs base}
  {callerFrame lexicalFrame : Frame} {caller lexical : MetadataState} {id target : Core.Word}

/-- A real completed view lookup supplies both factory receipts. -/
theorem of_view
    (callerHistory : CallableAncestryPairedLookup.Authenticates inputs callerFrame (some caller))
    (lexicalHistory : CallableAncestryPairedLookup.Authenticates inputs lexicalFrame (some lexical))
    {result : MetadataState}
    (accepted : SourceCoreCallableAncestryPairedPreparation.view? inputs caller lexical id target = some result) :
    ∃ recipe : Recipe inputs callerFrame lexicalFrame caller lexical id target,
      result = recipe.read.after lexical := by
  obtain ⟨read, applied, readAccepted, appliedAccepted, same⟩ :=
    CallableAncestryPairedValidation.view_receipts accepted
  exact ⟨⟨callerHistory, lexicalHistory, read, readAccepted, applied, appliedAccepted⟩, same⟩

variable (recipe : Recipe inputs callerFrame lexicalFrame caller lexical id target)

theorem view_accepted :
    SourceCoreCallableAncestryPairedPreparation.view? inputs caller lexical id target =
      some (recipe.read.after lexical) := by
  simp [SourceCoreCallableAncestryPairedPreparation.view?, recipe.readAccepted,
    recipe.appliedAccepted, Except.toOption]

theorem authenticated : CallableAncestryPairedLookup.Authenticates inputs
    (.appliedView id target callerFrame lexicalFrame) (some (recipe.read.after lexical)) :=
  .appliedView recipe.callerHistory recipe.lexicalHistory recipe.view_accepted

theorem full_source : (recipe.read.after lexical).metadata.source =
    SourceTypedRuntime.rewriteLocalRequirements recipe.read.witnesses
      (lexical.metadata.source.applySubstitution recipe.read.substitution) := rfl

theorem semantic_active : (recipe.read.after lexical).metadata.active =
    recipe.read.substitution.compose lexical.metadata.active := rfl

theorem native_active : (recipe.read.after lexical).nativeActive =
    recipe.read.entry.view.cumulative := rfl

theorem header : ExpressionForm.lambda
    (recipe.applied.parameters.map (TypedBinder.applySubstitution recipe.read.substitution))
    (recipe.read.substitution.apply recipe.applied.resultType) recipe.applied.body =
    recipe.read.template.node.form := recipe.applied.nativeHeader

theorem source_value (captured : SourceTypedRuntime.Environment)
    (evidence : SourceCompilationPlan.EvidenceEnvironment) :
    recipe.applied.sourceValue captured evidence =
      .instantiated recipe.read.substitution recipe.read.witnesses
        (.closure recipe.applied.parameters recipe.applied.resultType recipe.applied.body
          lexical.metadata.source lexical.metadata.owner captured evidence) := rfl

end Recipe

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β}
    {output : β} (accepted : (action >>= next) = .ok output) :
    ∃ input, action = .ok input ∧ next input = .ok output := by
  cases action with
  | error error => cases accepted
  | ok input => exact ⟨input, rfl, accepted⟩

private theorem mapError_ok {α ε δ : Type} {action : Except ε α} {f : ε → δ} {output : α}
    (accepted : action.mapError f = .ok output) : action = .ok output := by
  cases action <;> cases accepted <;> rfl

private theorem map_ok {α β ε : Type} {action : Except ε α} {f : α → β} {output : β}
    (accepted : action.map f = .ok output) : ∃ input, action = .ok input ∧ f input = output := by
  cases action with
  | error error => cases accepted
  | ok input => exact ⟨input, rfl, Except.ok.inj accepted⟩

private theorem exact_key {plan : SourceCompilationPlan.Plan} {key : SourceCompilationPlan.Key}
    {original : SourceSpecialization.SpecializedFunction}
    (accepted : SourceCompilationPlan.exactSpecialization plan key = .ok original) : original.key = key := by
  unfold SourceCompilationPlan.exactSpecialization at accepted
  split at accepted
  · cases accepted
  · next selected found =>
    cases accepted
    have member : original ∈ [original] := by simp
    rw [← found] at member
    exact of_decide_eq_true (List.mem_filter.mp member).2
  · cases accepted

private theorem exact_member {plan : SourceCompilationPlan.Plan} {key : SourceCompilationPlan.Key}
    {original candidate : SourceSpecialization.SpecializedFunction}
    (accepted : SourceCompilationPlan.exactSpecialization plan key = .ok original)
    (member : candidate ∈ plan.specializations) (same : candidate.key = key) : candidate = original := by
  unfold SourceCompilationPlan.exactSpecialization at accepted
  split at accepted
  · cases accepted
  · next selected found =>
    cases accepted
    have retained : candidate ∈ plan.specializations.filter (fun item => decide (item.key = key)) :=
      List.mem_filter.mpr ⟨member, by simpa using same⟩
    rw [found] at retained
    exact List.mem_singleton.mp retained
  · cases accepted

private theorem exactCaller_source {plan : SourceCompilationPlan.Plan}
    {binding : SourceCoreLocalPolymorphism.Binding} {original : SourceSpecialization.SpecializedFunction}
    (accepted : SourceCoreLocalEvidence.exactCaller plan binding = .ok original) :
    SourceCompilationPlan.exactSpecialization plan binding.caller = .ok original := by
  unfold SourceCoreLocalEvidence.exactCaller at accepted
  cases selected : SourceCompilationPlan.exactSpecialization plan binding.caller with
  | error error => simp [selected, Except.mapError, bind, Except.bind] at accepted
  | ok caller =>
    simp only [selected, Except.mapError, bind, Except.bind] at accepted
    split at accepted
    · cases accepted
    · split at accepted
      · cases accepted; rfl
      · cases accepted

private theorem prepared_canonical {program : CheckedProgram} {plan : SourceCompilationPlan.Plan}
    {candidate : SourceCoreLocalPolymorphism.Instance} {parent : Option SourceCoreLocalEvidence.Prepared}
    {prepared : SourceCoreLocalEvidence.Prepared}
    (accepted : SourceCoreLocalEvidence.prepare program plan candidate parent = .ok prepared) :
    ∃ original, SourceCompilationPlan.exactSpecialization plan prepared.caller.key = .ok original ∧
      prepared.source = original.function.typedBody.applySubstitution prepared.substitution := by
  unfold SourceCoreLocalEvidence.prepare at accepted
  obtain ⟨original, selected, accepted⟩ := bind_ok accepted
  have originalSelected := exactCaller_source selected
  have key := exact_key originalSelected
  simp only [bind, Except.bind, pure, Except.pure, Except.mapError] at accepted
  repeat' first | split at accepted | cases accepted
  all_goals exact ⟨original, by simpa only [SourceCoreLocalEvidence.contextualCaller, key] using originalSelected, rfl⟩

private theorem certified_source {program : CheckedProgram} {plan : SourceCompilationPlan.Plan}
    {candidates : List SourceCoreLocalPolymorphism.Instance} {parents : List SourceCoreLocalEvidence.Prepared}
    (accepted : SourceCoreStageCodebook.prepareContexts program plan candidates = .ok parents)
    (row : SourceCoreAllocationContexts.Certified plan parents)
    {original : SourceSpecialization.SpecializedFunction}
    (selected : SourceCompilationPlan.exactSpecialization plan row.context.owner = .ok original) :
    row.context.source = original.function.typedBody.applySubstitution row.context.active := by
  rw [row.sourceExact, row.activeExact]
  rw [row.ownerExact] at selected
  cases origin : row.origin with
  | root candidate member =>
    rw [origin] at selected
    have same := exact_member selected member rfl
    subst candidate
    simp only [SourceCoreAllocationContexts.Origin.source, SourceCoreAllocationContexts.Origin.active,
      EmptySourceSubstitution.source]
  | contextual prepared member =>
    rw [origin] at selected
    obtain ⟨candidate, parent, authentic⟩ := SourceCoreStageCodebook.prepareContexts_authentic accepted member
    obtain ⟨caller, found, source⟩ := prepared_canonical authentic
    cases Except.ok.inj (found.symm.trans selected)
    exact source


private theorem base_contexts {program : CheckedProgram} {plan : SourceCompilationPlan.Plan}
    {checked : Checked} {ownership : checked.signatures = program.signatures} {fuel : Nat}
    {base : Base checked}
    (accepted : SourceCoreCompatibleFunctions.prepareWithCatalog program plan checked ownership fuel = .ok base) :
    ∃ candidates, SourceCoreStageCodebook.prepareContexts base.sourceProgram base.plan candidates = .ok base.contexts := by
  unfold SourceCoreCompatibleFunctions.prepareWithCatalog at accepted
  obtain ⟨executable, _, accepted⟩ := bind_ok accepted
  obtain ⟨locals, _, accepted⟩ := bind_ok accepted
  obtain ⟨contexts, prepared, accepted⟩ := bind_ok accepted
  have prepared := mapError_ok prepared
  obtain ⟨functions, _, accepted⟩ := bind_ok accepted
  split at accepted
  · cases accepted
    exact ⟨_, prepared⟩
  · obtain ⟨diagnostics, _, accepted⟩ := bind_ok accepted
    split at accepted
    · obtain ⟨table, _, accepted⟩ := bind_ok accepted
      obtain ⟨callableDiagnostics, _, accepted⟩ := bind_ok accepted
      simp only [bind, Except.bind, pure, Except.pure] at accepted
      obtain ⟨locals, _, accepted⟩ := bind_ok accepted
      obtain ⟨closures, _, accepted⟩ := bind_ok accepted
      obtain ⟨sourceInputs, _, accepted⟩ := bind_ok accepted
      obtain ⟨entries, _, accepted⟩ := bind_ok accepted
      cases accepted
      exact ⟨_, prepared⟩
    · simp only [bind, Except.bind, pure, Except.pure] at accepted
      obtain ⟨closures, _, accepted⟩ := bind_ok accepted
      obtain ⟨sourceInputs, _, accepted⟩ := bind_ok accepted
      obtain ⟨entries, _, accepted⟩ := bind_ok accepted
      cases accepted
      exact ⟨_, prepared⟩

private theorem mapM_member {α β ε : Type} {f : α → Except ε β} {items : List α} {output : List β}
    (accepted : items.mapM f = .ok output) {value : β} (member : value ∈ output) :
    ∃ item, item ∈ items ∧ f item = .ok value := by
  induction items generalizing output with
  | nil => cases accepted; cases member
  | cons item items ih =>
    simp only [List.mapM_cons, bind, Except.bind, pure, Except.pure] at accepted
    cases first : f item with
    | error error => simp [first] at accepted
    | ok head =>
      simp only [first] at accepted
      cases rest : items.mapM f with
      | error error => simp [rest] at accepted
      | ok tail =>
        simp only [rest, Except.ok.injEq] at accepted
        subst output
        rcases List.mem_cons.mp member with rfl | member
        · exact ⟨item, List.mem_cons_self, first⟩
        · obtain ⟨child, member, selected⟩ := ih rest member
          exact ⟨child, List.mem_cons_of_mem item member, selected⟩

private theorem allocation_inventory {ambient : Core.DataEnvironment}
    {inventories : List SourceCoreAllocationCodebook.ContextInventory} {first : Nat}
    {prepared : SourceCoreAllocationCodebook.Prepared}
    (accepted : SourceCoreAllocationCodebook.prepare ambient inventories first = .ok prepared)
    {context : SourceCoreAllocationCodebook.IndexedContext} (member : context ∈ prepared.contexts) :
    context.inventory ∈ inventories := by
  unfold SourceCoreAllocationCodebook.prepare at accepted
  split at accepted
  · obtain ⟨_, _, accepted⟩ := bind_ok accepted
    split at accepted
    · obtain ⟨contexts, mapped, accepted⟩ := bind_ok accepted
      split at accepted
      · cases accepted
        obtain ⟨⟨inventory, index⟩, selected, compiled⟩ := mapM_member mapped member
        obtain ⟨key, _, compiled⟩ := bind_ok compiled
        obtain ⟨bindings, _, compiled⟩ := bind_ok compiled
        cases compiled
        exact List.fst_mem_of_mem_zipIdx selected
      · split at accepted
        · cases accepted
        · split at accepted <;> cases accepted
    · cases accepted
  · cases accepted

private theorem discovered_source {program : CheckedProgram} {plan : SourceCompilationPlan.Plan}
    {candidates : List SourceCoreLocalPolymorphism.Instance} {parents : List SourceCoreLocalEvidence.Prepared}
    (accepted : SourceCoreStageCodebook.prepareContexts program plan candidates = .ok parents)
    (rows : SourceCoreAllocationContexts.Inventory plan parents)
    {ambient : Core.DataEnvironment} {discovered : SourceCoreAllocationDiscovery.Prepared}
    (prepared : SourceCoreAllocationDiscovery.prepare ambient rows.contexts = .ok discovered)
    {owner : SourceCompilationPlan.Key} {active : TypeSystem.Substitution}
    {context : SourceCoreAllocationCodebook.IndexedContext}
    (found : discovered.metadata.contextAt? owner active = some context)
    {original : SourceSpecialization.SpecializedFunction}
    (selected : SourceCompilationPlan.exactSpecialization plan owner = .ok original) :
    context.inventory.source = original.function.typedBody.applySubstitution active := by
  obtain ⟨metadata, compiled, same⟩ := map_ok prepared
  cases same
  have member := allocation_inventory compiled (List.mem_of_find?_eq_some found)
  obtain ⟨row, rowMember, same⟩ := List.mem_map.mp member
  unfold SourceCoreAllocationCodebook.Prepared.contextAt? at found
  have fields := of_decide_eq_true (List.find?_some (p := fun candidate : SourceCoreAllocationCodebook.IndexedContext => decide (candidate.inventory.owner = owner ∧ candidate.inventory.active = active)) found)
  obtain ⟨certified, _, rfl⟩ := List.mem_map.mp rowMember
  rw [← same] at fields ⊢
  have fields : certified.context.owner = owner ∧ certified.context.active = active := fields
  rw [← fields.2]
  exact certified_source accepted certified (by rw [fields.1]; exact selected)


private theorem forIn_invariant {α β ε : Type} {items : List α} {initial final : β}
    {step : α → β → Except ε (ForInStep β)} {invariant : β → Prop}
    (accepted : forIn items initial step = .ok final) (start : invariant initial)
    (each : ∀ item, item ∈ items → ∀ state outcome, invariant state → step item state = .ok outcome →
      ∃ updated, outcome = .yield updated ∧ invariant updated) : invariant final := by
  induction items generalizing initial with
  | nil =>
    simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] at accepted
    exact accepted ▸ start
  | cons item items ih =>
    rw [List.forIn_cons] at accepted
    obtain ⟨outcome, ran, accepted⟩ := bind_ok accepted
    obtain ⟨updated, rfl, preserved⟩ := each item List.mem_cons_self initial outcome start ran
    exact ih accepted preserved (fun next member => each next (List.mem_cons_of_mem item member))

private def TemplateSource {checked : Checked} (base : Base checked)
    (template : SourceCoreLambdaTemplates.Lambda) : Prop :=
  ∃ original, SourceCompilationPlan.exactSpecialization base.plan template.owner = .ok original ∧
    original.function.typedBody.lookupExpression? template.id = some template.original ∧
    template.node = template.original.applySubstitution template.active

/-- Every field comes from the same successful template preparation. The
ordered parent witnesses and both source views are retained without rewriting
or discarding any row. -/
def PreparedTemplate {checked : Checked} (base : Base checked)
    (template : SourceCoreLambdaTemplates.Lambda) : Prop :=
  ∃ (receipts : SourceCoreAllocationContexts.Inventory base.plan base.contexts)
    (metadata : SourceCoreAllocationDiscovery.Prepared)
    (callable : SourceCoreGeneralFunctions.CallableContext)
    (entry : SourceCoreStageCodebook.Entry)
    (original : SourceSpecialization.SpecializedFunction)
    (parameters : List TypedBinder) (result : TypeSystem.Ty) (body : List StatementId),
    SourceCoreAllocationContexts.fromPrepared base.plan base.contexts = .ok receipts ∧
    SourceCoreAllocationDiscovery.prepare checked.catalog.definitions receipts.contexts = .ok metadata ∧
    base.callableContext = some callable ∧ entry ∈ callable.table.entries ∧
    entry.origin = .lambda template.owner template.id template.active ∧
    entry.id = template.descriptor ∧
    metadata.metadata.contextAt? template.owner template.active = some template.context ∧
    SourceCompilationPlan.exactSpecialization base.plan template.owner = .ok original ∧
    original.function.typedBody.lookupExpression? template.id = some template.original ∧
    template.originalSource = original.function.typedBody ∧
    template.principalSource = SourceTypedRuntime.rewriteLocalRequirements
      (((base.contexts.find? (fun parent => decide
        (parent.caller.key = template.owner ∧ parent.substitution = template.active))).map
          (·.witnesses)).getD [])
      (original.function.typedBody.applySubstitution template.active) ∧
    template.context.inventory.source.lookupExpression? template.id = some template.node ∧
    template.node.form = .lambda parameters result body ∧
    checked.catalog.project (TypeSystem.Ty.productMany (parameters.map (·.scheme.body))) =
      .ok template.parameterType ∧
    checked.catalog.project result = .ok template.resultType

/-- The sole preparation fold retains the actual selected table row and all
source and native header fields. -/
theorem prepared_template {checked : Checked} {base : Base checked}
    {inventory : SourceCoreLambdaTemplates.Inventory checked}
    (accepted : SourceCoreLambdaTemplates.prepare base = .ok inventory)
    {template : SourceCoreLambdaTemplates.Lambda} (member : template ∈ inventory.lambdas) :
    PreparedTemplate base template := by
  unfold SourceCoreLambdaTemplates.prepare at accepted
  obtain ⟨receipts, receiptsPrepared, accepted⟩ := bind_ok accepted
  have receiptsPrepared := mapError_ok receiptsPrepared
  obtain ⟨metadata, compiled, accepted⟩ := bind_ok accepted
  have compiled := mapError_ok compiled
  split at accepted
  · next callable callableFound =>
    simp only [bind, Except.bind, pure, Except.pure] at accepted
    obtain ⟨lambdas, loop, accepted⟩ := bind_ok accepted
    cases accepted
    have invariant : ∀ value ∈ lambdas, PreparedTemplate base value := by
      apply forIn_invariant (invariant := fun values => ∀ value ∈ values, PreparedTemplate base value) loop
      · intro value member; cases member
      · intro entry entryMember state outcome previous iteration
        cases origin : entry.origin with
        | named key =>
          simp only [origin] at iteration
          cases iteration
          exact ⟨state, rfl, previous⟩
        | builtin function =>
          simp only [origin] at iteration
          cases iteration
          exact ⟨state, rfl, previous⟩
        | lambda owner id active =>
          simp only [origin] at iteration
          split at iteration
          · next context found =>
            try simp only [bind, Except.bind, pure, Except.pure] at iteration
            obtain ⟨original, selected, iteration⟩ := bind_ok iteration
            have selected := mapError_ok selected
            split at iteration
            · next originalNode originalFound =>
              try simp only [bind, Except.bind, pure, Except.pure] at iteration
              split at iteration
              · next node nodeFound =>
                try simp only [bind, Except.bind, pure, Except.pure] at iteration
                split at iteration
                · next parameters result body shape =>
                  obtain ⟨parameterType, parameterProjected, iteration⟩ := bind_ok iteration
                  obtain ⟨resultType, resultProjected, iteration⟩ := bind_ok iteration
                  cases iteration
                  refine ⟨_, rfl, ?_⟩
                  intro value member
                  rcases List.mem_append.mp member with old | fresh
                  · exact previous value old
                  · cases List.mem_singleton.mp fresh
                    exact ⟨receipts, metadata, callable, entry, original, _, _, _,
                      receiptsPrepared, compiled, callableFound, entryMember, origin, rfl,
                      found, selected, originalFound, rfl, rfl, nodeFound, shape,
                      mapError_ok parameterProjected, mapError_ok resultProjected⟩
                · cases iteration
              · cases iteration
            · cases iteration
          · cases iteration
    exact invariant template member
  · cases accepted


private theorem template_source {checked : Checked} {base : Base checked}
    {candidates : List SourceCoreLocalPolymorphism.Instance}
    (contexts : SourceCoreStageCodebook.prepareContexts base.sourceProgram base.plan candidates = .ok base.contexts)
    {inventory : SourceCoreLambdaTemplates.Inventory checked}
    (accepted : SourceCoreLambdaTemplates.prepare base = .ok inventory)
    {template : SourceCoreLambdaTemplates.Lambda} (member : template ∈ inventory.lambdas) :
    TemplateSource base template := by
  obtain ⟨receipts, metadata, callable, entry, original, parameters, result, body,
    _, compiled, _, _, _, _, found, selected, originalFound, _, _, nodeFound, _, _, _⟩ :=
    prepared_template accepted member
  refine ⟨original, selected, originalFound, ?_⟩
  have source := discovered_source contexts receipts compiled found selected
  have substituted := Frontend.SourceTypedRuntime.TypedSource.lookupExpression?_applySubstitution
    original.function.typedBody template.active template.id template.original originalFound
  rw [source] at nodeFound
  exact Option.some.inj (nodeFound.symm.trans substituted)


private theorem sidecar_lookup {plan : SourceCompilationPlan.Plan} {key : SourceCompilationPlan.Key}
    {sidecar : SourceCoreStageContracts.Sidecar}
    (accepted : SourceCoreStageContracts.prepareSidecar plan key = .ok sidecar) :
    SourceCompilationPlan.exactSpecialization plan key = .ok sidecar.caller := by
  unfold SourceCoreStageContracts.prepareSidecar at accepted
  cases selected : SourceCompilationPlan.exactSpecialization plan key with
  | error error => simp [selected, Except.mapError, bind, Except.bind] at accepted
  | ok caller =>
    simp only [selected, Except.mapError, bind, Except.bind] at accepted
    cases valid : SourceCompilationPlan.validateSpecializationMetadataWith true caller with
    | error error => simp [valid, Functor.discard, Functor.mapConst, Except.map] at accepted
    | ok value =>
      simp only [valid] at accepted
      dsimp [Functor.discard, Functor.mapConst, Except.map] at accepted
      split at accepted
      · cases accepted
      · split at accepted
        · cases accepted; rfl
        · cases accepted

private def HeaderShape (node : ExpressionNode) (contract : SourceCoreStageContracts.Contract) : Prop :=
  ∃ parameters result body, node.form = .lambda parameters result body ∧
    contract.parameters = parameters ∧ contract.stagedResult = SourceCompilationPlan.sourceTypeIsComptimeOnly result

private theorem contract_header {plan : SourceCompilationPlan.Plan} {owner : SourceCompilationPlan.Key}
    {id : ExpressionId} {active : TypeSystem.Substitution} {arity : Nat}
    {attached : Option SourceCoreStageContracts.Contract}
    (authenticated : CallEntryCertificates.OriginContract plan (.lambda owner id active) arity attached)
    {original : SourceSpecialization.SpecializedFunction} {node : ExpressionNode}
    (selected : SourceCompilationPlan.exactSpecialization plan owner = .ok original)
    (found : original.function.typedBody.lookupExpression? id = some node) :
    ∃ contract, attached = some contract ∧ HeaderShape (node.applySubstitution active) contract := by
  cases authenticated with
  | originalLambda prepared accepted =>
    obtain ⟨receipt⟩ := CallContractCertificates.lambda_of_accepted accepted
    have same := Except.ok.inj (selected.symm.trans (sidecar_lookup prepared))
    subst original
    have nodeEq := CallContractCertificates.expression_unique receipt.selected (lookupExpression?_sound found)
    subst node
    exact ⟨_, rfl, receipt.parameters, receipt.result, receipt.body,
      by simpa only [EmptySourceSubstitution.expression] using receipt.form,
      receipt.parameters_eq, receipt.stagedResult⟩
  | contextualLambda prepared accepted =>
    obtain ⟨receipt⟩ := CallContractCertificates.contextualLambda_of_accepted accepted
    have same := Except.ok.inj (selected.symm.trans (sidecar_lookup prepared))
    subst original
    have nodeEq := CallContractCertificates.expression_unique receipt.selected (lookupExpression?_sound found)
    subst node
    refine ⟨_, rfl, _, _, receipt.body, ?_, receipt.parameters_eq, receipt.stagedResult⟩
    simp only [ExpressionNode.applySubstitution, receipt.form, ExpressionForm.applySubstitution]

/-- The source header is authenticated by both actual preparations. Its form
comes from the same selected template, while the contract comes from the full
original codebook factory. -/
structure CanonicalHeader {checked : Checked} {base : Base checked} (inputs : Inputs base)
    (template : SourceCoreLambdaTemplates.Lambda) (contract : SourceCoreStageContracts.Contract) : Prop where
  basePrepared : ∃ (program : CheckedProgram) (plan : SourceCompilationPlan.Plan)
    (ownership : checked.signatures = program.signatures) (fuel : Nat),
    SourceCoreCompatibleFunctions.prepareWithCatalog program plan checked ownership fuel = .ok base
  tablePrepared : ∃ (project : TypeSystem.Ty → Except SourceCoreLocalPolymorphism.Error Core.Ty)
    (limits : SourceCoreStageCodebook.Limits) (firstId : Nat),
    SourceCoreStageCodebook.prepareWithProjection base.sourceProgram base.plan project limits firstId = .ok inputs.callable.table
  shape : ∃ parameters result body, template.node.form = .lambda parameters result body ∧
    contract.parameters = parameters ∧ contract.stagedResult = SourceCompilationPlan.sourceTypeIsComptimeOnly result

/-- Factory success connects an actual read target to its canonical contract.
No private template constructor or native header check establishes provenance. -/
theorem header_of_prepared {program : CheckedProgram} {plan : SourceCompilationPlan.Plan}
    {checked : Checked} {ownership : checked.signatures = program.signatures} {fuel : Nat}
    {base : Base checked} {inputs : Inputs base}
    (accepted : SourceCoreCompatibleFunctions.prepareWithCatalog program plan checked ownership fuel = .ok base)
    {project : TypeSystem.Ty → Except SourceCoreLocalPolymorphism.Error Core.Ty}
    {limits : SourceCoreStageCodebook.Limits} {firstId : Nat}
    (table : SourceCoreStageCodebook.prepareWithProjection base.sourceProgram base.plan project limits firstId = .ok inputs.callable.table)
    {caller : MetadataState} {id target : Core.Word} (read : Read inputs caller id target) :
    ∃ contract, read.descriptor.contract = some contract ∧ CanonicalHeader inputs read.template contract := by
  obtain ⟨candidates, contexts⟩ := base_contexts accepted
  obtain ⟨original, selected, found, nodeEq⟩ := template_source contexts inputs.templatesPrepared
    (List.mem_of_find?_eq_some read.targetSelected)
  have authenticated := CallEntryCertificates.prepareWithProjection_authenticates table
    read.descriptor (List.mem_of_find?_eq_some read.descriptorSelected)
  unfold CallEntryCertificates.Authenticated at authenticated
  rw [read.templateOrigin] at authenticated
  obtain ⟨contract, attached, shape⟩ := contract_header authenticated selected found
  rw [← nodeEq] at shape
  exact ⟨contract, attached, ⟨⟨program, plan, ownership, fuel, accepted⟩,
    ⟨project, limits, firstId, table⟩, shape⟩⟩


namespace Recipe
variable {checked : Checked} {base : Base checked} {inputs : Inputs base}
  {callerFrame lexicalFrame : Frame} {caller lexical : MetadataState} {id target : Core.Word}
  (recipe : Recipe inputs callerFrame lexicalFrame caller lexical id target)
  {contract : SourceCoreStageContracts.Contract} (canonical : CanonicalHeader inputs recipe.read.template contract)

include canonical in
theorem contract_parameters : contract.parameters =
    recipe.applied.parameters.map (TypedBinder.applySubstitution recipe.read.substitution) := by
  obtain ⟨parameters, result, body, form, same, _⟩ := canonical.shape
  exact same.trans (ExpressionForm.lambda.inj (recipe.header.trans form)).1.symm

include canonical in
theorem contract_result : contract.stagedResult =
    SourceCompilationPlan.sourceTypeIsComptimeOnly (recipe.read.substitution.apply recipe.applied.resultType) := by
  obtain ⟨parameters, result, body, form, _, same⟩ := canonical.shape
  rw [(ExpressionForm.lambda.inj (recipe.header.trans form)).2.1]
  exact same


/-- The real recipe selects the pointwise rewritten original node, including
all of its requirement rows; the lambda header itself is not rewritten. -/
theorem source_node :
    (recipe.read.after lexical).metadata.source.lookupExpression? recipe.read.entry.view.principal.initializer =
      some (SourceTypedRuntime.rewriteExpressionLocalRequirements recipe.read.witnesses
        (recipe.applied.node.applySubstitution recipe.read.substitution)) :=
  SourceTypedRuntime.TypedSource.lookupExpression?_rewriteLocalRequirements _ _ _ _
    (SourceTypedRuntime.TypedSource.lookupExpression?_applySubstitution _ _ _ _ recipe.applied.found)

theorem source_node_form :
    (SourceTypedRuntime.rewriteExpressionLocalRequirements recipe.read.witnesses
      (recipe.applied.node.applySubstitution recipe.read.substitution)).form =
      .lambda (recipe.applied.parameters.map (TypedBinder.applySubstitution recipe.read.substitution))
        (recipe.read.substitution.apply recipe.applied.resultType) recipe.applied.body := by
  simp only [SourceTypedRuntime.rewriteExpressionLocalRequirements,
    ExpressionNode.applySubstitution, recipe.applied.shape, ExpressionForm.applySubstitution]

end Recipe

end Solcore.SourceSemantics.CoreLowering.CallableAppliedViewProvenance
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableAppliedDynamicSourceMaterialization
/-!
Exact finite correspondence between independent source substitution and the
compiler's occurrence-sensitive requirement rewriting. Each applied edge
retains both authentic metadata parents and the actual read/application
factories. Earlier rewrites stay in the lexical metadata source; the independent
source receives only the same sequence of substitutions.

This relation can be produced from authenticated metadata ancestry. Identifying
its independent source with a live generalized cell still requires an allocation
and heap invariant. The final theorem consumes genuine GeneralizedClosureCaptures
at that independent source. It derives the actual closed header without assuming
full lexical source equality, rewrite invariance, method identity, or execution.
The materialization below uses the authenticated read substitution. A live
Dynamic use additionally needs extensional agreement with its actual
substitution: matching a permuted variable domain alone does not establish
that agreement. Literal substitution-list equality is not asserted.
-/
set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.CallableAppliedDynamicSourceMaterialization
open Frontend SourceInference TypeSystem
open SourceCoreCallableAncestryReadRecipes
open CallableAncestryMetadata (eraseRequirements eraseNodeRequirements rewrite_erased)

abbrev Frame := SourceCoreCallablePairedFrames.Frame

/-- An exact source recipe at one authentic paired frame. The source index is
substituted independently; compiler metadata retains every actual rewrite. -/
inductive Pair {checked : Checked} {base : Base checked} (inputs : Inputs base) :
    Frame → SourceCoreCallableAncestryReadRecipes.State → TypedSource → Prop where
  | named {id : Core.Word} {state : SourceCoreCallableAncestryReadRecipes.State}
      (selected : SourceCoreCallableAncestryPairedPreparation.named? inputs id = some state) :
      Pair inputs (.named id) state state.metadata.source
  | lambda {frame : Frame} {state : SourceCoreCallableAncestryReadRecipes.State} {source : TypedSource} {id : Core.Word}
      (prior : Pair inputs frame state source)
      (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed inputs state id = true) :
      Pair inputs (.lambda id frame) state source
  | applied {callerFrame lexicalFrame : Frame} {caller lexical : SourceCoreCallableAncestryReadRecipes.State}
      {source : TypedSource} {id target : Core.Word}
      (prior : Pair inputs lexicalFrame lexical source)
      (recipe : CallableAppliedViewProvenance.Recipe inputs callerFrame lexicalFrame
        caller lexical id target) :
      Pair inputs (.appliedView id target callerFrame lexicalFrame)
        (recipe.read.after lexical) (source.applySubstitution recipe.read.substitution)

private def HasSource {checked : Checked} {base : Base checked} (inputs : Inputs base)
    (frame : Frame) : Option SourceCoreCallableAncestryReadRecipes.State → Prop
  | none => True
  | some state => ∃ source, Pair inputs frame state source

private theorem authenticated_has_source
    {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {frame : Frame} {state : Option SourceCoreCallableAncestryReadRecipes.State}
    (authenticated : CallableAncestryPairedLookup.Authenticates inputs frame state) :
    HasSource inputs frame state := by
  induction authenticated with
  | empty => trivial
  | named selected => exact ⟨_, .named selected⟩
  | lambda ancestry allowed ih =>
      obtain ⟨source, prior⟩ := ih
      exact ⟨source, .lambda prior allowed⟩
  | appliedView callerAncestry lexicalAncestry selected _callerIH lexicalIH =>
      obtain ⟨source, prior⟩ := lexicalIH
      obtain ⟨recipe, same⟩ :=
        CallableAppliedViewProvenance.Recipe.of_view callerAncestry lexicalAncestry selected
      cases same
      exact ⟨source.applySubstitution recipe.read.substitution, .applied prior recipe⟩

/-- The actual finite metadata derivation supplies this recipe. Its source is
an exact independently substituted candidate, not an asserted live heap value. -/
theorem of_authenticated
    {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {frame : Frame} {state : SourceCoreCallableAncestryReadRecipes.State}
    (authenticated : CallableAncestryPairedLookup.Authenticates inputs frame (some state)) :
    ∃ source, Pair inputs frame state source :=
  authenticated_has_source authenticated

/-- Every previous substitution and rewrite is retained by induction. Only
expression requirement lists are erased; all other source fields stay exact. -/
theorem erase_source
    {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {frame : Frame} {state : SourceCoreCallableAncestryReadRecipes.State} {source : TypedSource}
    (paired : Pair inputs frame state source) :
    eraseRequirements state.metadata.source = eraseRequirements source := by
  induction paired with
  | named _selected => rfl
  | lambda _prior _allowed ih => exact ih
  | @applied callerFrame lexicalFrame caller lexical source id target _prior recipe ih =>
      change eraseRequirements (SourceTypedRuntime.rewriteLocalRequirements
        recipe.read.witnesses (lexical.metadata.source.applySubstitution recipe.read.substitution)) = _
      rw [rewrite_erased, CallableAncestryProfiles.erase_substitute,
        CallableAncestryProfiles.erase_substitute, ih]

/-- These are the two different exact source equations at a genuine step.
The lexical metadata on the right may already contain earlier rewrites. -/
theorem step_sources
    {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {callerFrame lexicalFrame : Frame} {caller lexical : SourceCoreCallableAncestryReadRecipes.State} {id target : Core.Word}
    (recipe : CallableAppliedViewProvenance.Recipe inputs callerFrame lexicalFrame
      caller lexical id target)
    (function : Dynamic.GeneralizedClosure) (evidence : Dynamic.EvidenceEnvironment) :
    (function.instantiate recipe.read.substitution evidence).source =
      function.source.applySubstitution recipe.read.substitution ∧
    (recipe.read.after lexical).metadata.source =
      SourceTypedRuntime.rewriteLocalRequirements recipe.read.witnesses
        (lexical.metadata.source.applySubstitution recipe.read.substitution) :=
  ⟨rfl, rfl⟩

private theorem lookup_erased {source : TypedSource} {id : ExpressionId}
    {node : ExpressionNode} (found : source.lookupExpression? id = some node) :
    (eraseRequirements source).lookupExpression? id =
      some {node with requirements := []} := by
  unfold TypedSource.lookupExpression? TypedSource.lookupNode? at found ⊢
  simp only [eraseRequirements, List.find?_map]
  have samePredicate :
      ((fun candidate => decide (candidate.occurrenceId = id.occurrence)) ∘
        eraseNodeRequirements) =
      (fun candidate => decide (candidate.occurrenceId = id.occurrence)) := by
    funext candidate
    cases candidate <;> rfl
  rw [samePredicate]
  cases selected : List.find?
      (fun candidate => decide (candidate.occurrenceId = id.occurrence)) source.nodes with
  | none => simp [selected] at found
  | some candidate =>
      cases candidate with
      | expression selectedNode =>
          simp [selected, eraseNodeRequirements] at found ⊢
          cases found
          simp
      | statement selectedNode => simp [selected] at found

/-- A real generalized capture at the independently tracked source attaches
one actual materialization. Uniqueness makes its declarative lambda occurrence
agree with the compiler's executable lookup. No full-source equality is needed.

Producing `paired` for the actual source retained by a live generalized cell is
one remaining heap/allocation attachment obligation. A real Dynamic use also
needs agreement of its substitution action with this read substitution; this
theorem does not derive it from a domain permutation. -/
theorem materialize
    {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {callerFrame lexicalFrame : Frame} {caller lexical : SourceCoreCallableAncestryReadRecipes.State} {source : TypedSource}
    {id target : Core.Word}
    (paired : Pair inputs lexicalFrame lexical source)
    (recipe : CallableAppliedViewProvenance.Recipe inputs callerFrame lexicalFrame
      caller lexical id target)
    {context : Context} {captured : Dynamic.Environment} {binder : TypedBinder}
    {function : Dynamic.GeneralizedClosure}
    (captures : Dynamic.GeneralizedClosureCaptures context source captured binder
      recipe.read.entry.view.principal.initializer function)
    (unique : NodeOccurrencesUnique source) (evidence : Dynamic.EvidenceEnvironment) :
    Pair inputs (.appliedView id target callerFrame lexicalFrame)
      (recipe.read.after lexical) (function.instantiate recipe.read.substitution evidence).source ∧
    eraseRequirements (recipe.read.after lexical).metadata.source =
      eraseRequirements (function.instantiate recipe.read.substitution evidence).source ∧
    ExpressionForm.lambda (function.instantiate recipe.read.substitution evidence).parameters
      (function.instantiate recipe.read.substitution evidence).resultType
      (function.instantiate recipe.read.substitution evidence).body = recipe.read.template.node.form ∧
    (function.instantiate recipe.read.substitution evidence).captured = captured ∧
    (function.instantiate recipe.read.substitution evidence).evidence = evidence := by
  have sourceEq := captures.source_eq
  have initializerEq := captures.initializer_eq
  have transported : Pair inputs (.appliedView id target callerFrame lexicalFrame)
      (recipe.read.after lexical) (function.instantiate recipe.read.substitution evidence).source := by
    change Pair inputs _ _ (function.source.applySubstitution recipe.read.substitution)
    rw [sourceEq]
    exact .applied paired recipe
  obtain ⟨node, contains, form, _rawType, _type, _requirements, _coercions⟩ := captures.occurrence
  have found : source.lookupExpression? recipe.read.entry.view.principal.initializer = some node := by
    apply lookupExpression?_complete unique
    simpa only [sourceEq, initializerEq] using contains
  have nativeFound := lookup_erased recipe.applied.found
  have dynamicFound := lookup_erased found
  rw [erase_source paired] at nativeFound
  have nodeEq : ({recipe.applied.node with requirements := []} : ExpressionNode) =
      {node with requirements := []} :=
    Option.some.inj (nativeFound.symm.trans dynamicFound)
  have formsErased := congrArg ExpressionNode.form nodeEq
  have forms : recipe.applied.node.form = node.form := formsErased
  have sameHeader : ExpressionForm.lambda recipe.applied.parameters recipe.applied.resultType
      recipe.applied.body = ExpressionForm.lambda function.parameters function.resultType function.body :=
    recipe.applied.shape.symm.trans (forms.trans form)
  rcases ExpressionForm.lambda.inj sameHeader with ⟨parameters, resultType, body⟩
  have header := recipe.applied.nativeHeader
  rw [parameters, resultType, body] at header
  exact ⟨transported, erase_source transported, header, captures.captured_eq, rfl⟩

end Solcore.SourceSemantics.CoreLowering.CallableAppliedDynamicSourceMaterialization
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableLedger
/-! A caller frame built from retained source metadata, with a scoped
representation refinement. Its source ledger records closure parameters and
source result staging, exact named metadata selection, and builtin bypass.
World-independent origin receipts supplement an existing semantic payload
model; they never establish closure code correctness merely from Core typing.

The original source alignment of contextual lambdas is explicit. The metadata
factory's boolean caller check alone is not silently used as a propositional
TypedSource equality. Whole recursive stage-frame propagation remains separate. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableLedger
open Frontend Frontend.SourceInference SourceCoreStageContracts GeneralHeap
open CallContractCertificates

inductive Binds (plan : Plan) : Dynamic.Value → SourceContract → Prop where
  | closure {function : Dynamic.Closure} {contract : SourceContract}
      (parameters : contract.parameters = function.parameters)
      (result : contract.stagedResult = true ↔ Staging.ComptimeOnlyType function.resultType) :
      Binds plan (.closure function) contract
  | named {function : Dynamic.GlobalFunction} {key : Key} {contract : Contract}
      (selected : SourceCompilationPlan.exactInstantiationKey plan function.instantiation = .ok key)
      (prepared : Contract.named plan key = .ok contract) :
      Binds plan (.global function) (semanticContract contract)

theorem Binds.userCallable {plan : Plan} {value : Dynamic.Value} {contract : SourceContract}
    (bound : Binds plan value contract) : Staging.CallBoundary.UserCallable value := by
  cases bound with
  | closure => exact .closure _
  | named => exact .global _

theorem Binds.unique {plan : Plan} {value : Dynamic.Value} {left right : SourceContract}
    (first : Binds plan value left) (second : Binds plan value right) : left = right := by
  cases first with
  | closure parameters result =>
    cases second with
    | closure otherParameters otherResult =>
      cases left with
      | mk leftParameters leftResult =>
        cases right with
        | mk rightParameters rightResult =>
          dsimp only at parameters result otherParameters otherResult
          cases parameters.trans otherParameters.symm
          cases leftResult <;> cases rightResult <;> simp_all
  | named selected prepared =>
    cases second with
    | named otherSelected otherPrepared =>
      cases Except.ok.inj (selected.symm.trans otherSelected)
      cases Except.ok.inj (prepared.symm.trans otherPrepared)
      rfl

/-- Caller stages come from the retained analyzed sidecar. Contracts are read
from original source metadata, independently of the erased Core carrier. -/
def frame (sidecar : Sidecar) : Staging.CallBoundary.Frame where
  stages := CallStageGuard.frame sidecar.caller
  Binds := Binds sidecar.plan
  userCallable := Binds.userCallable
  unique := Binds.unique

/-- Alignment of one actual source closure with its original monomorphic or
contextual lambda factory receipt. `active` is the full cumulative context. -/
inductive LambdaOrigin (plan : Plan) (owner : Key) (id : ExpressionId) :
    TypeSystem.Substitution → Dynamic.Closure → Contract → Prop where
  | original {sidecar : Sidecar} {function : Dynamic.Closure} {contract : Contract}
      (prepared : Contract.lambda sidecar id = .ok contract)
      (receipt : LambdaReceipt sidecar id contract)
      (samePlan : sidecar.plan = plan) (sameOwner : sidecar.caller.key = owner)
      (source : function.source = sidecar.source)
      (parameters : function.parameters = receipt.parameters)
      (result : function.resultType = receipt.result)
      (body : function.body = receipt.body) : LambdaOrigin plan owner id [] function contract
  | contextual {sidecar : Sidecar} {contextual : SourceCoreLocalEvidence.Prepared}
      {function : Dynamic.Closure} {contract : Contract}
      (prepared : Contract.contextualLambda sidecar contextual id = .ok contract)
      (receipt : ContextualLambdaReceipt sidecar contextual id contract)
      (samePlan : sidecar.plan = plan) (sameOwner : sidecar.caller.key = owner)
      (source : function.source = sidecar.source.applySubstitution contextual.substitution)
      (parameters : function.parameters = receipt.parameters.map (TypedBinder.applySubstitution contextual.substitution))
      (result : function.resultType = contextual.substitution.apply receipt.result)
      (body : function.body = receipt.body) :
      LambdaOrigin plan owner id contextual.substitution function contract

  | applied {checked : SourceCoreCompatibleCatalog.Checked}
      {base : SourceCoreCompatibleFunctions.Prepared checked}
      {inputs : SourceCoreCallableAncestryPreparation.Inputs base}
      {callerFrame lexicalFrame : SourceCoreCallablePairedFrames.Frame}
      {caller lexical : SourceCoreCallableAncestryReadRecipes.State} {view target : Core.Word}
      {function : Dynamic.Closure} {contract : Contract}
      (recipe : CallableAppliedViewProvenance.Recipe inputs callerFrame lexicalFrame caller lexical view target)
      (canonical : CallableAppliedViewProvenance.CanonicalHeader inputs recipe.read.template contract)
      (retained : recipe.read.descriptor.contract = some contract)
      (samePlan : base.plan = plan) (sameOwner : recipe.read.template.owner = owner)
      (sameId : recipe.read.template.id = id)
      (source : function.source = (recipe.read.after lexical).metadata.source)
      (parameters : function.parameters = recipe.applied.parameters.map
        (TypedBinder.applySubstitution recipe.read.substitution))
      (result : function.resultType = recipe.read.substitution.apply recipe.applied.resultType)
      (body : function.body = recipe.applied.body) :
      LambdaOrigin plan owner id recipe.read.template.active function contract

  /-- The Source graph follows the captured lexical history independently of
  compiler requirement rewrites. Both the graph and header are supplied by the
  same authenticated application, without identifying the complete sources. -/
  | independentApplied {checked : SourceCoreCompatibleCatalog.Checked}
      {base : SourceCoreCompatibleFunctions.Prepared checked}
      {inputs : SourceCoreCallableAncestryPreparation.Inputs base}
      {callerFrame lexicalFrame : SourceCoreCallablePairedFrames.Frame}
      {caller lexical : SourceCoreCallableAncestryReadRecipes.State} {view target : Core.Word}
      {function : Dynamic.Closure} {contract : Contract}
      (recipe : CallableAppliedViewProvenance.Recipe inputs callerFrame lexicalFrame caller lexical view target)
      (canonical : CallableAppliedViewProvenance.CanonicalHeader inputs recipe.read.template contract)
      (retained : recipe.read.descriptor.contract = some contract)
      (samePlan : base.plan = plan) (sameOwner : recipe.read.template.owner = owner)
      (sameId : recipe.read.template.id = id)
      (paired : CallableAppliedDynamicSourceMaterialization.Pair inputs
        (.appliedView view target callerFrame lexicalFrame) (recipe.read.after lexical) function.source)
      (header : Frontend.SourceInference.ExpressionForm.lambda function.parameters function.resultType function.body =
        recipe.read.template.node.form) :
      LambdaOrigin plan owner id recipe.read.template.active function contract

theorem LambdaOrigin.binds {plan : Plan} {owner : Key} {id : ExpressionId} {active : TypeSystem.Substitution}
    {function : Dynamic.Closure} {contract : Contract}
    (origin : LambdaOrigin plan owner id active function contract) : Binds plan (.closure function) (semanticContract contract) := by
  cases origin with
  | original _ receipt _ _ _ parameters result _ =>
    refine .closure (receipt.parameters_eq.trans parameters.symm) ?_
    change contract.stagedResult = true ↔ Staging.ComptimeOnlyType function.resultType
    rw [receipt.stagedResult, result]
    exact SourceStageAnalysis.typeIsComptimeOnly_eq_true_iff _
  | contextual _ receipt _ _ _ parameters result _ =>
    refine .closure (receipt.parameters_eq.trans parameters.symm) ?_
    change contract.stagedResult = true ↔ Staging.ComptimeOnlyType function.resultType
    rw [receipt.stagedResult, result]
    exact SourceStageAnalysis.typeIsComptimeOnly_eq_true_iff _

  | applied recipe canonical _ _ _ _ _ parameters result _ =>
    refine .closure ((recipe.contract_parameters canonical).trans parameters.symm) ?_
    change contract.stagedResult = true ↔ Staging.ComptimeOnlyType function.resultType
    rw [recipe.contract_result canonical, result]
    exact SourceStageAnalysis.typeIsComptimeOnly_eq_true_iff _

  | independentApplied recipe canonical _ _ _ _ _ header =>
    have components := Frontend.SourceInference.ExpressionForm.lambda.inj
      (header.trans recipe.header.symm)
    refine .closure ((recipe.contract_parameters canonical).trans components.1.symm) ?_
    change contract.stagedResult = true ↔ Staging.ComptimeOnlyType function.resultType
    rw [recipe.contract_result canonical, components.2.1]
    exact SourceStageAnalysis.typeIsComptimeOnly_eq_true_iff _

/-- Static metadata provenance for the visible descriptor of a value. The
underlying payload model remains responsible for its code/capture meaning. -/
inductive OriginRep (plan : Plan) (table : SourceCoreStageCodebook.Table) : Dynamic.Value → Core.Value → Prop where
  | closure {function : Dynamic.Closure} {raw : Core.Value} {entry : SourceCoreStageCodebook.Entry}
      {owner : Key} {id : ExpressionId} {active : TypeSystem.Substitution} {contract : Contract}
      (member : entry ∈ table.entries) (entryOrigin : entry.origin = .lambda owner id active)
      (retained : entry.contract = some contract) (origin : LambdaOrigin plan owner id active function contract) :
      OriginRep plan table (.closure function) (.pair raw (.word entry.id))
  | named {function : Dynamic.GlobalFunction} {raw : Core.Value} {entry : SourceCoreStageCodebook.Entry}
      {key : Key} {contract : Contract}
      (member : entry ∈ table.entries) (entryOrigin : entry.origin = .named key)
      (retained : entry.contract = some contract)
      (selected : SourceCompilationPlan.exactInstantiationKey plan function.instantiation = .ok key)
      (prepared : Contract.named plan key = .ok contract) :
      OriginRep plan table (.global function) (.pair raw (.word entry.id))
  | builtin {function : Dynamic.BuiltinFunction} {raw : Core.Value} {entry : SourceCoreStageCodebook.Entry}
      (member : entry ∈ table.entries) (entryOrigin : entry.origin = .builtin function.id)
      (retained : entry.contract = none) :
      OriginRep plan table (.builtin function) (.pair raw (.word entry.id))

/-- Add stage provenance to an existing value relation. This is intentionally
not a model admitting arbitrary values solely from `RuntimeValueHasType`. -/
def model {catalog : SourceCoreDataCatalog.Catalog} (underlying : GenericHeap.PayloadModel catalog)
    (plan : Plan) (table : SourceCoreStageCodebook.Table) : GenericHeap.PayloadModel catalog where
  Represents mapping world type source core payload :=
    underlying.Represents mapping world type source core payload ∧ OriginRep plan table source core
  projection related := underlying.projection related.1
  runtime_hasType related := underlying.runtime_hasType related.1
  extend related maps worlds := ⟨underlying.extend related.1 maps worlds, related.2⟩

/-- A static row receipt records actual `prepareGuard` success. Factory
extraction for complete tables is kept separate from source value semantics. -/
structure Row (sidecar : Sidecar) (site : SourceCoreCallableContracts.Callsite)
    (call : ExpressionId) (arguments : List ExpressionId) (entry : SourceCoreStageCodebook.Entry) where
  decision : SourceCoreStageCodebook.Decision
  found : site.rowAt? entry.id = some decision
  entry_eq : decision.entry = entry
  prepared : ∀ contract, entry.contract = some contract → ∃ guard,
    prepareGuard sidecar call contract = .ok guard ∧ decision.guard = some guard ∧ guard.arguments = arguments
  builtin : entry.contract = none → decision.guard = none

/-- Each actual retained entry has its original guarded row at this caller.
This predicate contains metadata-factory equations, not child evaluations. -/
def Rows (sidecar : Sidecar) (site : SourceCoreCallableContracts.Callsite)
    (call : ExpressionId) (arguments : List ExpressionId) : Prop :=
  ∀ entry, entry ∈ site.table.entries → Nonempty (Row sidecar site call arguments entry)

theorem dispatch {sidecar : Sidecar} {site : SourceCoreCallableContracts.Callsite}
    {call : ExpressionId} {arguments : List ExpressionId} {source : Dynamic.Value} {carrier : Core.Value}
    (rows : Rows sidecar site call arguments)
    (origin : OriginRep sidecar.plan site.table source carrier)
    {contract : SourceContract} (bound : (frame sidecar).Binds source contract) :
    Nonempty (CallStageBoundary.Dispatch (frame sidecar) site call arguments source carrier) := by
  cases origin with
  | @closure function raw entry owner id active original member _ retained provenance =>
    obtain ⟨row⟩ := rows entry member
    obtain ⟨guard, prepared, attached, arguments_eq⟩ := row.prepared original retained
    obtain ⟨receipt⟩ := guard_of_accepted prepared
    refine ⟨⟨raw, entry.id, row.decision, guard, rfl, row.found, attached, receipt.call, arguments_eq, ?_, ?_⟩⟩
    · rw [receipt.sidecar_eq]; rfl
    · rw [receipt.contract_eq]
      exact provenance.binds
  | @named function raw entry key original member _ retained selected prepared =>
    obtain ⟨row⟩ := rows entry member
    obtain ⟨guard, checked, attached, arguments_eq⟩ := row.prepared original retained
    obtain ⟨receipt⟩ := guard_of_accepted checked
    refine ⟨⟨raw, entry.id, row.decision, guard, rfl, row.found, attached, receipt.call, arguments_eq, ?_, ?_⟩⟩
    · rw [receipt.sidecar_eq]; rfl
    · rw [receipt.contract_eq]
      exact Binds.named selected prepared
  | builtin => cases bound

theorem covers {catalog : SourceCoreDataCatalog.Catalog} (underlying : GenericHeap.PayloadModel catalog)
    {sidecar : Sidecar} {site : SourceCoreCallableContracts.Callsite} {call : ExpressionId}
    {arguments : List ExpressionId} (rows : Rows sidecar site call arguments)
    (sourceType : TypeSystem.Ty) (type : Core.Ty) :
    CallStageBoundary.Covers (model underlying sidecar.plan site.table) (frame sidecar) site call arguments sourceType type := by
  intro mapping world source carrier contract represented bound
  exact dispatch rows represented.2 bound

end Solcore.SourceSemantics.CoreLowering.CallableLedger
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableClosedSchemeSubstitutionAgreement
/-!
A successful concrete scheme matcher determines the action of every exact
semantic instantiation at that same scheme and occurrence type. The proof
retains arbitrary ordering of the semantic substitution. No ordered list
equality, source equality, Dynamic execution law, or read/capture attachment is
assumed. Attaching the two matching inputs to an actual read and live Dynamic
cell remains a separate producer obligation.
-/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableClosedSchemeSubstitutionAgreement
open Frontend SourceInference TypeSystem
open CallableAncestryProfiles.SourceComposition

/-- The matcher only introduces domain keys appearing in its expected type.
Existing keys are retained independently of that occurrence. -/
private theorem matchBody_domain_occurs (quantified : List TypeVarId)
    (expected actual : Ty) {initial final : Substitution}
    (matched : Scheme.matchBody? quantified expected actual initial = some final) :
    ∀ metavariable, metavariable ∈ final.domain →
      metavariable ∈ initial.domain ∨ metavariable ∈ expected.freeVariables := by
  induction expected generalizing actual initial final with
  | «variable» metavariable =>
      simp only [Scheme.matchBody?] at matched
      split at matched
      · split at matched
        · split at matched <;> try contradiction
          cases matched
          exact fun _ member => Or.inl member
        · cases matched
          intro candidate member
          simp only [Substitution.domain, List.map_cons, List.mem_cons] at member
          rcases member with same | member
          · exact Or.inr (by simpa [Ty.freeVariables] using same)
          · exact Or.inl member
      · split at matched <;> try contradiction
        cases matched
        exact fun _ member => Or.inl member
  | parameter | constructor =>
      cases actual <;> simp only [Scheme.matchBody?] at matched <;> try contradiction
      split at matched <;> try contradiction
      cases matched
      exact fun _ member => Or.inl member
  | error =>
      cases actual <;> simp only [Scheme.matchBody?] at matched <;> try contradiction
      cases matched
      exact fun _ member => Or.inl member
  | application left right ihLeft ihRight
  | function left right ihLeft ihRight
  | product left right ihLeft ihRight
  | mapping left right ihLeft ihRight =>
      cases actual <;> simp only [Scheme.matchBody?] at matched <;> try contradiction
      rename_i actualLeft actualRight
      obtain ⟨middle, leftMatched, rightMatched⟩ := Option.bind_eq_some_iff.mp matched
      intro metavariable member
      rcases ihRight actualRight rightMatched metavariable member with middleMember | rightMember
      · rcases ihLeft actualLeft leftMatched metavariable middleMember with initialMember | leftMember
        · exact Or.inl initialMember
        · exact Or.inr (by simp [leftMember])
      · exact Or.inr (by simp [rightMember])
  | proxy inner ih | comptime inner ih =>
      cases actual <;> simp only [Scheme.matchBody?] at matched <;> try contradiction
      rename_i actualInner
      intro metavariable member
      simpa only [Ty.freeVariables] using ih actualInner matched metavariable member

/-- Successful reordering can select every binder only if each has a genuine
assignment in the structural matcher's output. -/
private theorem reorder_domain_covers {matched : Substitution}
    {variables : List TypeVarId} {result : Substitution}
    (accepted : variables.mapM (fun metavariable => do
      pure (metavariable, ← matched.lookup? metavariable)) = some result) :
    ∀ metavariable, metavariable ∈ variables → metavariable ∈ matched.domain := by
  induction variables generalizing result with
  | nil => intro metavariable member; simp at member
  | cons head tail ih =>
      rw [List.mapM_cons] at accepted
      obtain ⟨first, found, accepted⟩ := Option.bind_eq_some_iff.mp accepted
      obtain ⟨rest, remainder, _accepted⟩ := Option.bind_eq_some_iff.mp accepted
      cases lookup : matched.lookup? head with
      | none => simp [lookup] at found
      | some replacement =>
          intro metavariable member
          rcases List.mem_cons.mp member with same | member
          · subst metavariable
            exact List.mem_map.mpr
              ⟨(head, replacement), Substitution.lookup?_eq_some_mem lookup, rfl⟩
          · exact ih remainder metavariable member

private theorem quantified_occurs_of_match
    {scheme : Scheme} {actual : Ty} {substitution : Substitution}
    (accepted : scheme.matchInstance? actual = some substitution) :
    ∀ metavariable, metavariable ∈ scheme.quantified →
      metavariable ∈ scheme.body.freeVariables := by
  unfold Scheme.matchInstance? at accepted
  cases certified : Scheme.matchInstanceCertificate? scheme actual with
  | none => simp [certified] at accepted
  | some certificate =>
      unfold Scheme.matchInstanceCertificate? at certified
      split at certified <;> try contradiction
      obtain ⟨matched, shape, certified⟩ := Option.bind_eq_some_iff.mp certified
      obtain ⟨reordered, ordering, _certified⟩ := Option.bind_eq_some_iff.mp certified
      intro metavariable quantified
      have inDomain := reorder_domain_covers ordering metavariable quantified
      have occurs := matchBody_domain_occurs scheme.quantified scheme.body actual
        shape metavariable inDomain
      simpa only [Substitution.domain, List.map_nil, List.mem_nil_iff, false_or] using occurs

/-- Complete accepted matching rejects phantom quantified variables. This
coverage comes from the actual matcher, rather than an extra static premise. -/
theorem quantified_occurs_of_closed_match
    {scheme : Scheme} {actual : Ty} {substitution : Substitution}
    (accepted : SourceSpecialization.matchClosedSchemeInstance? scheme actual =
      some substitution) :
    ∀ metavariable, metavariable ∈ scheme.quantified →
      metavariable ∈ scheme.body.freeVariables := by
  have concrete := (SourceSpecialization.matchClosedSchemeInstance?_sound accepted).1
  apply quantified_occurs_of_match
  simpa [SourceSpecialization.matchClosedSchemeInstance?, concrete] using accepted

/-- Equality of two substituted copies of one type identifies the variable
replacement actions at every variable which actually occurs in that type. -/
private theorem variable_actions_eq_of_apply_eq {left right : Substitution}
    (type : Ty) (same : left.apply type = right.apply type) :
    ∀ metavariable, metavariable ∈ type.freeVariables →
      left.apply (.variable metavariable) = right.apply (.variable metavariable) := by
  induction type with
  | «variable» candidate =>
      intro metavariable member
      have sameVariable : metavariable = candidate := by
        simpa [Ty.freeVariables] using member
      subst metavariable
      exact same
  | parameter | constructor | error =>
      intro metavariable member
      simp [Ty.freeVariables] at member
  | application leftType rightType ihLeft ihRight
  | function leftType rightType ihLeft ihRight
  | product leftType rightType ihLeft ihRight
  | mapping leftType rightType ihLeft ihRight =>
      injection same with leftSame rightSame
      intro metavariable member
      simp at member
      rcases member with member | member
      · exact ihLeft leftSame metavariable member
      · exact ihRight rightSame metavariable member
  | proxy inner ih | comptime inner ih =>
      injection same with innerSame
      intro metavariable member
      exact ih innerSame metavariable member

private theorem lookup_exists_of_domain {substitution : Substitution}
    {metavariable : TypeVarId} (member : metavariable ∈ substitution.domain) :
    ∃ replacement, substitution.lookup? metavariable = some replacement := by
  cases found : substitution.lookup? metavariable with
  | none =>
      exact False.elim
        (((Substitution.lookup?_eq_none_iff_not_mem_domain substitution metavariable).mp found) member)
  | some replacement => exact ⟨replacement, rfl⟩

/-- The exact semantic substitution and the actual complete matcher have the
same first-match lookup action. Their ordered lists are left independent. -/
theorem lookup_eq_of_closed_match
    {scheme : Scheme} {actual : Ty} {compiled semantic : Substitution}
    (matched : SourceSpecialization.matchClosedSchemeInstance? scheme actual =
      some compiled)
    (exact : ExactSubstitution semantic scheme.quantified)
    (result : semantic.apply scheme.body = actual) :
    ∀ metavariable, semantic.lookup? metavariable = compiled.lookup? metavariable := by
  obtain ⟨_concrete, unique, domain, applies⟩ :=
    SourceSpecialization.matchClosedSchemeInstance?_sound matched
  have compiledExact : ExactSubstitution compiled scheme.quantified := {
    variables_nodup := unique
    domain_permutation := by rw [domain]
  }
  have actions := variable_actions_eq_of_apply_eq scheme.body (result.trans applies.symm)
  intro metavariable
  by_cases quantified : metavariable ∈ scheme.quantified
  · obtain ⟨semanticReplacement, semanticLookup⟩ :=
      lookup_exists_of_domain ((exact.mem_domain_iff metavariable).mpr quantified)
    obtain ⟨compiledReplacement, compiledLookup⟩ :=
      lookup_exists_of_domain ((compiledExact.mem_domain_iff metavariable).mpr quantified)
    have replacements : semanticReplacement = compiledReplacement := by
      simpa only [Substitution.apply, semanticLookup, compiledLookup, Option.getD_some] using
        actions metavariable (quantified_occurs_of_closed_match matched metavariable quantified)
    rw [semanticLookup, compiledLookup, replacements]
  · have semanticAbsent : metavariable ∉ semantic.domain := by
      intro member
      exact quantified ((exact.mem_domain_iff metavariable).mp member)
    have compiledAbsent : metavariable ∉ compiled.domain := by
      simpa only [domain] using quantified
    rw [(Substitution.lookup?_eq_none_iff_not_mem_domain semantic metavariable).mpr semanticAbsent,
      (Substitution.lookup?_eq_none_iff_not_mem_domain compiled metavariable).mpr compiledAbsent]

/-- Every type action agrees; source/header/context actions can therefore
transport this lookup agreement through their existing structural operators. -/
theorem apply_eq_of_closed_match
    {scheme : Scheme} {actual : Ty} {compiled semantic : Substitution}
    (matched : SourceSpecialization.matchClosedSchemeInstance? scheme actual =
      some compiled)
    (exact : ExactSubstitution semantic scheme.quantified)
    (result : semantic.apply scheme.body = actual) (type : Ty) :
    semantic.apply type = compiled.apply type :=
  apply_lookup_congr (lookup_eq_of_closed_match matched exact result) type

/-- The actual Dynamic instantiation supplies exactness and the instance
equation internally. Only the same scheme and occurrence-type matcher input
is required at this theorem's retained binder/type indices. -/
theorem runtime_instantiation_lookup_eq
    {context : Context} {callerEvidence produced : Dynamic.EvidenceEnvironment}
    {binder : TypedBinder} {actual : Ty} {requirements : List RequirementId}
    {compiled semantic : Substitution}
    (matched : SourceSpecialization.matchClosedSchemeInstance? binder.scheme actual =
      some compiled)
    (instantiation : Dynamic.LocalSchemeRuntimeInstantiation context callerEvidence
      binder actual requirements semantic produced) :
    ∀ metavariable, semantic.lookup? metavariable = compiled.lookup? metavariable :=
  lookup_eq_of_closed_match matched instantiation.exact instantiation.result

end Solcore.SourceSemantics.CoreLowering.CallableClosedSchemeSubstitutionAgreement
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableFlexibleSubstitutionAgreement
/-! Equal flexible-metavariable lookups act equally on the complete retained
source carrier and its initializer context. Quantified schemes keep their
actual masks; substitution lists need not have the same order. Materializing
the same principal descriptor with the same evidence then yields the same
ordinary closure. Runtime attachment and accepted matching are separate facts. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableFlexibleSubstitutionAgreement
open Frontend SourceInference TypeSystem
open CallableAncestryProfiles.SourceComposition

private theorem masked_lookup {left right : Substitution}
    (same : ∀ metavariable, left.lookup? metavariable = right.lookup? metavariable)
    (variables : List TypeVarId) :
    ∀ metavariable, (left.without variables).lookup? metavariable =
      (right.without variables).lookup? metavariable := by
  intro metavariable
  simp only [lookup_without, same metavariable]

private theorem apply_function {left right : Substitution}
    (same : ∀ metavariable, left.lookup? metavariable = right.lookup? metavariable) :
    left.apply = right.apply :=
  funext (apply_lookup_congr same)

private theorem predicate_function {left right : Substitution}
    (same : ∀ metavariable, left.lookup? metavariable = right.lookup? metavariable) :
    TypedTraitResolution.applySubstitution left =
      TypedTraitResolution.applySubstitution right := by
  funext predicate
  simp only [TypedTraitResolution.applySubstitution, apply_function same]

private theorem requirement_function {left right : Substitution}
    (same : ∀ metavariable, left.lookup? metavariable = right.lookup? metavariable) :
    LocalSchemeRequirement.applySubstitution left =
      LocalSchemeRequirement.applySubstitution right := by
  funext requirement
  simp only [LocalSchemeRequirement.applySubstitution, predicate_function same]

private theorem scheme_congr {left right : Substitution}
    (same : ∀ metavariable, left.lookup? metavariable = right.lookup? metavariable)
    (scheme : Scheme) : scheme.apply left = scheme.apply right := by
  simp only [Scheme.apply, apply_lookup_congr (masked_lookup same scheme.quantified)]

private theorem binder_function {left right : Substitution}
    (same : ∀ metavariable, left.lookup? metavariable = right.lookup? metavariable) :
    TypedBinder.applySubstitution left = TypedBinder.applySubstitution right := by
  funext binder
  have masked := masked_lookup same binder.scheme.quantified
  simp only [TypedBinder.applySubstitution, scheme_congr masked,
    requirement_function masked]

private theorem declaration_function {left right : Substitution}
    (same : ∀ metavariable, left.lookup? metavariable = right.lookup? metavariable) :
    DeclarationInstantiation.applySubstitution left =
      DeclarationInstantiation.applySubstitution right := by
  funext value
  unfold DeclarationInstantiation.applySubstitution
  change { value with
    parameterSubstitution := value.parameterSubstitution.map
      (fun (entry : TypeParameterId × Ty) => (entry.1, left.apply entry.2))
    type := left.apply value.type
    predicates := value.predicates.map (TypedTraitResolution.applySubstitution left) } =
    { value with
      parameterSubstitution := value.parameterSubstitution.map
        (fun (entry : TypeParameterId × Ty) => (entry.1, right.apply entry.2))
      type := right.apply value.type
      predicates := value.predicates.map (TypedTraitResolution.applySubstitution right) }
  simp only [apply_function same, predicate_function same]

private theorem constructor_function {left right : Substitution}
    (same : ∀ metavariable, left.lookup? metavariable = right.lookup? metavariable) :
    DataConstructorInstantiation.applySubstitution left =
      DataConstructorInstantiation.applySubstitution right := by
  funext value
  unfold DataConstructorInstantiation.applySubstitution
  change { value with
    parameterSubstitution := value.parameterSubstitution.map
      (fun (entry : TypeParameterId × Ty) => (entry.1, left.apply entry.2))
    payloadTypes := value.payloadTypes.map left.apply
    resultType := left.apply value.resultType } =
    { value with
      parameterSubstitution := value.parameterSubstitution.map
        (fun (entry : TypeParameterId × Ty) => (entry.1, right.apply entry.2))
      payloadTypes := value.payloadTypes.map right.apply
      resultType := right.apply value.resultType }
  simp only [apply_function same]

private theorem integer_function {left right : Substitution}
    (same : ∀ metavariable, left.lookup? metavariable = right.lookup? metavariable) :
    IntegerLiteralResolution.applySubstitution left =
      IntegerLiteralResolution.applySubstitution right := by
  funext resolution
  simp only [IntegerLiteralResolution.applySubstitution, apply_function same]

private theorem coercion_function {left right : Substitution}
    (same : ∀ metavariable, left.lookup? metavariable = right.lookup? metavariable) :
    CoercionStep.applySubstitution left = CoercionStep.applySubstitution right := by
  funext step
  simp only [CoercionStep.applySubstitution, apply_function same]

private theorem indirect_function {left right : Substitution}
    (same : ∀ metavariable, left.lookup? metavariable = right.lookup? metavariable) :
    IndirectCallResolution.applySubstitution left =
      IndirectCallResolution.applySubstitution right := by
  funext resolution
  simp only [IndirectCallResolution.applySubstitution, apply_function same,
    coercion_function same]

private theorem reference_function {left right : Substitution}
    (same : ∀ metavariable, left.lookup? metavariable = right.lookup? metavariable) :
    ReferenceResolution.applySubstitution left = ReferenceResolution.applySubstitution right := by
  funext resolution
  cases resolution <;> simp only [ReferenceResolution.applySubstitution, declaration_function same]

private theorem call_function {left right : Substitution}
    (same : ∀ metavariable, left.lookup? metavariable = right.lookup? metavariable) :
    CallResolution.applySubstitution left = CallResolution.applySubstitution right := by
  funext resolution
  cases resolution <;> simp only [CallResolution.applySubstitution, indirect_function same,
    declaration_function same]

private theorem expression_function {left right : Substitution}
    (same : ∀ metavariable, left.lookup? metavariable = right.lookup? metavariable) :
    ExpressionForm.applySubstitution left = ExpressionForm.applySubstitution right := by
  funext form
  cases form <;> simp only [ExpressionForm.applySubstitution, integer_function same,
    reference_function same, call_function same, constructor_function same,
    binder_function same, apply_function same]

private theorem instruction_function {left right : Substitution}
    (same : ∀ metavariable, left.lookup? metavariable = right.lookup? metavariable) :
    MatchPatternInstruction.applySubstitution left =
      MatchPatternInstruction.applySubstitution right := by
  funext instruction
  cases instruction <;> simp only [MatchPatternInstruction.applySubstitution,
    integer_function same, binder_function same, constructor_function same]

private theorem pattern_function {left right : Substitution}
    (same : ∀ metavariable, left.lookup? metavariable = right.lookup? metavariable) :
    MatchPatternResolution.applySubstitution left =
      MatchPatternResolution.applySubstitution right := by
  funext pattern
  cases pattern <;> simp only [MatchPatternResolution.applySubstitution,
    integer_function same, binder_function same, constructor_function same,
    instruction_function same]

private theorem match_function {left right : Substitution}
    (same : ∀ metavariable, left.lookup? metavariable = right.lookup? metavariable) :
    MatchResolution.applySubstitution left = MatchResolution.applySubstitution right := by
  have arm_function : TypedMatchCase.applySubstitution left =
      TypedMatchCase.applySubstitution right := by
    funext arm
    simp only [TypedMatchCase.applySubstitution, TypedMatchPattern.applySubstitution,
      pattern_function same, apply_function same]
  funext resolution
  simp only [MatchResolution.applySubstitution, arm_function]

private theorem assignment_function {left right : Substitution}
    (same : ∀ metavariable, left.lookup? metavariable = right.lookup? metavariable) :
    AssignmentResolution.applySubstitution left = AssignmentResolution.applySubstitution right := by
  funext assignment
  simp only [AssignmentResolution.applySubstitution, PlaceResolution.applySubstitution,
    apply_function same]

private theorem for_item_function {left right : Substitution}
    (same : ∀ metavariable, left.lookup? metavariable = right.lookup? metavariable) :
    ForItemForm.applySubstitution left = ForItemForm.applySubstitution right := by
  funext item
  cases item <;> simp only [ForItemForm.applySubstitution, binder_function same,
    assignment_function same]

private theorem statement_function {left right : Substitution}
    (same : ∀ metavariable, left.lookup? metavariable = right.lookup? metavariable) :
    StatementForm.applySubstitution left = StatementForm.applySubstitution right := by
  funext form
  cases form <;> simp only [StatementForm.applySubstitution, binder_function same,
    assignment_function same, match_function same, for_item_function same]

private theorem node_function {left right : Substitution}
    (same : ∀ metavariable, left.lookup? metavariable = right.lookup? metavariable) :
    Node.applySubstitution left = Node.applySubstitution right := by
  funext node
  cases node <;> simp only [Node.applySubstitution, ExpressionNode.applySubstitution,
    StatementNode.applySubstitution, coercion_function same,
    expression_function same, statement_function same, apply_function same]

/-- The full source table, binder schemes, nested declaration substitutions,
coercions and requirement metadata retain the same raw structural action. -/
theorem typedSource_congr {left right : Substitution}
    (same : ∀ metavariable, left.lookup? metavariable = right.lookup? metavariable)
    (source : TypedSource) :
    source.applySubstitution left = source.applySubstitution right := by
  simp only [TypedSource.applySubstitution, binder_function same, node_function same]

mutual
  private theorem evidence_congr {left right : Substitution}
      (same : ∀ metavariable, left.lookup? metavariable = right.lookup? metavariable)
      (evidence : TypedTraitResolution.Evidence) :
      FlexibleSubstitution.applyEvidence left evidence =
        FlexibleSubstitution.applyEvidence right evidence := by
    cases evidence with
    | byImpl goal implementation premises =>
      simp only [FlexibleSubstitution.applyEvidence, predicate_function same,
        evidences_congr same premises]

  private theorem evidences_congr {left right : Substitution}
      (same : ∀ metavariable, left.lookup? metavariable = right.lookup? metavariable)
      (evidences : List TypedTraitResolution.Evidence) :
      FlexibleSubstitution.applyEvidences left evidences =
        FlexibleSubstitution.applyEvidences right evidences := by
    cases evidences with
    | nil => rfl
    | cons head tail =>
      simp only [FlexibleSubstitution.applyEvidences, evidence_congr same head,
        evidences_congr same tail]
end

private theorem solved_requirement_congr {left right : Substitution}
    (same : ∀ metavariable, left.lookup? metavariable = right.lookup? metavariable)
    (row : SolvedRequirement) :
    FlexibleSubstitution.applySolvedRequirement left row =
      FlexibleSubstitution.applySolvedRequirement right row := by
  have evidence_eq : FlexibleSubstitution.applyPredicateEvidence left row.evidence =
      FlexibleSubstitution.applyPredicateEvidence right row.evidence := by
    cases row.evidence <;> simp only [FlexibleSubstitution.applyPredicateEvidence,
      predicate_function same, evidence_congr same]
  simp only [FlexibleSubstitution.applySolvedRequirement, predicate_function same, evidence_eq]

private theorem locals_congr {left right : Substitution}
    (same : ∀ metavariable, left.lookup? metavariable = right.lookup? metavariable)
    (locals : Resolved.LocalScope Scheme) :
    FlexibleSubstitution.applyLocals left locals =
      FlexibleSubstitution.applyLocals right locals := by
  unfold FlexibleSubstitution.applyLocals
  apply List.map_congr_left
  intro entry _
  rw [scheme_congr same entry.2]

private theorem local_requirements_congr {left right : Substitution}
    (same : ∀ metavariable, left.lookup? metavariable = right.lookup? metavariable)
    (locals : Resolved.LocalScope Scheme)
    (requirements : Resolved.LocalScope (List LocalSchemeRequirement)) :
    FlexibleSubstitution.applyLocalSchemeRequirements left locals requirements =
      FlexibleSubstitution.applyLocalSchemeRequirements right locals requirements := by
  unfold FlexibleSubstitution.applyLocalSchemeRequirements
  apply List.map_congr_left
  intro entry _
  have local_same : ∀ metavariable,
      (FlexibleSubstitution.forLocal left locals entry.1).lookup? metavariable =
        (FlexibleSubstitution.forLocal right locals entry.1).lookup? metavariable := by
    cases found : locals.lookup? entry.1 with
    | none => simpa only [FlexibleSubstitution.forLocal, found] using same
    | some scheme =>
      simpa only [FlexibleSubstitution.forLocal, found] using
        masked_lookup same scheme.quantified
  simp only [requirement_function local_same]

/-- Closing the same initializer context retains every original local mask,
assumption and recursively mapped solved evidence row. -/
theorem closeContext_congr {left right : Substitution}
    (same : ∀ metavariable, left.lookup? metavariable = right.lookup? metavariable)
    (context : SourceSemantics.Context) :
    FlexibleSubstitution.closeContext left context =
      FlexibleSubstitution.closeContext right context := by
  have solved_function : FlexibleSubstitution.applySolvedRequirement left =
      FlexibleSubstitution.applySolvedRequirement right :=
    funext (solved_requirement_congr same)
  simp only [FlexibleSubstitution.closeContext, FlexibleSubstitution.applyContext,
    locals_congr same, local_requirements_congr same, predicate_function same,
    solved_function]

/-- Lookup agreement closes all fields of one genuine principal descriptor.
The captured locations and the supplied runtime evidence are exactly shared. -/
theorem instantiate_congr {left right : Substitution}
    (same : ∀ metavariable, left.lookup? metavariable = right.lookup? metavariable)
    (function : Dynamic.GeneralizedClosure) (evidence : Dynamic.EvidenceEnvironment) :
    function.instantiate left evidence = function.instantiate right evidence := by
  simp only [Dynamic.GeneralizedClosure.instantiate, binder_function same,
    apply_function same, typedSource_congr same, closeContext_congr same]

end Solcore.SourceSemantics.CoreLowering.CallableFlexibleSubstitutionAgreement
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableAppliedRuntimeMaterialization
/-! Attach the substitution chosen by an actual Dynamic local-scheme use to
the sealed compiler read. The complete matcher and runtime instantiation
determine equal substitution actions; the actual produced-plus-caller evidence
is retained literally. The live descriptor's source ancestry and the matching
scheme/type inputs remain explicit allocation/read obligations. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableAppliedRuntimeMaterialization
open Frontend SourceInference TypeSystem
open SourceCoreCallableAncestryReadRecipes

/-- Actual witness preparation determines the same variable lookups as the
runtime instantiation at the same scheme and raw occurrence type. -/
theorem read_lookup_eq
    {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {caller : SourceCoreCallableAncestryReadRecipes.State} {id target : Core.Word}
    (read : Read inputs caller id target)
    {context : Context} {callerEvidence produced : Dynamic.EvidenceEnvironment}
    {binder : TypedBinder} {actual : Ty} {requirements : List RequirementId}
    {semantic : Substitution}
    (instantiation : Dynamic.LocalSchemeRuntimeInstantiation context callerEvidence
      binder actual requirements semantic produced)
    (sameScheme : binder.scheme = read.binder.scheme)
    (sameType : actual = read.node.rawType) :
    ∀ metavariable, semantic.lookup? metavariable = read.substitution.lookup? metavariable := by
  have matched := CallableAncestryProfiles.SourceComposition.witnesses_matched read.factory
  change SourceSpecialization.matchClosedSchemeInstance? read.binder.scheme
    read.node.rawType = some read.substitution at matched
  apply CallableClosedSchemeSubstitutionAgreement.runtime_instantiation_lookup_eq
    (instantiation := instantiation)
  rw [sameScheme, sameType]
  exact matched

/-- The observed substitution yields exactly the same complete closure as
the read substitution when both retain this actual use's evidence. -/
theorem instantiated_closure_eq
    {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {caller : SourceCoreCallableAncestryReadRecipes.State} {id target : Core.Word}
    (read : Read inputs caller id target)
    {context : Context} {callerEvidence produced : Dynamic.EvidenceEnvironment}
    (function : Dynamic.GeneralizedClosure) {actual : Ty}
    {requirements : List RequirementId} {semantic : Substitution}
    (instantiation : Dynamic.LocalSchemeRuntimeInstantiation context callerEvidence
      function.binder actual requirements semantic produced)
    (sameScheme : function.binder.scheme = read.binder.scheme)
    (sameType : actual = read.node.rawType) :
    function.instantiate semantic (produced ++ callerEvidence.applySubstitution semantic) =
      function.instantiate read.substitution
        (produced ++ callerEvidence.applySubstitution semantic) :=
  CallableFlexibleSubstitutionAgreement.instantiate_congr
    (read_lookup_eq read instantiation sameScheme sameType) function _

/-- The real Dynamic use, including its observed substitution and evidence,
inherits the authenticated source recipe and exact native lambda header.
This consumes the descriptor's live source attachment; it does not reconstruct
that attachment from metadata ancestry or native frame decoding. -/
theorem materialize
    {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {callerFrame lexicalFrame : SourceCoreCallablePairedFrames.Frame}
    {caller lexical : SourceCoreCallableAncestryReadRecipes.State}
    {source : TypedSource} {id target : Core.Word}
    (paired : CallableAppliedDynamicSourceMaterialization.Pair inputs lexicalFrame lexical source)
    (recipe : CallableAppliedViewProvenance.Recipe inputs callerFrame lexicalFrame
      caller lexical id target)
    {definitionContext context : Context} {captured : Dynamic.Environment}
    {binder : TypedBinder} {function : Dynamic.GeneralizedClosure}
    (captures : Dynamic.GeneralizedClosureCaptures definitionContext source captured binder
      recipe.read.entry.view.principal.initializer function)
    (unique : NodeOccurrencesUnique source)
    {callerEvidence produced : Dynamic.EvidenceEnvironment} {actual : Ty}
    {requirements : List RequirementId} {semantic : Substitution}
    (instantiation : Dynamic.LocalSchemeRuntimeInstantiation context callerEvidence
      function.binder actual requirements semantic produced)
    (sameScheme : function.binder.scheme = recipe.read.binder.scheme)
    (sameType : actual = recipe.read.node.rawType) :
    let instantiated := function.instantiate semantic
      (produced ++ callerEvidence.applySubstitution semantic)
    CallableAppliedDynamicSourceMaterialization.Pair inputs
      (.appliedView id target callerFrame lexicalFrame)
      (recipe.read.after lexical) instantiated.source ∧
    CallableAncestryMetadata.eraseRequirements (recipe.read.after lexical).metadata.source =
      CallableAncestryMetadata.eraseRequirements instantiated.source ∧
    ExpressionForm.lambda instantiated.parameters instantiated.resultType instantiated.body =
      recipe.read.template.node.form ∧
    instantiated.captured = captured ∧
    instantiated.evidence = produced ++ callerEvidence.applySubstitution semantic := by
  dsimp only
  rw [instantiated_closure_eq recipe.read function instantiation sameScheme sameType]
  exact CallableAppliedDynamicSourceMaterialization.materialize paired recipe captures unique _

end Solcore.SourceSemantics.CoreLowering.CallableAppliedRuntimeMaterialization
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallablePairedContextFrames
/-! Native finite semantics for the two-parent carrier. A matching read view
keeps its saved caller separate from the lexical creation frame. These laws
concern actual Core evaluation and stores, not source history inferred from IDs.
-/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallablePairedContextFrames
open Core Frontend.SourceCoreCallablePairedFrames
open DataEquality (Selects)
abbrev PairedFrame := Frontend.SourceCoreCallablePairedFrames.Frame

theorem allocate_evaluates {layout : Layout} {environment : Environment} {before after : Store}
    {body : Expr} {result : Value}
    (evaluated : Evaluates (.cellRef layout.type before.length :: environment)
      (before ++ [encode layout .empty]) body result after) :
    Evaluates environment before (allocate layout body) result after :=
  .letE (.newCell (.construct .unit)) evaluated

private theorem lambda_selected {layout : Layout} {environment : Environment} {lexical : Expr}
    {frame : PairedFrame} (selected : Selects environment lexical (encode layout frame))
    (origin : Word) (store : Store) :
    Evaluates environment store (lambda layout origin lexical) (encode layout (.lambda origin frame)) store :=
  .construct (.pair .word (selected.evaluates store))

theorem lambdaFrame_evaluates {layout : Layout} {environment : Environment} {lexical current : Expr}
    {lexicalFrame currentFrame : PairedFrame} (origin : Word)
    (lexicalSelected : Selects environment lexical (encode layout lexicalFrame))
    (currentSelected : Selects environment current (encode layout currentFrame)) (store : Store) :
    Evaluates environment store (lambdaFrame layout origin lexical current)
      (encode layout (selectedFrame origin lexicalFrame currentFrame)) store := by
  cases currentFrame with
  | empty =>
    exact .matchData (currentSelected.evaluates store) rfl rfl (by
      simpa [lambda, Expr.weakenAt, selectedFrame] using lambda_selected (lexicalSelected.weaken .unit) origin store)
  | named id =>
    exact .matchData (currentSelected.evaluates store) rfl rfl (by
      simpa [lambda, Expr.weakenAt, selectedFrame] using lambda_selected (lexicalSelected.weaken (.word id)) origin store)
  | lambda id parent =>
    exact .matchData (currentSelected.evaluates store) rfl rfl (by
      simpa [lambda, Expr.weakenAt, selectedFrame] using lambda_selected (lexicalSelected.weaken (.pair (.word id) (encode layout parent))) origin store)
  | view id target caller =>
    apply Evaluates.matchData (currentSelected.evaluates store) rfl rfl
    by_cases equal : target = origin
    · simp only [selectedFrame, if_pos equal]
      apply Evaluates.ifTrue (.binary (.first (.second (.var rfl))) .word ?_)
      · exact .construct (.pair (.first (.var rfl)) (.pair .word
          (.pair (.second (.second (.var rfl))) ((lexicalSelected.weaken _).evaluates store))))
      · simp [BinaryOp.apply, equal]
    · simp only [selectedFrame, if_neg equal]
      apply Evaluates.ifFalse (.binary (.first (.second (.var rfl))) .word ?_)
      · simpa [lambda, Expr.weakenAt, selectedFrame] using lambda_selected
          (lexicalSelected.weaken (.pair (.word id) (.pair (.word target) (encode layout caller)))) origin store
      · simp [BinaryOp.apply, equal]
  | appliedView id target caller saved =>
    exact .matchData (currentSelected.evaluates store) rfl rfl (by
      simpa [lambda, Expr.weakenAt, selectedFrame] using lambda_selected
        (lexicalSelected.weaken (.pair (.word id) (.pair (.word target)
          (.pair (encode layout caller) (encode layout saved))))) origin store)

theorem lambdaFrame_reflects {layout : Layout} {environment : Environment} {before after : Store}
    {lexical current : Expr} {lexicalFrame currentFrame : PairedFrame} {origin : Word} {result : Value}
    (lexicalSelected : Selects environment lexical (encode layout lexicalFrame))
    (currentSelected : Selects environment current (encode layout currentFrame))
    (evaluated : Evaluates environment before (lambdaFrame layout origin lexical current) result after) :
    result = encode layout (selectedFrame origin lexicalFrame currentFrame) ∧ after = before :=
  evaluation_deterministic evaluated (lambdaFrame_evaluates origin lexicalSelected currentSelected before)

theorem lambdaFrame_run {layout : Layout} {environment : Environment} {store : Store}
    {lexical current : Expr} {lexicalFrame currentFrame : PairedFrame} (origin : Word)
    (lexicalSelected : Selects environment lexical (encode layout lexicalFrame))
    (currentSelected : Selects environment current (encode layout currentFrame)) :
    (∃ required, ∀ fuel, required ≤ fuel →
      runStateful fuel (.initial (lambdaFrame layout origin lexical current) environment store) =
        .done (encode layout (selectedFrame origin lexicalFrame currentFrame)) store) ∧
    (∀ fuel actual after,
      runStateful fuel (.initial (lambdaFrame layout origin lexical current) environment store) = .done actual after →
        actual = encode layout (selectedFrame origin lexicalFrame currentFrame) ∧ after = store) :=
  ⟨evaluation_runStateful_complete_with_sufficient_fuel (lambdaFrame_evaluates origin lexicalSelected currentSelected store),
    fun _ _ _ ran => lambdaFrame_reflects lexicalSelected currentSelected (runStateful_evaluation_sound ran)⟩

end Solcore.SourceSemantics.CoreLowering.CallablePairedContextFrames
end
