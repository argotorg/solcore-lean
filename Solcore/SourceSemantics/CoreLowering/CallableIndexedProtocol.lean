import Solcore.SourceSemantics.CoreLowering.CallableIndexedHistory
import Solcore.SourceSemantics.CoreLowering.CallableIndexedContextFrames

/-! Actual indexed dispatch evaluation carries ghost metadata derivations.
The mutable current-frame reference is read through its exact native slot.
We use the real extra match binder and do not weaken arbitrary closure values
or stores by an alleged exact-equality theorem. These finite helper laws do not
claim that every closure or allocation produced by the compiler already carries
this invariant; that requires the surrounding emitted-protocol induction. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedProtocol
open Core Frontend CallableAncestryPairedLookup CallableIndexedHistory
open SourceCoreCallableIndexedFrames SourceCoreCallableIndexedDispatch
open DataEquality (Selects)

/-- The lexical state match adds one integer slot before it executes current.
The premise is the actual child evaluation in that environment. -/
theorem lambdaFrame_read {layout : Layout} {environment : Environment} {store : Store}
    {lexical current : Expr} {position : Nat} {currentNative : NativeFrame}
    (table : SourceCoreCallableIndexedDispatch.Table) (origin : Word)
    (lexicalSelected : Selects environment lexical (encode layout (.state (Int.ofNat position))))
    (currentRead : Evaluates (.integer (Int.ofNat position) :: environment) store
      (current.weakenAt 0) (encode layout currentNative) store) :
    Evaluates environment store (lambdaFrame table layout origin lexical current)
      (encode layout (selectedFrame table origin (.state (Int.ofNat position)) currentNative)) store := by
  apply Evaluates.matchData (lexicalSelected.evaluates store) rfl rfl
  cases currentNative with
  | empty =>
    exact .matchData currentRead rfl rfl
      (CallableIndexedContextFrames.plainDispatch_evaluates table origin (.var rfl) _ store)
  | state index =>
    exact .matchData currentRead rfl rfl
      (CallableIndexedContextFrames.plainDispatch_evaluates table origin (.var rfl) _ store)
  | invalid =>
    exact .matchData currentRead rfl rfl
      (CallableIndexedContextFrames.plainDispatch_evaluates table origin (.var rfl) _ store)
  | view id target caller =>
    apply Evaluates.matchData currentRead rfl rfl
    by_cases same : target = origin
    · simp only [selectedFrame, if_pos same]
      apply Evaluates.ifTrue (.binary (.first (.second (.var rfl))) .word ?_)
      · exact CallableIndexedContextFrames.viewDispatch_evaluates table origin
          (.first (.var rfl)) (.second (.second (.var rfl))) (.var rfl) _ store
      · simp [BinaryOp.apply, same]
    · simp only [selectedFrame, if_neg same]
      apply Evaluates.ifFalse (.binary (.first (.second (.var rfl))) .word ?_)
      · exact CallableIndexedContextFrames.plainDispatch_evaluates table origin (.var rfl) _ store
      · simp [BinaryOp.apply, same]

/-- Reading the actual administrative reference supplies the child premise.
No statement about arbitrary effectful reference expressions is used. -/
theorem lambdaFrame_load {layout : Layout} {environment : Environment} {store : Store}
    {lexical : Expr} {position referenceIndex location : Nat} {currentNative : NativeFrame}
    (table : SourceCoreCallableIndexedDispatch.Table) (origin : Word)
    (lexicalSelected : Selects environment lexical (encode layout (.state (Int.ofNat position))))
    (reference : environment[referenceIndex]? = some (.cellRef layout.type location))
    (read : store.read? location = some (encode layout currentNative)) :
    Evaluates environment store (lambdaFrame table layout origin lexical (.loadCell (.var referenceIndex)))
      (encode layout (selectedFrame table origin (.state (Int.ofNat position)) currentNative)) store := by
  apply lambdaFrame_read table origin lexicalSelected
  simpa only [Expr.weakenAt, Nat.zero_le, decide_true, ↓reduceIte] using
    (show Evaluates (.integer (Int.ofNat position) :: environment) store (.loadCell (.var (referenceIndex + 1)))
      (encode layout currentNative) store from .loadCell (.var reference) read)

/-- The real read-view helper turns a carried stable caller into its transient
read token; the factory receipt keeps the caller's occurrence-specific IDs. -/
theorem read_evaluates {checked : Checked} {base : Base checked}
    (graph : SourceCoreCallableAncestryPairedPreparation.Prepared base)
    {layout : Layout} {environment : Environment} {store : Store} {current : Expr}
    {native : NativeFrame} {ghost : GhostFrame} {metadata : MetadataState} {id target : Word}
    (selected : Selects environment current (encode layout native))
    (carried : Carries graph.inputs graph.table native ghost (some metadata))
    (read : SourceCoreCallableAncestryReadRecipes.Read graph.inputs metadata id target)
    (prepared : SourceCoreCallableAncestryReadRecipes.prepareRead graph.inputs metadata id target = .ok read) :
    Evaluates environment store (readView layout id target current)
      (encode layout (readFrame id target native)) store ∧
    Current graph.inputs graph.table (readFrame id target native) (.view id target ghost) :=
  ⟨CallableIndexedContextFrames.readView_evaluates id target selected store,
    read_history carried read prepared⟩

theorem dispatch_evaluates {checked : Checked} {base : Base checked}
    (graph : SourceCoreCallableAncestryPairedPreparation.Prepared base)
    {layout : Layout} {environment : Environment} {store : Store} {lexical current : Expr}
    {lexicalNative currentNative : NativeFrame} {lexicalGhost currentGhost : GhostFrame}
    {metadata : MetadataState} {origin : Word}
    (lexicalSelected : Selects environment lexical (encode layout lexicalNative))
    (currentSelected : Selects environment current (encode layout currentNative))
    (carried : Carries graph.inputs graph.table lexicalNative lexicalGhost (some metadata))
    (currentHistory : Current graph.inputs graph.table currentNative currentGhost)
    (valid : selectedFrame graph.table origin lexicalNative currentNative ≠ .invalid) :
    ∃ resultState,
      Evaluates environment store (lambdaFrame graph.table layout origin lexical current)
        (encode layout (selectedFrame graph.table origin lexicalNative currentNative)) store ∧
      Carries graph.inputs graph.table (selectedFrame graph.table origin lexicalNative currentNative)
        (SourceCoreCallablePairedFrames.selectedFrame origin lexicalGhost currentGhost) (some resultState) := by
  obtain ⟨resultState, history⟩ := selection_history graph carried currentHistory valid
  exact ⟨resultState, CallableIndexedContextFrames.lambdaFrame_evaluates graph.table origin lexicalSelected currentSelected store, history⟩

/-- A completed native dispatch is reflected against the same independently
carried parents. Native determinism supplies result/store equality only. -/
theorem dispatch_reflects {checked : Checked} {base : Base checked}
    (graph : SourceCoreCallableAncestryPairedPreparation.Prepared base)
    {layout : Layout} {environment : Environment} {before after : Store} {lexical current : Expr}
    {lexicalNative currentNative : NativeFrame} {lexicalGhost currentGhost : GhostFrame}
    {metadata : MetadataState} {origin : Word} {result : Value}
    (lexicalSelected : Selects environment lexical (encode layout lexicalNative))
    (currentSelected : Selects environment current (encode layout currentNative))
    (carried : Carries graph.inputs graph.table lexicalNative lexicalGhost (some metadata))
    (currentHistory : Current graph.inputs graph.table currentNative currentGhost)
    (valid : selectedFrame graph.table origin lexicalNative currentNative ≠ .invalid)
    (evaluated : Evaluates environment before (lambdaFrame graph.table layout origin lexical current) result after) :
    result = encode layout (selectedFrame graph.table origin lexicalNative currentNative) ∧ after = before ∧
      ∃ resultState, Carries graph.inputs graph.table (selectedFrame graph.table origin lexicalNative currentNative)
        (SourceCoreCallablePairedFrames.selectedFrame origin lexicalGhost currentGhost) (some resultState) := by
  obtain ⟨resultState, expected, history⟩ := dispatch_evaluates graph lexicalSelected currentSelected carried currentHistory valid
  obtain ⟨sameResult, sameStore⟩ := evaluation_deterministic evaluated expected
  exact ⟨sameResult, sameStore, resultState, history⟩

/-- The load-based helper connects the cell receipt to the exact finite graph
transition. The source/Core body is not evaluated by this helper. -/
theorem dispatch_load {checked : Checked} {base : Base checked}
    (graph : SourceCoreCallableAncestryPairedPreparation.Prepared base)
    {layout : Layout} {environment : Environment} {store : Store} {lexical : Expr}
    {position referenceIndex location : Nat} {currentNative : NativeFrame} {lexicalGhost currentGhost : GhostFrame}
    {metadata : MetadataState} {origin : Word}
    (lexicalSelected : Selects environment lexical (encode layout (.state (Int.ofNat position))))
    (reference : environment[referenceIndex]? = some (.cellRef layout.type location))
    (carried : Carries graph.inputs graph.table (.state (Int.ofNat position)) lexicalGhost (some metadata))
    (cell : CellState graph.inputs graph.table layout location currentNative currentGhost store)
    (valid : selectedFrame graph.table origin (.state (Int.ofNat position)) currentNative ≠ .invalid) :
    ∃ resultState,
      Evaluates environment store (lambdaFrame graph.table layout origin lexical (.loadCell (.var referenceIndex)))
        (encode layout (selectedFrame graph.table origin (.state (Int.ofNat position)) currentNative)) store ∧
      Carries graph.inputs graph.table (selectedFrame graph.table origin (.state (Int.ofNat position)) currentNative)
        (SourceCoreCallablePairedFrames.selectedFrame origin lexicalGhost currentGhost) (some resultState) := by
  obtain ⟨resultState, history⟩ := selection_history graph carried cell.history valid
  exact ⟨resultState, lambdaFrame_load graph.table origin lexicalSelected reference cell.read, history⟩

/-- A completed native state result supplies the validity check itself.
The two carried parent histories are still required; decoded indices alone
are not promoted to authentication. -/
theorem dispatch_load_reflects_state {checked : Checked} {base : Base checked}
    (graph : SourceCoreCallableAncestryPairedPreparation.Prepared base)
    {layout : Layout} {environment : Environment} {before after : Store} {lexical : Expr}
    {position referenceIndex location : Nat} {resultIndex : Int} {currentNative : NativeFrame}
    {lexicalGhost currentGhost : GhostFrame} {metadata : MetadataState} {origin : Word}
    (lexicalSelected : Selects environment lexical (encode layout (.state (Int.ofNat position))))
    (reference : environment[referenceIndex]? = some (.cellRef layout.type location))
    (carried : Carries graph.inputs graph.table (.state (Int.ofNat position)) lexicalGhost (some metadata))
    (cell : CellState graph.inputs graph.table layout location currentNative currentGhost before)
    (evaluated : Evaluates environment before
      (lambdaFrame graph.table layout origin lexical (.loadCell (.var referenceIndex)))
      (encode layout (.state resultIndex)) after) :
    after = before ∧ ∃ resultState, Carries graph.inputs graph.table (.state resultIndex)
      (SourceCoreCallablePairedFrames.selectedFrame origin lexicalGhost currentGhost) (some resultState) := by
  have expected := lambdaFrame_load graph.table origin lexicalSelected reference cell.read
  obtain ⟨sameResult, sameStore⟩ := evaluation_deterministic evaluated expected
  have sameFrame : (.state resultIndex : NativeFrame) =
      selectedFrame graph.table origin (.state (Int.ofNat position)) currentNative := by
    have decoded := congrArg (decode layout) sameResult
    simpa only [decode_encode, Option.some.injEq] using decoded
  have valid : selectedFrame graph.table origin (.state (Int.ofNat position)) currentNative ≠ .invalid := by
    rw [← sameFrame]; simp
  obtain ⟨resultState, history⟩ := selection_history graph carried cell.history valid
  exact ⟨sameStore, resultState, sameFrame.symm ▸ history⟩

theorem dispatch_load_run {checked : Checked} {base : Base checked}
    (graph : SourceCoreCallableAncestryPairedPreparation.Prepared base)
    {layout : Layout} {environment : Environment} {store : Store} {lexical : Expr}
    {position referenceIndex location : Nat} {currentNative : NativeFrame} {lexicalGhost currentGhost : GhostFrame}
    {metadata : MetadataState} {origin : Word}
    (lexicalSelected : Selects environment lexical (encode layout (.state (Int.ofNat position))))
    (reference : environment[referenceIndex]? = some (.cellRef layout.type location))
    (carried : Carries graph.inputs graph.table (.state (Int.ofNat position)) lexicalGhost (some metadata))
    (cell : CellState graph.inputs graph.table layout location currentNative currentGhost store)
    (valid : selectedFrame graph.table origin (.state (Int.ofNat position)) currentNative ≠ .invalid) :
    (∃ required, ∀ fuel, required ≤ fuel →
      runStateful fuel (.initial (lambdaFrame graph.table layout origin lexical (.loadCell (.var referenceIndex))) environment store) =
        .done (encode layout (selectedFrame graph.table origin (.state (Int.ofNat position)) currentNative)) store) ∧
    (∀ fuel actual after,
      runStateful fuel (.initial (lambdaFrame graph.table layout origin lexical (.loadCell (.var referenceIndex))) environment store) =
        .done actual after →
      actual = encode layout (selectedFrame graph.table origin (.state (Int.ofNat position)) currentNative) ∧ after = store) ∧
    ∃ resultState, Carries graph.inputs graph.table (selectedFrame graph.table origin (.state (Int.ofNat position)) currentNative)
      (SourceCoreCallablePairedFrames.selectedFrame origin lexicalGhost currentGhost) (some resultState) := by
  obtain ⟨resultState, evaluated, history⟩ := dispatch_load graph lexicalSelected reference carried cell valid
  exact ⟨evaluation_runStateful_complete_with_sufficient_fuel evaluated,
    fun _ _ _ completed => evaluation_deterministic (runStateful_evaluation_sound completed) evaluated,
    resultState, history⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedProtocol
