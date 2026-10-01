import Solcore.SourceSemantics.CoreLowering.CallableIndexedProtocol
import Solcore.SourceSemantics.CoreLowering.CallableIndexedRenaming

/-! Finite indexed lambda entry and restoration in the actual administrative
binder layout. The child body runs in its emitted environment and store.
These compositional laws preserve carried metadata; they do not supply the
source/Core body correspondence or authenticate arbitrary native closures. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedEntry
open Core Frontend CallableAncestryPairedLookup CallableIndexedHistory
open SourceCoreCallableIndexedFrames SourceCoreCallableIndexedDispatch
open DataEquality (Selects)

private theorem installed_history {checked : Checked} {base : Base checked} {inputs : Inputs base} {table : SourceCoreCallableIndexedDispatch.Table}
    {layout : Layout} {location : Location} {before : Store} {saved : Value} {native : NativeFrame} {ghost : GhostFrame}
    (read : before.read? location = some saved) (history : Current inputs table native ghost) :
    CellState inputs table layout location native ghost (before.set location (encode layout native)) := by
  have written : before.write? location (encode layout native) = some (before.set location (encode layout native)) :=
    Store.write?_eq_some_iff.mpr ⟨(List.getElem?_eq_some_iff.mp read).1, rfl⟩
  exact ⟨Store.write?_reads_written written, history⟩

/-- The exact selector after the caller frame has been saved. The syntactic
insertion law shifts emitted code using its exact insertion receipt. -/
theorem lambda_next_evaluates {layout : Layout} {environment : Environment} {before : Store}
    {referenceIndex location position : Nat} {current : NativeFrame}
    (table : SourceCoreCallableIndexedDispatch.Table) (origin : Word)
    (reference : environment[referenceIndex]? = some (.cellRef layout.type location))
    (lexicalSelected : environment[1]? = some (encode layout (.state (Int.ofNat position))))
    (read : before.read? location = some (encode layout current)) :
    Evaluates (encode layout current :: environment) before
      ((lambdaFrame table layout origin (.var 1) (.loadCell (.var referenceIndex))).weakenAt 0)
      (encode layout (selectedFrame table origin (.state (Int.ofNat position)) current)) before := by
  rw [CallableIndexedRenaming.lambdaFrame_weaken]
  simp only [Expr.weakenAt, Nat.zero_le, ↓reduceIte]
  exact CallableIndexedProtocol.lambdaFrame_load table origin (.var lexicalSelected)
    (by simpa using reference) read

/-- Entry uses the caller's actual current token and the lambda's independently
captured lexical token, then restores the caller even on language failure. -/
theorem lambda_body_evaluates {checked : Checked} {base : Base checked}
    (graph : SourceCoreCallableAncestryPairedPreparation.Prepared base)
    {layout : Layout} {origin : Word} {referenceIndex location position : Nat} {body : Expr}
    {environment : Environment} {argument result : Value} {before after : Store}
    {current : NativeFrame} {lexicalGhost currentGhost : GhostFrame} {metadata : MetadataState}
    (reference : environment[referenceIndex]? = some (.cellRef layout.type location))
    (caller : CellState graph.inputs graph.table layout location current currentGhost before)
    (lexical : Carries graph.inputs graph.table (.state (Int.ofNat position)) lexicalGhost (some metadata))
    (valid : selectedFrame graph.table origin (.state (Int.ofNat position)) current ≠ .invalid)
    (bodyEvaluation : Evaluates
      (.unit :: encode layout current :: argument :: encode layout (.state (Int.ofNat position)) :: environment)
      (before.set location (encode layout (selectedFrame graph.table origin (.state (Int.ofNat position)) current)))
      (((body.weakenAt 1).weakenAt 0).weakenAt 0) result after) :
    ∃ resultState,
      Carries graph.inputs graph.table (selectedFrame graph.table origin (.state (Int.ofNat position)) current)
        (SourceCoreCallablePairedFrames.selectedFrame origin lexicalGhost currentGhost) (some resultState) ∧
      CellState graph.inputs graph.table layout location (selectedFrame graph.table origin (.state (Int.ofNat position)) current)
        (SourceCoreCallablePairedFrames.selectedFrame origin lexicalGhost currentGhost)
        (before.set location (encode layout (selectedFrame graph.table origin (.state (Int.ofNat position)) current))) ∧
      Evaluates (argument :: encode layout (.state (Int.ofNat position)) :: environment) before
        (withFrame (.var (referenceIndex + 2))
          (lambdaFrame graph.table layout origin (.var 1) (.loadCell (.var (referenceIndex + 2)))) (body.weakenAt 1))
        result (after.set location (encode layout current)) ∧
      CellState graph.inputs graph.table layout location current currentGhost (after.set location (encode layout current)) := by
  have selected : Selects (argument :: encode layout (.state (Int.ofNat position)) :: environment)
      (.var (referenceIndex + 2)) (.cellRef layout.type location) := .var (by simpa [Nat.add_assoc] using reference)
  have next := lambda_next_evaluates (referenceIndex := referenceIndex + 2) graph.table origin
    (by simpa [Nat.add_assoc] using reference)
    (show (argument :: encode layout (.state (Int.ofNat position)) :: environment)[1]? =
      some (encode layout (.state (Int.ofNat position))) from rfl) caller.read
  have evaluated := CallableContextFrames.withFrame_evaluates selected caller.read next bodyEvaluation
  obtain ⟨resultState, carried⟩ := selection_history graph lexical caller.history valid
  exact ⟨resultState, carried, installed_history caller.read (.stable carried), evaluated,
    ⟨(CallableContextFrames.withFrame_restores selected caller.read evaluated).1, caller.history⟩⟩

/-- Inversion exposes the real child trace and preserves the restored caller.
The completed native wrapper is the only body-execution premise. -/
theorem lambda_body_reflects {checked : Checked} {base : Base checked}
    (graph : SourceCoreCallableAncestryPairedPreparation.Prepared base)
    {layout : Layout} {origin : Word} {referenceIndex location position : Nat} {body : Expr}
    {environment : Environment} {argument result : Value} {before finalStore : Store}
    {current : NativeFrame} {lexicalGhost currentGhost : GhostFrame} {metadata : MetadataState}
    (reference : environment[referenceIndex]? = some (.cellRef layout.type location))
    (caller : CellState graph.inputs graph.table layout location current currentGhost before)
    (lexical : Carries graph.inputs graph.table (.state (Int.ofNat position)) lexicalGhost (some metadata))
    (valid : selectedFrame graph.table origin (.state (Int.ofNat position)) current ≠ .invalid)
    (evaluation : Evaluates (argument :: encode layout (.state (Int.ofNat position)) :: environment) before
      (withFrame (.var (referenceIndex + 2))
        (lambdaFrame graph.table layout origin (.var 1) (.loadCell (.var (referenceIndex + 2)))) (body.weakenAt 1)) result finalStore) :
    (∃ resultState, Carries graph.inputs graph.table (selectedFrame graph.table origin (.state (Int.ofNat position)) current)
      (SourceCoreCallablePairedFrames.selectedFrame origin lexicalGhost currentGhost) (some resultState)) ∧
    (∃ bodyStore, Evaluates (.unit :: encode layout current :: argument :: encode layout (.state (Int.ofNat position)) :: environment)
      (before.set location (encode layout (selectedFrame graph.table origin (.state (Int.ofNat position)) current)))
      (((body.weakenAt 1).weakenAt 0).weakenAt 0) result bodyStore ∧
      finalStore = bodyStore.set location (encode layout current)) ∧
    CellState graph.inputs graph.table layout location current currentGhost finalStore := by
  have selected : Selects (argument :: encode layout (.state (Int.ofNat position)) :: environment)
      (.var (referenceIndex + 2)) (.cellRef layout.type location) := .var (by simpa [Nat.add_assoc] using reference)
  obtain ⟨installed, nextStore, bodyStore, nextEvaluation, bodyEvaluation, finalEq⟩ :=
    CallableContextFrames.withFrame_reflects selected caller.read evaluation
  have expected := lambda_next_evaluates (referenceIndex := referenceIndex + 2) graph.table origin
    (by simpa [Nat.add_assoc] using reference)
    (show (argument :: encode layout (.state (Int.ofNat position)) :: environment)[1]? =
      some (encode layout (.state (Int.ofNat position))) from rfl) caller.read
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic nextEvaluation expected
  exact ⟨selection_history graph lexical caller.history valid, ⟨bodyStore, bodyEvaluation, finalEq⟩,
    ⟨(CallableContextFrames.withFrame_restores selected caller.read evaluation).1, caller.history⟩⟩

/-- A named entry uses the real named cache row and restores whichever stable
or transient token was active at the call site. -/
theorem named_body_evaluates {checked : Checked} {base : Base checked}
    (graph : SourceCoreCallableAncestryPairedPreparation.Prepared base)
    {layout : Layout} {origin : Word} {position : Nat} {reference body : Expr}
    {environment : Environment} {result : Value} {before after : Store} {location : Location}
    {current : NativeFrame} {currentGhost : GhostFrame}
    (selected : graph.table.namedAt? origin = some position)
    (referenceSelected : Selects environment reference (.cellRef layout.type location))
    (caller : CellState graph.inputs graph.table layout location current currentGhost before)
    (bodyEvaluation : Evaluates (.unit :: encode layout current :: environment)
      (before.set location (encode layout (namedFrame graph.table origin)))
      ((body.weakenAt 0).weakenAt 0) result after) :
    ∃ metadata,
      Carries graph.inputs graph.table (namedFrame graph.table origin) (.named origin) (some metadata) ∧
      CellState graph.inputs graph.table layout location (namedFrame graph.table origin) (.named origin)
        (before.set location (encode layout (namedFrame graph.table origin))) ∧
      Evaluates environment before (withFrame reference (literal layout (namedFrame graph.table origin)) body)
        result (after.set location (encode layout current)) ∧
      CellState graph.inputs graph.table layout location current currentGhost (after.set location (encode layout current)) := by
  have next : Evaluates (encode layout current :: environment) before
      ((literal layout (namedFrame graph.table origin)).weakenAt 0)
      (encode layout (namedFrame graph.table origin)) before := by
    rw [← Expr.rename_insertion, CallableIndexedRenaming.literal]
    exact CallableIndexedContextFrames.literal_evaluates layout _ _ _
  have evaluated := CallableContextFrames.withFrame_evaluates referenceSelected caller.read next bodyEvaluation
  obtain ⟨metadata, history⟩ := named_history graph selected
  exact ⟨metadata, history, installed_history caller.read (.stable history), evaluated,
    ⟨(CallableContextFrames.withFrame_restores referenceSelected caller.read evaluated).1, caller.history⟩⟩

/-- An instantiated read wrapper installs its captured read-time caller, even
when its eventual calling context differs. The underlying payload's execution
is the explicit child trace in the wrapper's actual administrative context. -/
theorem view_body_evaluates {checked : Checked} {base : Base checked}
    (graph : SourceCoreCallableAncestryPairedPreparation.Prepared base)
    {layout : Layout} {id target : Word} {position referenceIndex location : Nat}
    {environment : Environment} {argument original result : Value} {before after : Store}
    {current : NativeFrame} {readerGhost currentGhost : GhostFrame} {metadata : MetadataState}
    (reference : environment[referenceIndex]? = some (.cellRef layout.type location))
    (caller : CellState graph.inputs graph.table layout location current currentGhost before)
    (reader : Carries graph.inputs graph.table (.state (Int.ofNat position)) readerGhost (some metadata))
    (read : SourceCoreCallableAncestryReadRecipes.Read graph.inputs metadata id target)
    (prepared : SourceCoreCallableAncestryReadRecipes.prepareRead graph.inputs metadata id target = .ok read)
    (bodyEvaluation : Evaluates
      (.unit :: encode layout current :: argument :: encode layout (.state (Int.ofNat position)) :: original :: environment)
      (before.set location (encode layout (.view id target (Int.ofNat position))))
      (((Expr.apply (.second (.first (.var 2))) (.var 0)).weakenAt 0).weakenAt 0) result after) :
    CellState graph.inputs graph.table layout location (.view id target (Int.ofNat position)) (.view id target readerGhost)
      (before.set location (encode layout (.view id target (Int.ofNat position)))) ∧
    Evaluates (argument :: encode layout (.state (Int.ofNat position)) :: original :: environment) before
      (withFrame (.var (referenceIndex + 3)) (readView layout id target (.var 1))
        (.apply (.second (.first (.var 2))) (.var 0))) result (after.set location (encode layout current)) ∧
    CellState graph.inputs graph.table layout location current currentGhost (after.set location (encode layout current)) := by
  have selected : Selects (argument :: encode layout (.state (Int.ofNat position)) :: original :: environment)
      (.var (referenceIndex + 3)) (.cellRef layout.type location) := .var (by simpa [Nat.add_assoc] using reference)
  have next : Evaluates
      (encode layout current :: argument :: encode layout (.state (Int.ofNat position)) :: original :: environment) before
      ((readView layout id target (.var 1)).weakenAt 0)
      (encode layout (.view id target (Int.ofNat position))) before := by
    rw [CallableIndexedRenaming.readView_weaken]
    simpa only [Expr.weakenAt, Nat.zero_le, ↓reduceIte, readFrame] using
      CallableIndexedContextFrames.readView_evaluates (layout := layout)
      (environment := encode layout current :: argument :: encode layout (.state (Int.ofNat position)) :: original :: environment)
      (current := .var 2) (currentFrame := .state (Int.ofNat position)) id target (.var rfl) before
  have history : Current graph.inputs graph.table (.view id target (Int.ofNat position)) (.view id target readerGhost) :=
    .reading reader read prepared
  have evaluated := CallableContextFrames.withFrame_evaluates selected caller.read next bodyEvaluation
  exact ⟨installed_history caller.read history, evaluated,
    ⟨(CallableContextFrames.withFrame_restores selected caller.read evaluated).1, caller.history⟩⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedEntry
