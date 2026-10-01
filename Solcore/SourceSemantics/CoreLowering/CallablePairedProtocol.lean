import Solcore.SourceSemantics.CoreLowering.CallableAncestryPairedSeeds
import Solcore.SourceSemantics.CoreLowering.CallablePairedContextFrames
import Solcore.Frontend.SourceCoreCallablePairedAncestry
import Solcore.Frontend.SourceCoreCallablePairedAllocationFrames

/-! Finite laws for the emitted paired-frame protocol with carried metadata
history. A loaded value is not authenticated merely by its native type or ID.
Stable frames carry independent metadata authentication; the transient read tag
retains its actual read factory receipt and read-time caller. Body execution
remains an explicit compositional premise in its real administrative context.
-/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallablePairedProtocol
open Core Frontend CallableAncestryPairedLookup
open SourceCoreCallablePairedFrames
open DataEquality (Selects)
abbrev MetadataState := SourceCoreCallableAncestryReadRecipes.State
abbrev PairedFrame := SourceCoreCallablePairedFrames.Frame

/-- Transient tags are protocol states, not principal execution-source states.
Only stable frames are passed to the principal metadata lookup theorem. -/
inductive Current {checked : Checked} {base : Base checked} (inputs : Inputs base) : PairedFrame → Prop where
  | stable {frame : PairedFrame} {state : Option MetadataState}
      (history : Authenticates inputs frame state) : Current inputs frame
  | reading {caller : PairedFrame} {state : MetadataState} {id target : Word}
      (history : Authenticates inputs caller (some state))
      (read : SourceCoreCallableAncestryReadRecipes.Read inputs state id target)
      (prepared : SourceCoreCallableAncestryReadRecipes.prepareRead inputs state id target = .ok read) :
      Current inputs (.view id target caller)

structure CellState {checked : Checked} {base : Base checked} (inputs : Inputs base)
    (layout : Layout) (location : Location) (frame : PairedFrame) (store : Store) : Prop where
  read : store.read? location = some (encode layout frame)
  history : Current inputs frame

/-- A lambda's exact descriptor transition is separate from its native type.
Applied views authenticate the read caller and lexical principal separately. -/
inductive Entry {checked : Checked} {base : Base checked} (inputs : Inputs base) (origin : Word)
    (lexical : PairedFrame) : PairedFrame → MetadataState → Prop where
  | ordinary {current : PairedFrame} {state : MetadataState}
      (history : Authenticates inputs lexical (some state))
      (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed inputs state origin = true)
      (unmatched : ∀ id caller, current ≠ .view id origin caller) : Entry inputs origin lexical current state
  | applied {caller : PairedFrame} {callerState lexicalState : MetadataState} {id : Word}
      (callerHistory : Authenticates inputs caller (some callerState))
      (lexicalHistory : Authenticates inputs lexical (some lexicalState))
      (read : SourceCoreCallableAncestryReadRecipes.Read inputs callerState id origin)
      (readPrepared : SourceCoreCallableAncestryReadRecipes.prepareRead inputs callerState id origin = .ok read)
      (applied : SourceCoreCallableAncestryReadRecipes.Applied read lexicalState)
      (appliedPrepared : SourceCoreCallableAncestryReadRecipes.applyRead read lexicalState = .ok applied) :
      Entry inputs origin lexical (.view id origin caller) (read.after lexicalState)

theorem Entry.authenticates {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {origin : Word} {lexical current : PairedFrame} {state : MetadataState}
    (entry : Entry inputs origin lexical current state) :
    Authenticates inputs (selectedFrame origin lexical current) (some state) := by
  cases entry with
  | ordinary history allowed unmatched =>
    have same : selectedFrame origin lexical current = .lambda origin lexical := by
      cases current <;> simp only [selectedFrame]
      next id target caller =>
        by_cases sameTarget : target = origin
        · subst target; exact False.elim (unmatched id caller rfl)
        · simp only [sameTarget, ↓reduceIte]
    rw [same]
    exact .lambda history allowed
  | applied callerHistory lexicalHistory read readPrepared applied appliedPrepared =>
    simp only [selectedFrame, ↓reduceIte]
    apply Authenticates.appliedView callerHistory lexicalHistory
    simp only [SourceCoreCallableAncestryPairedPreparation.view?, readPrepared, appliedPrepared,
      Except.toOption, bind, Option.bind, pure]

private theorem lambda_selected {layout : Layout} {environment : Environment} {lexical : Expr}
    {frame : PairedFrame} (selected : Selects environment lexical (encode layout frame))
    (origin : Word) (store : Store) :
    Evaluates environment store (lambda layout origin lexical) (encode layout (.lambda origin frame)) store :=
  .construct (.pair .word (selected.evaluates store))

/-- The actual hook reads the current frame from the administrative cell.
That read may be a native expression; it must preserve the store. -/
theorem lambdaFrame_read {layout : Layout} {environment : Environment} {store : Store}
    {lexical current : Expr} {lexicalFrame currentFrame : PairedFrame} (origin : Word)
    (lexicalSelected : Selects environment lexical (encode layout lexicalFrame))
    (currentRead : Evaluates environment store current (encode layout currentFrame) store) :
    Evaluates environment store (lambdaFrame layout origin lexical current)
      (encode layout (selectedFrame origin lexicalFrame currentFrame)) store := by
  cases currentFrame with
  | empty =>
    exact .matchData currentRead rfl rfl (by
      simpa [lambda, Expr.weakenAt, selectedFrame] using lambda_selected (lexicalSelected.weaken .unit) origin store)
  | named id =>
    exact .matchData currentRead rfl rfl (by
      simpa [lambda, Expr.weakenAt, selectedFrame] using lambda_selected (lexicalSelected.weaken (.word id)) origin store)
  | lambda id parent =>
    exact .matchData currentRead rfl rfl (by
      simpa [lambda, Expr.weakenAt, selectedFrame] using lambda_selected (lexicalSelected.weaken (.pair (.word id) (encode layout parent))) origin store)
  | view id target caller =>
    apply Evaluates.matchData currentRead rfl rfl
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
    exact .matchData currentRead rfl rfl (by
      simpa [lambda, Expr.weakenAt, selectedFrame] using lambda_selected
        (lexicalSelected.weaken (.pair (.word id) (.pair (.word target)
          (.pair (encode layout caller) (encode layout saved))))) origin store)

theorem lambdaFrame_read_reflects {layout : Layout} {environment : Environment} {before after : Store}
    {lexical current : Expr} {lexicalFrame currentFrame : PairedFrame} {origin : Word} {result : Value}
    (lexicalSelected : Selects environment lexical (encode layout lexicalFrame))
    (currentRead : Evaluates environment before current (encode layout currentFrame) before)
    (evaluated : Evaluates environment before (lambdaFrame layout origin lexical current) result after) :
    result = encode layout (selectedFrame origin lexicalFrame currentFrame) ∧ after = before :=
  evaluation_deterministic evaluated (lambdaFrame_read origin lexicalSelected currentRead)

/-- The saved source ancestry is exactly the value loaded at lambda creation,
including the actual native environment order used by snapshotLambda. -/
def LambdaSnapshot {checked : Checked} {base : Base checked} (inputs : Inputs base)
    (layout : Layout) (origin : Word) (referenceIndex : Nat) (parameter result : Ty) (body : Expr)
    (environment : Environment) (value : Value) : Prop :=
  ∃ (frame : PairedFrame) (state : MetadataState), Authenticates inputs frame (some state) ∧
    value = .closure parameter (LanguageResult.resultType result)
    (withFrame (.var (referenceIndex + 2))
      (lambdaFrame layout origin (.var 1) (.loadCell (.var (referenceIndex + 2)))) (body.weakenAt 1))
    (encode layout frame :: environment)

theorem snapshotLambda_history {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {layout : Layout} {origin : Word} {referenceIndex location : Nat} {parameter result : Ty} {body : Expr}
    {environment : Environment} {store : Store} {frame : PairedFrame} {state : MetadataState}
    (reference : environment[referenceIndex]? = some (.cellRef layout.type location))
    (read : store.read? location = some (encode layout frame))
    (history : Authenticates inputs frame (some state)) :
    ∃ value, Evaluates environment store
      (SourceCoreCallablePairedAncestry.snapshotLambda layout origin referenceIndex parameter result body) value store ∧
      LambdaSnapshot inputs layout origin referenceIndex parameter result body environment value :=
  ⟨_, SourceCoreCallablePairedAncestry.snapshotLambda_evaluates origin reference read, ⟨frame, state, history, rfl⟩⟩

/-- Allocation snapshots retain the actual stable creation frame at the new
administrative index. The source allocation runs in its real inserted slot. -/
theorem snapshotBefore_history {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {layout : Layout} {reference allocation : Expr} {location : Location} {frame : PairedFrame} {state : Option MetadataState}
    {environment : Environment} {before after : Store} {result : Value}
    (selected : Selects environment reference (.cellRef layout.type location))
    (read : before.read? location = some (encode layout frame))
    (history : Authenticates inputs frame state)
    (evaluated : Evaluates (.cellRef layout.type before.length :: environment) (before ++ [encode layout frame])
      (allocation.weakenAt 0) result after) :
    Evaluates environment before (SourceCoreCallablePairedAllocationFrames.snapshotBefore layout reference allocation) result after ∧
    (before ++ [encode layout frame]).read? before.length = some (encode layout frame) ∧ Authenticates inputs frame state := by
  exact ⟨.letE (.newCell (.loadCell (selected.evaluates before) read)) evaluated, by simp [Store.read?], history⟩


private theorem installed_history {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {layout : Layout} {location : Location} {before : Store} {old frame : PairedFrame}
    (read : before.read? location = some (encode layout old)) (history : Current inputs frame) :
    CellState inputs layout location frame (before.set location (encode layout frame)) := by
  have written : before.write? location (encode layout frame) = some (before.set location (encode layout frame)) :=
    Store.write?_eq_some_iff.mpr ⟨(List.getElem?_eq_some_iff.mp read).1, rfl⟩
  exact ⟨Store.write?_reads_written written, history⟩

/-- The exact lambda-body selector after withFrame saves the caller. This
lemma evaluates the emitted load, including its real additional binder. -/
theorem lambda_next_evaluates {layout : Layout} {environment : Environment} {before : Store}
    {referenceIndex location : Nat} {lexical current : PairedFrame} (origin : Word)
    (reference : environment[referenceIndex]? = some (.cellRef layout.type location))
    (lexicalSelected : environment[1]? = some (encode layout lexical))
    (read : before.read? location = some (encode layout current)) :
    Evaluates (encode layout current :: environment) before
      ((lambdaFrame layout origin (.var 1) (.loadCell (.var referenceIndex))).weakenAt 0)
      (encode layout (selectedFrame origin lexical current)) before := by
  have shifted : (lambdaFrame layout origin (.var 1) (.loadCell (.var referenceIndex))).weakenAt 0 =
      lambdaFrame layout origin (.var 2) (.loadCell (.var (referenceIndex + 1))) := by
    simp [lambdaFrame, lambda, Expr.weakenAt]
  rw [shifted]
  exact lambdaFrame_read origin (.var lexicalSelected) (.loadCell (.var (by simpa using reference)) read)

/-- Actual emitted lambda-body entry installs an authenticated execution frame
and restores its exact caller, even when the result is a language failure.
The child runs under all four administrative/argument slots actually emitted. -/
theorem lambda_body_evaluates {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {layout : Layout} {origin : Word} {referenceIndex location : Nat} {body : Expr}
    {environment : Environment} {argument result : Value} {before after : Store}
    {lexical current : PairedFrame} {state : MetadataState}
    (reference : environment[referenceIndex]? = some (.cellRef layout.type location))
    (caller : CellState inputs layout location current before)
    (entry : Entry inputs origin lexical current state)
    (bodyEvaluation : Evaluates
      (.unit :: encode layout current :: argument :: encode layout lexical :: environment)
      (before.set location (encode layout (selectedFrame origin lexical current)))
      (((body.weakenAt 1).weakenAt 0).weakenAt 0) result after) :
    CellState inputs layout location (selectedFrame origin lexical current)
        (before.set location (encode layout (selectedFrame origin lexical current))) ∧
    Evaluates (argument :: encode layout lexical :: environment) before
      (withFrame (.var (referenceIndex + 2))
        (lambdaFrame layout origin (.var 1) (.loadCell (.var (referenceIndex + 2)))) (body.weakenAt 1))
      result (after.set location (encode layout current)) ∧
    CellState inputs layout location current (after.set location (encode layout current)) := by
  have selected : Selects (argument :: encode layout lexical :: environment)
      (.var (referenceIndex + 2)) (.cellRef layout.type location) := .var (by simpa [Nat.add_assoc] using reference)
  have next := lambda_next_evaluates (referenceIndex := referenceIndex + 2) origin (by simpa [Nat.add_assoc] using reference)
    (show (argument :: encode layout lexical :: environment)[1]? = some (encode layout lexical) from rfl) caller.read
  have evaluated := CallableContextFrames.withFrame_evaluates selected caller.read next bodyEvaluation
  exact ⟨installed_history caller.read (.stable entry.authenticates), evaluated,
    ⟨(CallableContextFrames.withFrame_restores selected caller.read evaluated).1, caller.history⟩⟩

/-- Completed emitted code exposes the real body trace and exact restoration;
no successful source trace is a premise of this inversion. -/
theorem lambda_body_reflects {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {layout : Layout} {origin : Word} {referenceIndex location : Nat} {body : Expr}
    {environment : Environment} {argument result : Value} {before finalStore : Store}
    {lexical current : PairedFrame} {state : MetadataState}
    (reference : environment[referenceIndex]? = some (.cellRef layout.type location))
    (caller : CellState inputs layout location current before)
    (entry : Entry inputs origin lexical current state)
    (evaluation : Evaluates (argument :: encode layout lexical :: environment) before
      (withFrame (.var (referenceIndex + 2))
        (lambdaFrame layout origin (.var 1) (.loadCell (.var (referenceIndex + 2)))) (body.weakenAt 1)) result finalStore) :
    Authenticates inputs (selectedFrame origin lexical current) (some state) ∧
    (∃ bodyStore, Evaluates (.unit :: encode layout current :: argument :: encode layout lexical :: environment)
      (before.set location (encode layout (selectedFrame origin lexical current)))
      (((body.weakenAt 1).weakenAt 0).weakenAt 0) result bodyStore ∧
      finalStore = bodyStore.set location (encode layout current)) ∧
    CellState inputs layout location current finalStore := by
  have selected : Selects (argument :: encode layout lexical :: environment)
      (.var (referenceIndex + 2)) (.cellRef layout.type location) := .var (by simpa [Nat.add_assoc] using reference)
  obtain ⟨installed, nextStore, bodyStore, nextEvaluation, bodyEvaluation, finalEq⟩ :=
    CallableContextFrames.withFrame_reflects selected caller.read evaluation
  have expected := lambda_next_evaluates (referenceIndex := referenceIndex + 2) origin (by simpa [Nat.add_assoc] using reference)
    (show (argument :: encode layout lexical :: environment)[1]? = some (encode layout lexical) from rfl) caller.read
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic nextEvaluation expected
  exact ⟨entry.authenticates, ⟨bodyStore, bodyEvaluation, finalEq⟩,
    ⟨(CallableContextFrames.withFrame_restores selected caller.read evaluation).1, caller.history⟩⟩


/-- A read wrapper captures the actual successful read's caller. Its lexical
payload is passed through exactly; authenticating that payload is an independent
lambda-snapshot receipt, not a consequence of its projected function type. -/
theorem viewLower_history {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {layout : Layout} {environment : Environment} {before after : Store} {readCode : Expr}
    {parameter result : Ty} {id target descriptor : Word} {referenceIndex location : Nat}
    {identity originalPayload : Value} {caller : PairedFrame} {callerState : MetadataState}
    (history : Authenticates inputs caller (some callerState))
    (read : SourceCoreCallableAncestryReadRecipes.Read inputs callerState id target)
    (prepared : SourceCoreCallableAncestryReadRecipes.prepareRead inputs callerState id target = .ok read)
    (evaluated : Evaluates environment before readCode
      (.inRight .word (.pair (.pair identity originalPayload) (.word descriptor))) after)
    (reference : environment[referenceIndex]? = some (.cellRef layout.type location))
    (snapshot : after.read? location = some (encode layout caller)) :
    Evaluates environment before (SourceCoreCallablePairedAncestry.viewLower layout parameter result id target referenceIndex readCode)
      (.inRight .word (.pair (.pair identity
        (.closure parameter (LanguageResult.resultType result)
          (SourceCoreCallablePairedAncestry.viewBody layout id target referenceIndex)
          (encode layout caller :: .pair (.pair identity originalPayload) (.word descriptor) :: environment))) (.word descriptor))) after ∧
    Current inputs (.view id target caller) :=
  ⟨SourceCoreCallablePairedAncestry.viewLower_evaluates evaluated reference snapshot, .reading history read prepared⟩

/-- Named entry resets execution metadata to its exact named plan receipt,
then restores the previous stable or transient protocol frame on completion. -/
theorem named_body_evaluates {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {layout : Layout} {environment : Environment} {before after : Store} {body : Expr}
    {referenceIndex location : Nat} {origin : Word} {state : MetadataState} {caller : PairedFrame} {result : Value}
    (reference : environment[referenceIndex]? = some (.cellRef layout.type location))
    (saved : CellState inputs layout location caller before)
    (namedReceipt : SourceCoreCallableAncestryPairedPreparation.named? inputs origin = some state)
    (bodyEvaluation : Evaluates (.unit :: encode layout caller :: environment)
      (before.set location (encode layout (.named origin))) ((body.weakenAt 0).weakenAt 0) result after) :
    CellState inputs layout location (.named origin) (before.set location (encode layout (.named origin))) ∧
    Evaluates environment before (withFrame (.var referenceIndex) (named layout origin) body)
      result (after.set location (encode layout caller)) ∧
    CellState inputs layout location caller (after.set location (encode layout caller)) := by
  have next : Evaluates (encode layout caller :: environment) before ((named layout origin).weakenAt 0)
      (encode layout (.named origin)) before := by
    simpa [named, Expr.weakenAt, encode] using
      (show Evaluates (encode layout caller :: environment) before (.construct layout.named (.word origin))
        (.constructed layout.named (.word origin)) before from .construct .word)
  have evaluated := CallableContextFrames.withFrame_evaluates (.var reference) saved.read next bodyEvaluation
  exact ⟨installed_history saved.read (.stable (.named namedReceipt)), evaluated,
    ⟨(CallableContextFrames.withFrame_restores (.var reference) saved.read evaluated).1, saved.history⟩⟩

/-- Pending execution keeps its real checkpoint. The native resumption law
preserves the eventual caller restoration; it does not call exhaustion a
source completion or claim the caller is installed while execution is paused. -/
theorem lambda_body_resumed_finishes {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {layout : Layout} {origin : Word} {referenceIndex location : Nat} {body : Expr}
    {environment : Environment} {argument result : Value} {before after : Store}
    {lexical current : PairedFrame} {state : MetadataState} {spent : Nat} {checkpoint : Core.State}
    (reference : environment[referenceIndex]? = some (.cellRef layout.type location))
    (caller : CellState inputs layout location current before)
    (entry : Entry inputs origin lexical current state)
    (bodyEvaluation : Evaluates
      (.unit :: encode layout current :: argument :: encode layout lexical :: environment)
      (before.set location (encode layout (selectedFrame origin lexical current)))
      (((body.weakenAt 1).weakenAt 0).weakenAt 0) result after)
    (exhausted : runStateful spent (.initial
      (withFrame (.var (referenceIndex + 2))
        (lambdaFrame layout origin (.var 1) (.loadCell (.var (referenceIndex + 2)))) (body.weakenAt 1))
      (argument :: encode layout lexical :: environment) before) = .outOfFuel checkpoint) :
    ∃ remaining, ∀ additional, remaining ≤ additional →
      runStateful additional checkpoint = .done result (after.set location (encode layout current)) := by
  have evaluated := (lambda_body_evaluates reference caller entry bodyEvaluation).2.1
  obtain ⟨required, sufficient⟩ := evaluation_runStateful_complete_with_sufficient_fuel evaluated
  exact ⟨required, fun additional enough => by
    rw [runStateful_resume exhausted additional]
    exact sufficient _ (by omega)⟩

end Solcore.SourceSemantics.CoreLowering.CallablePairedProtocol


