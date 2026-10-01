import Solcore.SourceSemantics.CoreLowering.CallableIndexedProtocol

/-! Indexed protocol receipts retain two independent parents and authenticate
only transitions derived from the actual owned graph. No raw table index is
promoted into a runtime-history claim. -/
set_option autoImplicit false
namespace Solcore.Test.SourceCoreCallableIndexedHistory
open Core Frontend SourceSemantics.CoreLowering
open CallableAncestryPairedLookup CallableIndexedHistory CallableIndexedProtocol
open SourceCoreCallableIndexedFrames SourceCoreCallableIndexedDispatch

/-- A negative native integer is not a state-table location, even though the
ordinary Core carrier remains well typed. -/
example (table : SourceCoreCallableIndexedDispatch.Table) (negative : Nat) :
    SourceCoreCallableIndexedDispatch.lookup? table (.state (.negSucc negative)) = none := rfl

example {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {table : CallableAncestryPairedLookup.Table} {ghost : GhostFrame} {metadata : Option MetadataState} :
    ¬ Carries inputs table .invalid ghost metadata := by intro carried; exact carried.not_invalid rfl

example {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {table : CallableAncestryPairedLookup.Table} {ghost : GhostFrame} {metadata : Option MetadataState}
    (negative : Nat) : ¬ Carries inputs table (.state (.negSucc negative)) ghost metadata := by
  intro carried; cases carried

/-- A saved stable caller survives a read as its own independent ghost parent. -/
example {checked : Checked} {base : Base checked}
    (graph : SourceCoreCallableAncestryPairedPreparation.Prepared base)
    {native : NativeFrame} {caller : GhostFrame} {metadata : MetadataState} {id target : Word}
    (carried : Carries graph.inputs graph.table native caller (some metadata))
    (read : SourceCoreCallableAncestryReadRecipes.Read graph.inputs metadata id target)
    (prepared : SourceCoreCallableAncestryReadRecipes.prepareRead graph.inputs metadata id target = .ok read) :
    Current graph.inputs graph.table (readFrame id target native) (.view id target caller) :=
  read_history carried read prepared

/-- No successful native transition or lookup is an additional premise here:
real caller/lexical recipe acceptance supplies the cached destination. -/
example {checked : Checked} {base : Base checked}
    (graph : SourceCoreCallableAncestryPairedPreparation.Prepared base)
    {callerIndex lexicalIndex : Nat} {callerGhost lexicalGhost : GhostFrame}
    {caller lexical : MetadataState} {id target : Word}
    (callerCarried : Carries graph.inputs graph.table (.state (Int.ofNat callerIndex)) callerGhost (some caller))
    (lexicalCarried : Carries graph.inputs graph.table (.state (Int.ofNat lexicalIndex)) lexicalGhost (some lexical))
    (read : SourceCoreCallableAncestryReadRecipes.Read graph.inputs caller id target)
    (prepared : SourceCoreCallableAncestryReadRecipes.prepareRead graph.inputs caller id target = .ok read)
    (applied : SourceCoreCallableAncestryReadRecipes.Applied read lexical)
    (appliedPrepared : SourceCoreCallableAncestryReadRecipes.applyRead read lexical = .ok applied) :
    Carries graph.inputs graph.table
      (selectedFrame graph.table target (.state (Int.ofNat lexicalIndex)) (.view id target (Int.ofNat callerIndex)))
      (.appliedView id target callerGhost lexicalGhost) (some (read.after lexical)) :=
  applied_complete graph callerCarried lexicalCarried read prepared applied appliedPrepared

/-- Actual reference-slot loading leaves the native store unchanged while
selecting from both parents. A closure-producing expression is never weakened. -/
example {checked : Checked} {base : Base checked}
    (graph : SourceCoreCallableAncestryPairedPreparation.Prepared base)
    {layout : Layout} {position : Nat} {currentNative : NativeFrame} {lexicalGhost currentGhost : GhostFrame}
    {metadata : MetadataState} {origin : Word}
    (carried : Carries graph.inputs graph.table (.state (Int.ofNat position)) lexicalGhost (some metadata))
    (current : Current graph.inputs graph.table currentNative currentGhost)
    (valid : selectedFrame graph.table origin (.state (Int.ofNat position)) currentNative ≠ .invalid) :
    ∃ resultState,
      Evaluates [encode layout (.state (Int.ofNat position)), .cellRef layout.type 0] [encode layout currentNative]
        (lambdaFrame graph.table layout origin (.var 0) (.loadCell (.var 1)))
        (encode layout (selectedFrame graph.table origin (.state (Int.ofNat position)) currentNative)) [encode layout currentNative] ∧
      Carries graph.inputs graph.table (selectedFrame graph.table origin (.state (Int.ofNat position)) currentNative)
        (SourceCoreCallablePairedFrames.selectedFrame origin lexicalGhost currentGhost) (some resultState) :=
  dispatch_load graph (.var rfl) rfl carried ⟨rfl, current⟩ valid

/-- Closure of the prepared cache also covers ordinary entry from an unrelated
stable caller without changing the lexical metadata state. -/
example {checked : Checked} {base : Base checked}
    (graph : SourceCoreCallableAncestryPairedPreparation.Prepared base)
    {native otherNative : NativeFrame} {lexical other : GhostFrame}
    {metadata otherMetadata : MetadataState} {origin : Word}
    (lexicalCarried : Carries graph.inputs graph.table native lexical (some metadata))
    (otherCarried : Carries graph.inputs graph.table otherNative other (some otherMetadata))
    (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed graph.inputs metadata origin = true) :
    Carries graph.inputs graph.table (selectedFrame graph.table origin native otherNative)
      (.lambda origin lexical) (some metadata) := ordinary_complete graph lexicalCarried otherCarried allowed

/-- Reflection consumes an actual completed state carrier, without assuming
that the dispatch validity check passed in advance. -/
example {checked : Checked} {base : Base checked}
    (graph : SourceCoreCallableAncestryPairedPreparation.Prepared base)
    {layout : Layout} {position : Nat} {resultIndex : Int} {currentNative : NativeFrame}
    {lexicalGhost currentGhost : GhostFrame} {metadata : MetadataState} {origin : Word} {after : Store}
    (carried : Carries graph.inputs graph.table (.state (Int.ofNat position)) lexicalGhost (some metadata))
    (current : Current graph.inputs graph.table currentNative currentGhost)
    (evaluated : Evaluates [encode layout (.state (Int.ofNat position)), .cellRef layout.type 0] [encode layout currentNative]
      (lambdaFrame graph.table layout origin (.var 0) (.loadCell (.var 1))) (encode layout (.state resultIndex)) after) :
    after = [encode layout currentNative] ∧ ∃ resultState, Carries graph.inputs graph.table (.state resultIndex)
      (SourceCoreCallablePairedFrames.selectedFrame origin lexicalGhost currentGhost) (some resultState) :=
  dispatch_load_reflects_state graph (.var rfl) rfl carried ⟨rfl, current⟩ evaluated

end Solcore.Test.SourceCoreCallableIndexedHistory
