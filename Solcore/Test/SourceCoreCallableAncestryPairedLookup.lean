import Solcore.SourceSemantics.CoreLowering.CallableAncestryPairedValidation

#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! Lookup consumers over actual successful preparation, including arbitrary
finite lambda repetition and paired caller/lexical derivations. This tests a
pure metadata domain; native execution history is not a premise hidden here. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallableAncestryPairedLookup
open Solcore Solcore.Frontend
open Solcore.SourceSemantics.CoreLowering
open CallableAncestryPairedLookup CallableAncestryPairedValidation
abbrev State := SourceCoreCallableAncestryReadRecipes.State

example {checked : Checked} {base : Base checked}
    (prepared : SourceCoreCallableAncestryPairedPreparation.Prepared base) (frame : Frame) (state : Option State) :
    prepared.table.lookup? frame = some state ↔ Authenticates prepared.inputs frame state := prepared_lookup_iff prepared

example {checked : Checked} {base : Base checked} (inputs : Inputs base) (table : Table)
    (validated : SourceCoreCallableAncestryPairedPreparation.valid inputs table = true) :
    Sound inputs table ∧ Closed inputs table := ⟨valid_sound inputs validated, valid_closed inputs validated⟩

private def repeated (id : Core.Word) : Nat → Frame → Frame
  | 0, parent => parent
  | count + 1, parent => .lambda id (repeated id count parent)

private theorem repeated_authenticates {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {frame : Frame} {state : State} {id : Core.Word} (ancestry : Authenticates inputs frame (some state))
    (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed inputs state id = true) (count : Nat) :
    Authenticates inputs (repeated id count frame) (some state) := by
  induction count with
  | zero => exact ancestry
  | succ count ih => exact .lambda ih allowed

example {checked : Checked} {base : Base checked}
    (prepared : SourceCoreCallableAncestryPairedPreparation.Prepared base)
    {frame : Frame} {state : State} {id : Core.Word} (ancestry : Authenticates prepared.inputs frame (some state))
    (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed prepared.inputs state id = true) (count : Nat) :
    prepared.table.lookup? (repeated id count frame) = some (some state) :=
  (prepared_lookup_iff prepared).mpr (repeated_authenticates ancestry allowed count)

example {checked : Checked} {base : Base checked}
    (prepared : SourceCoreCallableAncestryPairedPreparation.Prepared base)
    {callerFrame lexicalFrame : Frame} {caller lexical result : State} {id target : Core.Word}
    (callerAuth : Authenticates prepared.inputs callerFrame (some caller))
    (lexicalAuth : Authenticates prepared.inputs lexicalFrame (some lexical))
    (selected : SourceCoreCallableAncestryPairedPreparation.view? prepared.inputs caller lexical id target = some result) :
    prepared.table.lookup? (.appliedView id target callerFrame lexicalFrame) = some (some result) :=
  (prepared_lookup_iff prepared).mpr (.appliedView callerAuth lexicalAuth selected)

example (table : Table) (id target : Core.Word) (caller : Frame) :
    table.lookup? (.view id target caller) = none := rfl

example {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {caller lexical result : State} {id target : Core.Word}
    (accepted : SourceCoreCallableAncestryPairedPreparation.view? inputs caller lexical id target = some result) :
    ∃ (read : SourceCoreCallableAncestryReadRecipes.Read inputs caller id target)
      (applied : SourceCoreCallableAncestryReadRecipes.Applied read lexical),
      SourceCoreCallableAncestryReadRecipes.prepareRead inputs caller id target = .ok read ∧
      SourceCoreCallableAncestryReadRecipes.applyRead read lexical = .ok applied ∧ result = read.after lexical :=
  view_receipts accepted

end Tests.SourceCoreCallableAncestryPairedLookup
