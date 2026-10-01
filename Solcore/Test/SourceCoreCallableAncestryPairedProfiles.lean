import Solcore.SourceSemantics.CoreLowering.CallableAncestryPairedProfiles

#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! Theorems over actual named/read/application metadata receipts. There are
no runtime traces, supplied child evaluations, or bounds on frame depth. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallableAncestryPairedProfiles
open Solcore Solcore.Frontend SourceInference TypeSystem
open Solcore.SourceSemantics.CoreLowering
open CallableAncestryMetadata CallableAncestryPairedProfiles

section
variable {checked : Checked} {base : Base checked} (inputs : Inputs base)
  (roots : List PairedState)
  (selected : ∀ root ∈ roots, ∃ id,
    SourceCoreCallableAncestryPreparation.named? inputs id = some root.metadata ∧ root.nativeActive = [])

example : RootsCoherent roots := seeded_coherent (roots_seeded inputs roots selected)

example {root : PairedState} (member : root ∈ roots) : Valid inputs roots root :=
  seeded_valid inputs (roots_seeded inputs roots selected) member

example {left right : PairedState} (leftValid : Valid inputs roots left) (rightValid : Valid inputs roots right)
    (same : key left = key right) : left = right :=
  key_injective (seeded_coherent (roots_seeded inputs roots selected)) leftValid rightValid same

example {caller lexical : PairedState} {id target : Core.Word}
    (read : SourceCoreCallableAncestryReadRecipes.Read inputs caller id target)
    (applied : SourceCoreCallableAncestryReadRecipes.Applied read lexical)
    (callerValid : Valid inputs roots caller) (lexicalValid : Valid inputs roots lexical) :
    Valid inputs roots (read.after lexical) :=
  read_after_valid (seeded_coherent (roots_seeded inputs roots selected)) read applied callerValid lexicalValid

example (states : List PairedState) (unique : (states.map key).Nodup)
    (valid : ∀ state ∈ states, Valid inputs roots state) : states.length ≤ capacity inputs roots :=
  states_bounded inputs roots states unique valid

example : (keySpace inputs roots).length = capacity inputs roots := keySpace_length inputs roots

end

example {checked : Checked} {base : Base checked} (inputs : Inputs base)
    (initial : SourceCoreCallableAncestryPairedCache.Table) (states : List PairedState)
    (unique : (states.map key).Nodup) (valid : ∀ state ∈ states, Valid inputs initial.states state) :
    states.length ≤ SourceCoreCallableAncestryPairedPreparation.capacity inputs initial :=
  prepared_capacity_bound inputs initial states unique valid

/-- Equal retained source metadata does not identify different native code
contexts. This dimension is essential for the paired protocol. -/
example (state : PairedState) (first second : Substitution) (different : first ≠ second) :
    key {state with nativeActive := first} ≠ key {state with nativeActive := second} := by
  intro same
  exact different (congrArg (fun value : CallableAncestryPairedProfiles.Key => value.nativeActive) same)

example (state : PairedState) (first second : Substitution) (different : first ≠ second) :
    key {state with metadata := {state.metadata with active := first}} ≠
      key {state with metadata := {state.metadata with active := second}} := by
  intro same
  exact different (congrArg (fun value : CallableAncestryPairedProfiles.Key => value.sourceActive) same)

example (contexts : List Substitution) (root : PairedState) :
    (keysFor [] contexts root).length = contexts.length *
      (CallableAncestryProfiles.alphabet root.metadata.source).length ^
        (CallableAncestryProfiles.alphabet root.metadata.source).length := by
  simpa [CallableAncestrySourceActive.capacity, CallableAncestrySourceActive.domainAlphabet,
    CallableAncestrySourceActive.alphabet] using keysFor_length [] contexts root

end Tests.SourceCoreCallableAncestryPairedProfiles
