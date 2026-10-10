import Solcore.SourceSemantics.CoreLowering.RecursiveNamedHeaderParameterProjections
import Solcore.SourceSemantics.CoreLowering.CallableIndexedActualNamedSourceReceipts
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedSelectedExpressionFactory

/-! Actual selected Headers supply the raw Source parameter/result vectors and
native projections at each receiving Source context. Dictionaries stay intact;
neither ordinary evidence nor a completed expression Tree is required.
Coercions, generalized local branches, syntax and compiler policy coverage are
separate occurrence-specific obligations. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedSourceFactoryFacts
open Core Frontend SourceInference RecursiveNamedCatalog

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : Inventory compiled.indexed.ancestry (.initial compiled.compatible.checked)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions
    (Program.ofChecked compiled.sourceProgram)}
  {sourceContext : SourceSemantics.Context}

/-- The same actual source frame fixes ordered raw types. Accepted named
preparation supplies native projections, including for Headers with evidence. -/
theorem source_types
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (signatures : sourceContext.signatures = compiled.sourceProgram.signatures) :
    RecursiveNamedCallEvidenceHeads.SourceTypes headers sourceContext := by
  refine ⟨?_, ?_, ?_⟩
  · intro header _member signature member selected
    have actualMember : signature ∈ (Program.ofChecked compiled.sourceProgram).signatures.functions := by
      change signature ∈ compiled.sourceProgram.signatures.functions
      rw [← signatures]
      exact member
    exact (RecursiveNamedSourceSignatureFacts.header_shape header wellFormed actualMember selected).1
  · intro header _member signature member selected
    have actualMember : signature ∈ (Program.ofChecked compiled.sourceProgram).signatures.functions := by
      change signature ∈ compiled.sourceProgram.signatures.functions
      rw [← signatures]
      exact member
    exact (RecursiveNamedSourceSignatureFacts.header_shape header wellFormed actualMember selected).2
  · intro header _member
    exact RecursiveNamedHeaderParameterProjections.projections_of_record header rfl wellFormed
      (CallableIndexedActualNamedSourceReceipts.header_record compiled header)

/-- A selected declaration uses its actual full Header and Source signature
catalog. No assumption about other Headers' dictionaries is introduced. -/
theorem selected_validity
    (signatures : sourceContext.signatures = compiled.sourceProgram.signatures)
    (compilation : SourceCoreFunctions.Context) (source : TypedSource)
    (admitted : ExpressionId → Prop) :
    RecursiveNamedExpressionCompilerCertificates.SelectedDeclarationLaw headers compilation
      source sourceContext admitted :=
  RecursiveNamedSelectedExpressionFactory.selected_validity signatures

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedSourceFactoryFacts
