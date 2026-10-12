import Solcore.Test.SourceCoreCapturedLocalFixture
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodies

/-! The named body receipt comes from the actual accepted full two-statement
lowering, including local initialization. It is not a terminal-only receipt. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedLocal
open Solcore Frontend SourceInference SourceSemantics CoreLowering

theorem ActualHeader.statements {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (actual : ActualHeader fixture observed.row) :
    actual.header.function.body = [observed.shape.initialized.id, observed.statement.id] := by
  rw [actual.aligned.function]
  change actual.prepared.compilation.statements = _
  have accepted := actual.prepared.compilation.roots
  change (actual.prepared.named.specialized.function.typedBody.roots.mapM _) = _ at accepted
  rw [actual.prepared.same, observed.roots] at accepted
  exact (Except.ok.inj accepted).symm

/-- The complete original body has the supported initialized-let/return shape. -/
theorem ActualHeader.lexical_shape {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (actual : ActualHeader fixture observed.row) :
    CallableIndexedOwnedPreparedStagedLexicalTree.Shape actual.header.function.source actual.header.function.body := by
  rw [actual.source, actual.statements]
  exact .initialized observed.shape.initializedFound observed.shape.initializedForm
    (.returnValue [] observed.foundStatement observed.returnStatement)

theorem ActualHeader.lexical_receipt {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (actual : ActualHeader fixture observed.row) :
    Nonempty (CallableIndexedOwnedPreparedStagedNamedLexicalReceipts.Receipt actual.header) :=
  CallableIndexedOwnedPreparedStagedNamedLexicalReceipts.of_accepted
    actual.aligned.accepted actual.lexical_shape actual.aligned.projection

/-- The lexical bundle keeps the same actual Header provenance and compiler receipt. -/
def ActualHeader.lexical_body {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (actual : ActualHeader fixture observed.row)
    (receipt : CallableIndexedOwnedPreparedStagedNamedLexicalReceipts.Receipt actual.header) :
    CallableIndexedOwnedPreparedStagedNamedBodies.Body actual.header := {
  row := observed.row
  prepared := actual.prepared
  instantiation := CallableNamedMetadata.instantiation observed.row
  aligned := actual.aligned
  layouts := actual.aligned.layouts
  compilation := .lexical receipt }

theorem ActualHeader.input_types {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (actual : ActualHeader fixture observed.row) :
    actual.header.bindings.map (fun binding => binding.1.scheme.body) = [.word] := by
  have inputs := congrArg (fun binders => binders.map (fun binder => binder.scheme.body)) actual.header.inputs
  rw [actual.source, observed.inputs] at inputs
  simpa only [List.map_map, Function.comp_def, List.map_cons, List.map_nil,
    observed.binderScheme, TypeSystem.Scheme.mono] using inputs.symm

theorem ActualHeader.result_type {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (actual : ActualHeader fixture observed.row) : actual.header.function.resultType = .function .unit .word := by
  rw [actual.header.agreement.result, actual.aligned.named, actual.prepared.same]
  exact observed.resultType

def ActualHeader.descriptor {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed) (actual : ActualHeader fixture observed.row) :
    SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named actual.header.named.signature.key) := by
  rw [actual.aligned.named, RecursiveNamedPreparedCallEvidence.Prepared.signature_key actual.prepared]
  exact stages.descriptor

end Tests.SourceCoreCapturedLocal
