import Solcore.Test.SourceCoreCapturedCopyMetadata
import Solcore.Test.SourceCoreCapturedCopySyntax
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedLexicalLambdaReadRoots
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds

/-! Every authentic returned closure of this compiled program receives the
actual lexical body certificate. Its initializer reads the captured seed, then
the returned expression reads the newly allocated local cell. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedCopy
open Solcore Frontend SourceInference SourceSemantics CoreLowering

theorem actualStagePrepared (fixture : CompiledFixture) :
    RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable :=
  RecursiveNamedPreparedStageContracts.of_compiled fixture.recipe.compiled
    fixture.recipe.compiled.indexed.ancestry.graph.inputs.callableSelected

def ActualHeader.closure_family {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed) (actual : ActualHeader fixture observed.row)
    {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))}
    {keys : List (CallableIndexedOwnedFunctionValues.Key fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))}
    {registry : SourceCoreRawMetadata.Registry}
    {completion : SourceCoreCallableIndexedPrograms.Completion fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    {mapping world function native bindings parameter result}
    (association : CallableIndexedOwnedContextualTypedClosureReceipts.Association headers keys registry
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
      mapping world function native bindings parameter result) :
    CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.OrdinarySequenceFor
      (actualStagePrepared fixture) association := by
  cases association with
  | ordinary owner captured code history support origin prefixContext globals referenceIndex typed provenance =>
    apply CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.OrdinarySequenceFor.compiled
    have sameSource := support.source.trans (stages.source_of_cached actual support.caller.selected)
    have found := code.sourceFound
    rw [sameSource] at found
    have shape := observed.lambda_shape found code.sourceForm
    have bodyShape := shape.2.2
    have resultShape := shape.2.1
    have treeShape : CallableIndexedOwnedPreparedStagedLexicalTree.Shape function.source function.body := by
      rw [sameSource, bodyShape]
      exact .initialized observed.shape.initializedFound observed.shape.initializedForm
        (.returnValue [] observed.foundInnerReturn observed.innerReturnForm)
    obtain ⟨finalContext, bodyFacts, typed, _complete⟩ :=
      CallableIndexedOwnedLambdaSourceAdmission.body_typed_at_parameters support.body.frame support.body.extended
    have syntaxTree : GenericLexicalStatements.Syntax function.source
        (CallableIndexedOwnedPreparedStagedLexicalLambdaReadRoots.Read function.source)
        support.body.context true function.body function.resultType := by
      rw [sameSource, bodyShape, resultShape] at typed ⊢
      apply observed.body_syntax (by rw [← sameSource]; exact support.unique) ?_ ?_ typed
      · exact ⟨observed.shape.initialRead, _, _, observed.shape.initialReadFound, observed.shape.initialReadForm⟩
      · exact ⟨observed.bodyRead, _, _, observed.foundRead, observed.readForm⟩
    obtain ⟨sidecar, _issued, selected⟩ :=
      CallableIndexedOwnedPreparedDirectStageScopeReceipts.code_scope code support.source_receipt support.unique
    exact CallableIndexedOwnedPreparedStagedLexicalLambdaReadRoots.of_reads code support provenance
      receiver fixture.source_wellFormed (by rw [sameSource]; exact observed.metadata support.caller.named)
      treeShape syntaxTree (RecursiveStageRegistry.scope sidecar code.active function)
      (RecursiveNamedPreparedStageScopes.anonymous_preserved (actualStagePrepared fixture) selected)

  | principal owner captured code history support origin globals leading referenceIndex typed provenance =>
    exact False.elim (fixture.no_principal support.principal)

end Tests.SourceCoreCapturedCopy
