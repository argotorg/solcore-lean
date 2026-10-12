import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.Test.SourceCoreInitialLexicalFailureFacts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedLexicalCollectors
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedLexicalReadRoots
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreInitialLexicalFailure
open Solcore Frontend SourceInference SourceSemantics CoreLowering

theorem ActualHeader.failed_statements {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.failedRow.row) : actual.header.function.body = [observed.failedShape.declared.id, observed.failedShape.statement.id] := by
  rw [actual.aligned.function]
  change actual.prepared.compilation.statements = _
  have accepted := actual.prepared.compilation.roots
  change (actual.prepared.named.specialized.function.typedBody.roots.mapM _) = _ at accepted
  rw [actual.prepared.same, observed.failedShape.roots] at accepted
  exact (Except.ok.inj accepted).symm

theorem ActualHeader.failed_lexical_receipt {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.failedRow.row) :
    Nonempty (CallableIndexedOwnedPreparedStagedNamedLexicalReceipts.Receipt actual.header) := by
  apply CallableIndexedOwnedPreparedStagedNamedLexicalReceipts.of_accepted actual.aligned.accepted _ actual.aligned.projection
  rw [actual.source, actual.failed_statements]
  exact .absent observed.failedShape.declaredFound observed.failedShape.declaredForm
    (.returnValue [] observed.failedShape.statementFound observed.failedShape.statementForm)

theorem ActualHeader.identity_statements {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.identityRow.row) : actual.header.function.body = [observed.identityShape.statement.id] := by
  rw [actual.aligned.function]
  change actual.prepared.compilation.statements = _
  have accepted := actual.prepared.compilation.roots
  change (actual.prepared.named.specialized.function.typedBody.roots.mapM _) = _ at accepted
  rw [actual.prepared.same, observed.identityShape.roots] at accepted
  exact (Except.ok.inj accepted).symm

theorem ActualHeader.identity_lexical_receipt {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.identityRow.row) :
    Nonempty (CallableIndexedOwnedPreparedStagedNamedLexicalReceipts.Receipt actual.header) := by
  apply CallableIndexedOwnedPreparedStagedNamedLexicalReceipts.of_accepted actual.aligned.accepted _ actual.aligned.projection
  rw [actual.source, actual.identity_statements]
  exact .returnValue [] observed.identityShape.statementFound observed.identityShape.statementForm

def ActualHeader.lexical_body {fixture : CompiledFixture} {row : SourceSpecialization.SpecializedFunction}
    (actual : ActualHeader fixture row)
    (receipt : CallableIndexedOwnedPreparedStagedNamedLexicalReceipts.Receipt actual.header) :
    CallableIndexedOwnedPreparedStagedNamedBodies.Body actual.header := {
  row := row, prepared := actual.prepared, instantiation := CallableNamedMetadata.instantiation row
  aligned := actual.aligned, layouts := actual.aligned.layouts, compilation := .lexical receipt }

theorem ObservedProgram.failed_local_declaration {fixture : CompiledFixture} (observed : ObservedProgram fixture) :
    SourceCoreDataPlaces.rootBinder observed.failedRow.row.function.typedBody observed.failedShape.binder.id =
      .ok observed.failedShape.binder := by
  simp [SourceCoreDataPlaces.rootBinder, SourceCoreDataPlaces.declaredBinders, observed.failedShape.inputs,
    observed.failedShape.nodes, observed.failedShape.declaredForm, observed.failedShape.readForm,
    observed.failedShape.statementForm, observed.failedShape.binderOwner, observed.failedShape.binderScheme,
    TypeSystem.Scheme.mono, observed.failedShape.binderRequirements]

theorem ActualHeader.failed_syntax {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.failedRow.row) :
    GenericLexicalStatements.Syntax actual.header.function.source (fun id => id = observed.failedShape.read.id)
      actual.header.context true actual.header.function.body actual.header.function.resultType := by
  obtain ⟨facts, final, typed, _roots, _complete⟩ := actual.aligned.bodyTyped
  have source := actual.source
  rw [source, observed.failedShape.roots] at typed
  simp only [List.filterMap_cons, List.filterMap_nil] at typed
  rw [source, actual.failed_statements]
  have unique : NodeOccurrencesUnique observed.failedRow.row.function.typedBody := source ▸ actual.header.unique
  cases typed with
  | cons head tail =>
    cases tail with
    | singleton last =>
      cases head with
      | letUninitialized contains form mono generalized extended type =>
        have same := Option.some.inj ((lookupStatement?_complete unique contains).symm.trans observed.failedShape.declaredFound)
        cases same
        rw [observed.failedShape.declaredForm] at form
        cases (StatementForm.letDecl.inj form).1
        apply GenericLexicalStatements.Syntax.uninitialized observed.failedShape.declaredFound observed.failedShape.declaredForm
          observed.failed_local_declaration mono extended (by rw [observed.failedShape.inputs]; rfl)
        cases last with
        | returnValue contains form expression type =>
          have same := Option.some.inj ((lookupStatement?_complete unique contains).symm.trans observed.failedShape.statementFound)
          cases same
          rw [observed.failedShape.statementForm] at form
          cases Option.some.inj (StatementForm.returnStmt.inj form)
          exact .returnValue [] observed.failedShape.statementFound observed.failedShape.statementForm type
            observed.failedShape.readFound (observed.failedShape.readType.trans actual.failed_result_type.symm)
            (by simpa only [observed.failedShape.readType, actual.failed_result_type] using expression) rfl
        | _ =>
          have same := Option.some.inj ((lookupStatement?_complete unique (by assumption)).symm.trans observed.failedShape.statementFound)
          cases same
          simp_all [observed.failedShape.statementForm]
      | _ =>
        have same := Option.some.inj ((lookupStatement?_complete unique (by assumption)).symm.trans observed.failedShape.declaredFound)
        cases same
        simp_all [observed.failedShape.declaredForm]

theorem ActualHeader.identity_syntax {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.identityRow.row) :
    GenericLexicalStatements.Syntax actual.header.function.source (fun id => id = observed.identityShape.read.id)
      actual.header.context true actual.header.function.body actual.header.function.resultType := by
  obtain ⟨facts, final, typed, _roots, _complete⟩ := actual.aligned.bodyTyped
  have source := actual.source
  rw [source, observed.identityShape.roots] at typed
  simp only [List.filterMap_cons, List.filterMap_nil] at typed
  rw [source, actual.identity_statements]
  have unique : NodeOccurrencesUnique observed.identityRow.row.function.typedBody := source ▸ actual.header.unique
  cases typed with
  | singleton last =>
    cases last with
    | returnValue contains form expression type =>
      have same := Option.some.inj ((lookupStatement?_complete unique contains).symm.trans observed.identityShape.statementFound)
      cases same
      rw [observed.identityShape.statementForm] at form
      cases Option.some.inj (StatementForm.returnStmt.inj form)
      exact .returnValue [] observed.identityShape.statementFound observed.identityShape.statementForm type
        observed.identityShape.readFound (observed.identityShape.readType.trans actual.identity_result_type.symm)
        (by simpa only [observed.identityShape.readType, actual.identity_result_type] using expression) rfl
    | _ =>
      have same := Option.some.inj ((lookupStatement?_complete unique (by assumption)).symm.trans observed.identityShape.statementFound)
      cases same
      simp_all [observed.identityShape.statementForm]

theorem ActualHeader.failed_support {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.failedRow.row)
    (receipt : CallableIndexedOwnedPreparedStagedNamedLexicalReceipts.Receipt actual.header)
    (headers : List (CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)))
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed) headers)
    {registry : SourceCoreRawMetadata.Registry}
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics) :
    Nonempty (CallableIndexedOwnedPreparedStagedNamedLexicalSupport.Support headers
      (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
      registry actual.header (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)) receipt
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) := by
  apply Nonempty.intro
  apply CallableIndexedOwnedPreparedNamedLexicalCollectors.of_compiler actual.prepared actual.aligned
    fixture.recipePrepared fixture.source_wellFormed complete (bootstrap_zero fixture.recipe.compiled)
    observed.failedRow.entryMember receipt _ actual.failed_syntax
  intro child selected context fields scope fuel id node lowered declarations approved found typed accepted nativeType _native
  subst id
  have same : node = observed.failedShape.read :=
    Option.some.inj (found.symm.trans (by rw [actual.source]; exact observed.failedShape.readFound))
  subst node
  obtain ⟨root⟩ := CallableIndexedOwnedPreparedStagedNamedLexicalReadRoots.of_accepted
    actual.prepared actual.aligned actual.diagnostic receiver fixture.source_wellFormed
    (by rw [actual.source]; exact observed.failed_metadata actual.prepared.named)
    ((RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)).source selected)
    ((RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)).evidence selected) fields
    (by rw [(RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)).source selected]; exact declarations)
    (by rw [(RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)).source selected]; exact found)
    observed.failedShape.readForm
    (by rw [(RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)).source selected]; exact typed)
    (by rw [(RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)).source selected]; exact accepted)
  exact .recursive root

theorem ActualHeader.identity_support {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.identityRow.row)
    (receipt : CallableIndexedOwnedPreparedStagedNamedLexicalReceipts.Receipt actual.header)
    (headers : List (CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)))
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed) headers)
    {registry : SourceCoreRawMetadata.Registry}
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics) :
    Nonempty (CallableIndexedOwnedPreparedStagedNamedLexicalSupport.Support headers
      (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
      registry actual.header (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)) receipt
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) := by
  apply Nonempty.intro
  apply CallableIndexedOwnedPreparedNamedLexicalCollectors.of_compiler actual.prepared actual.aligned
    fixture.recipePrepared fixture.source_wellFormed complete (bootstrap_zero fixture.recipe.compiled)
    observed.identityRow.entryMember receipt _ actual.identity_syntax
  intro child selected context fields scope fuel id node lowered declarations approved found typed accepted nativeType _native
  subst id
  have same : node = observed.identityShape.read :=
    Option.some.inj (found.symm.trans (by rw [actual.source]; exact observed.identityShape.readFound))
  subst node
  obtain ⟨root⟩ := CallableIndexedOwnedPreparedStagedNamedLexicalReadRoots.of_accepted
    actual.prepared actual.aligned actual.diagnostic receiver fixture.source_wellFormed
    (by rw [actual.source]; exact observed.identity_metadata actual.prepared.named)
    ((RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)).source selected)
    ((RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)).evidence selected) fields
    (by rw [(RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)).source selected]; exact declarations)
    (by rw [(RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)).source selected]; exact found)
    observed.identityShape.readForm
    (by rw [(RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)).source selected]; exact typed)
    (by rw [(RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)).source selected]; exact accepted)
  exact .recursive root

end Tests.SourceCoreInitialLexicalFailure
