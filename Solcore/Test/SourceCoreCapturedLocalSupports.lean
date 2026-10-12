import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.Test.SourceCoreCapturedLocalBodyReceipt
import Solcore.Test.SourceCoreCapturedLocalClosureFamily
import Solcore.Test.SourceCoreCapturedLocalSyntax
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedLexicalCollectors
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedLexicalLambdaFormation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedLexicalReadRoots
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodiesSupport

/-! The actual singleton inventory packages full lexical named-body coverage
and every retained captured-read closure body for the same public model. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedLocal
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Issued Inventory headers)
open CallableIndexedOwnedPreparedStagedNamedBodies (Body)
open CallableIndexedOwnedPreparedStagedNamedBodiesSupport (Support)

/-- Every child is built at the context and scope reached by the actual
accepted lexical lowering. The two finite syntax cases supply compiler facts,
not an assumed body execution law. -/
theorem ActualHeader.lexical_support {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed) (actual : ActualHeader fixture observed.row)
    (receipt : CallableIndexedOwnedPreparedStagedNamedLexicalReceipts.Receipt actual.header)
    {registry : SourceCoreRawMetadata.Registry}
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics) :
    Nonempty (CallableIndexedOwnedPreparedStagedNamedLexicalSupport.Support
      [actual.header] (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
      registry actual.header stages.registry receipt
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) := by
  apply Nonempty.intro
  apply CallableIndexedOwnedPreparedNamedLexicalCollectors.of_compiler actual.prepared actual.aligned
    fixture.recipePrepared fixture.source_wellFormed (actual.complete stages)
    (bootstrap_zero fixture.recipe.compiled) observed.entryMember receipt stages.registry actual.lexical_syntax
  intro child selected context fields scope fuel id node lowered declarations approved found typed accepted nativeType native
  obtain initial | lambda := approved
  · subst id
    have same : node = observed.shape.initialRead :=
      Option.some.inj (found.symm.trans (by rw [actual.source]; exact observed.shape.initialReadFound))
    subst node
    obtain ⟨root⟩ := CallableIndexedOwnedPreparedStagedNamedLexicalReadRoots.of_accepted
      actual.prepared actual.aligned actual.diagnostic receiver fixture.source_wellFormed
      (by rw [actual.source]; exact observed.metadata actual.prepared.named)
      (stages.registry.source selected) (stages.registry.evidence selected) fields
      (by rw [stages.registry.source selected]; exact declarations)
      (by rw [stages.registry.source selected]; exact found) observed.shape.initialReadForm
      (by rw [stages.registry.source selected]; exact typed)
      (by rw [stages.registry.source selected]; exact accepted)
    exact .recursive root
  · subst id
    have same : node = observed.expression :=
      Option.some.inj (found.symm.trans (by rw [actual.source]; exact observed.foundExpression))
    subst node
    obtain ⟨formation⟩ := CallableIndexedOwnedPreparedNamedLexicalLambdaFormation.of_expression
      actual.prepared actual.aligned actual.diagnostic fixture.source_wellFormed observed.profile selected
      found observed.lambda (by rw [actual.source]; exact observed.owned)
      observed.requirements observed.coercions (by simp only [observed.noLocals, List.find?_nil])
      (by rw [actual.source]; exact observed.read)
      (by rw [actual.source]; exact observed.foundInnerReturn) observed.innerReturnForm observed.innerReturnType
      fields declarations typed accepted native
    obtain ⟨_, certificate⟩ := RecursiveNamedHeaderSourceTyping.certificate actual.header fixture.source_wellFormed
    have original : Dynamic.SourceRuntimeValid (Program.ofChecked fixture.recipe.compiled.sourceProgram)
        actual.header.function.context actual.header.function.source := by
      rw [actual.header.frame.context, actual.header.frame.source]
      exact certificate.toBodyInstanceTypingCertificate.sourceRuntimeValid
    exact .formation formation
      (by rw [stages.registry.source selected]
          exact (original.transport (RecursiveNamedInitialContextValidity.mono_fields actual.header.extended)).transport fields)
      (by rw [stages.registry.evidence selected]
          exact fields.covers (RecursiveNamedInitialContextValidity.covers actual.header.frame actual.header.extended))


structure StaticSupportPackage (fixture : CompiledFixture) (observed : ObservedFactory fixture)
    (registry : SourceCoreRawMetadata.Registry)
    (completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed) where
  input : Input fixture.recipe.compiled
  packet : Issued input
  actual : ActualHeader fixture observed.row
  headerEq : actual.header = packet.header
  rows : Inventory [input]
  rowsEq : rows = .cons packet .nil
  complete : RecursiveNamedCatalogNativeContexts.Complete
    (values := .initial fixture.recipe.compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed) (headers rows)
  terminals : ∀ header, header ∈ headers rows → Body header
  supports : ∀ header (member : header ∈ headers rows),
    Support (headers rows) (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
      registry header (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture))
      (terminals header member) (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
  family : ∀ {mapping world function native bindings parameter result}
    (association : CallableIndexedOwnedContextualTypedClosureReceipts.Association (headers rows)
      (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled) registry
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
      mapping world function native bindings parameter result),
    CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.OrdinarySequenceFor (actualStagePrepared fixture) association
  descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named actual.header.named.signature.key)

 theorem StaticSupportPackage.header_list {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {registry : SourceCoreRawMetadata.Registry}
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (support : StaticSupportPackage fixture observed registry completion) : headers support.rows = [support.actual.header] := by
  rw [support.rowsEq, support.headerEq]
  rfl

theorem static_supports (fixture : CompiledFixture) (observed : ObservedFactory fixture)
    (stages : ObservedStages fixture observed) (registry : SourceCoreRawMetadata.Registry)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics) :
    Nonempty (StaticSupportPackage fixture observed registry completion) := by
  obtain ⟨input, _row, packet, actual, sameHeader⟩ := stages.inventory
  let rows : Inventory [input] := .cons packet .nil
  have headerList : headers rows = [actual.header] := by
    simp only [rows, headers, sameHeader]
  obtain ⟨receipt⟩ := actual.lexical_receipt
  let body := actual.lexical_body receipt
  obtain ⟨support⟩ := actual.lexical_support stages receipt (registry := registry) receiver
  let terminals : ∀ header, header ∈ headers rows → Body header := fun header member => by
    have same : header = actual.header := by simpa only [headerList, List.mem_singleton] using member
    exact same ▸ body
  have supports : ∀ header (member : header ∈ headers rows),
      Support (headers rows) (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
        registry header (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture))
        (terminals header member) (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics) := by
    intro header member
    have same : header = actual.header := by simpa only [headerList, List.mem_singleton] using member
    subst header
    simpa only [headerList, terminals, body, ActualHeader.lexical_body,
      CallableIndexedOwnedPreparedStagedNamedBodiesSupport.Support, ObservedStages.registry,
      actualStagePrepared] using support
  exact ⟨{
    input := input, packet := packet, actual := actual, headerEq := sameHeader, rows := rows, rowsEq := rfl
    complete := by rw [headerList]; exact actual.complete stages
    terminals := terminals, supports := supports
    family := fun association => actual.closure_family stages receiver association
    descriptor := actual.descriptor stages }⟩

end Tests.SourceCoreCapturedLocal
