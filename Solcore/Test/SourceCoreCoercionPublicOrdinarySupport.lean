import Solcore.Test.SourceCoreCoercionPublicMetadata
import Solcore.Test.SourceCoreCoercionPublicCatalog
import Solcore.Test.SourceCoreCoercionPublicCommon
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedPhysicalMixedTerminalSupport
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCoercionPublic
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)
open CallableIndexedOwnedPreparedStagedPhysicalMixedNamedTerminalSupport (Support)
open CallableIndexedOwnedPreparedStagedDirectCallCertificates (Supported)

variable {fixture : CompiledFixture}
  {inputs : List (Input fixture.recipe.compiled)} (rows : Inventory inputs)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (methods : CallableIndexedOwnedPreparedStagedClosedCoercionSelection.Catalog fixture.recipe.compiled)

local notation "actualRegistry" => RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)
local notation "faults" => CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics

include rows receiver methods in
theorem ActualHeader.use_support {signature : ProgramFunctionSignature} {type : TypeSystem.Ty}
    (row : ObservedRow fixture signature)
    (shape : UseShape row.row.function signature type)
    (nodes : row.row.function.typedBody.nodes = shape.nodeList)
    (noLocals : fixture.recipe.compiled.indexed.base.locals.bindings = [])
    (actual : ActualHeader fixture row.row) :
    ∃ terminal : Terminal actual.header,
      Nonempty (Support (headers := headers rows) (stages := actualRegistry) (semanticFaults := faults)
        actual.header terminal) := by
  obtain ⟨terminal, diagnostic, expression, point⟩ := actual.terminal shape.value.node.id
    shape.body.statement shape.body.roots shape.body.statementFound
    shape.body.statementForm
  have metadata : CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
      fixture.recipe.compiled.indexed terminal.prepared.named actual.header.function.source
      (fun _ => False) := by
    rw [actual.source]
    exact shape.policy_metadata nodes terminal.prepared.named noLocals
  obtain ⟨loaded, checked⟩ := fixture.loaded
  refine ⟨terminal, CallableIndexedOwnedPreparedStagedNamedPhysicalMixedTerminalSupport.of_actual_with_catalog
    terminal diagnostic receiver fixture.source_wellFormed (fun _ impossible => impossible.elim) metadata
    (by rw [expression, actual.source]; exact shape.syntax) rows
    (fun _ impossible => impossible.elim) checked ?_ (.generic ⟨methods.formed, methods.assumptions⟩)
    (actualStagePrepared fixture) point⟩
  rw [fixture.sameProgram]
  exact CallableCoercionSelectionIdentity.Catalog.of_checked fixture.checked

include rows receiver methods in
theorem ActualHeader.identity_support {signature : ProgramFunctionSignature} {type : TypeSystem.Ty}
    (row : ObservedRow fixture signature)
    (shape : SelectedIdentityShape row.row.function type)
    (nodes : row.row.function.typedBody.nodes = shape.nodeList)
    (noLocals : fixture.recipe.compiled.indexed.base.locals.bindings = [])
    (actual : ActualHeader fixture row.row) :
    ∃ terminal : Terminal actual.header,
      Nonempty (Support (headers := headers rows) (stages := actualRegistry) (semanticFaults := faults)
        actual.header terminal) := by
  obtain ⟨terminal, diagnostic, expression, point⟩ := actual.terminal shape.read.node.id
    shape.statement shape.roots shape.statementFound shape.statementForm
  have metadata : CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
      fixture.recipe.compiled.indexed terminal.prepared.named actual.header.function.source
      (fun _ => False) := by
    rw [actual.source]
    exact shape.metadata nodes terminal.prepared.named noLocals
  obtain ⟨loaded, checked⟩ := fixture.loaded
  refine ⟨terminal, CallableIndexedOwnedPreparedStagedNamedPhysicalMixedTerminalSupport.of_actual_with_catalog
    terminal diagnostic receiver fixture.source_wellFormed (fun _ impossible => impossible.elim) metadata
    (by rw [expression, actual.source]; exact shape.syntax) rows
    (fun _ impossible => impossible.elim) checked ?_ (.generic ⟨methods.formed, methods.assumptions⟩)
    (actualStagePrepared fixture) point⟩
  rw [fixture.sameProgram]
  exact CallableCoercionSelectionIdentity.Catalog.of_checked fixture.checked

end Tests.SourceCoreCoercionPublic
