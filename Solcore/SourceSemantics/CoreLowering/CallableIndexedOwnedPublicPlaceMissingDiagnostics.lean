import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicCatalogClosedSources
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicPreparedTokenReadyNamedExpressionBounds
import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceMissingTerminalDiagnostics
import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceConcretePreparation

/-! Genuine cached Header selection supplies its complete Source in the actual
public diagnostic inventory. The callable root-table override retains all
place reasons. Accepted catalog and place preparation then interpret the
actual unavailable mapping terminal at its own raw metadata header. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicPlaceMissingDiagnostics
open Core Frontend SourceInference CompatiblePayload CompatibleMixedRoute
open SourceCoreCompatibleDataPlaces

private theorem exact_collected {plan : SourceCompilationPlan.Plan} {key : SourceCompilationPlan.Key}
    {row : SourceSpecialization.SpecializedFunction}
    (selected : SourceCompilationPlan.exactSpecialization plan key = .ok row) :
    (key, row.function.typedBody) ∈ plan.specializations.map (fun specialized =>
      (specialized.key, specialized.function.typedBody)) := by
  unfold SourceCompilationPlan.exactSpecialization at selected
  split at selected
  · cases selected
  · next actual found =>
    cases selected
    have member : row ∈ plan.specializations.filter (fun specialized => decide (specialized.key = key)) := by
      rw [found]; exact List.mem_singleton_self _
    have keyEq := of_decide_eq_true (List.mem_filter.mp member).2
    exact List.mem_map.mpr ⟨row, (List.mem_filter.mp member).1, by rw [keyEq]⟩
  · cases selected

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))

/-- Exact cached specialization and original named Source agreement establish
membership of the whole Header Source, including every node and header item. -/
theorem header_collected :
    (header.named.signature.key, header.function.source) ∈
      compiled.indexed.base.plan.specializations.map (fun specialized =>
        (specialized.key, specialized.function.typedBody)) := by
  rw [header.agreement.source]
  exact exact_collected (CallableIndexedActualNamedSourceReceipts.header_record compiled header)

/-- The real sealed diagnostic preparation visits this same full Header Source. -/
theorem inventory_at_header
    {diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked)}
    (found : compiled.indexed.base.diagnostics = some diagnostics) :
    ∃ root sources,
      SourceCoreCompatibleDataPlaceFaultSites.prepare (.initial compiled.compatible.checked)
        compiled.indexed.base.plan root sources = .ok diagnostics ∧
      (header.named.signature.key, header.function.source) ∈
        compiled.indexed.base.plan.specializations.map (fun specialized =>
          (specialized.key, specialized.function.typedBody)) ++ sources := by
  obtain ⟨root, sources, accepted⟩ := CallableIndexedOwnedPublicDiagnosticReceipts.compiled_diagnostics compiled found
  exact ⟨root, sources, accepted, List.mem_append_left _ (header_collected header)⟩

/-- The existing public receipt chooses its own actual diagnostic inventory.
Only the real callable root-table replacement is present in the lowered table. -/
theorem public_inventory
    (receipt : CallableIndexedOwnedPublicPreparedTokenReadyNamedExpressionBounds.PublicReceipt header) :
    ∃ diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked),
      compiled.indexed.base.diagnostics = some diagnostics ∧
      receipt.original.prepared.diagnostics.places = diagnostics.program.places ∧
      ∃ root sources,
        SourceCoreCompatibleDataPlaceFaultSites.prepare (.initial compiled.compatible.checked)
          compiled.indexed.base.plan root sources = .ok diagnostics ∧
        (header.named.signature.key, header.function.source) ∈
          compiled.indexed.base.plan.specializations.map (fun specialized =>
            (specialized.key, specialized.function.typedBody)) ++ sources := by
  obtain ⟨diagnostics, found, lowered⟩ := receipt.diagnostic.actual
  refine ⟨diagnostics, found, ?_, inventory_at_header header found⟩
  rw [lowered]
  cases compiled.indexed.base.callableContext <;> rfl

private theorem public_placeReason
    (receipt : CallableIndexedOwnedPublicPreparedTokenReadyNamedExpressionBounds.PublicReceipt header)
    {diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked)}
    (found : compiled.indexed.base.diagnostics = some diagnostics)
    (owner : SourceSpecialization.SpecializationKey) (site : SourceCoreElaboration.ErrorSite)
    (binder : Resolved.LocalId) (valueType : Option TypeSystem.Ty) :
    receipt.original.prepared.diagnostics.placeReason owner site binder valueType =
      diagnostics.program.placeReason owner site binder valueType := by
  obtain ⟨actual, actualFound, lowered⟩ := receipt.diagnostic.actual
  have same := Option.some.inj (found.symm.trans actualFound)
  subst actual
  rw [lowered]
  cases compiled.indexed.base.callableContext <;> rfl

/-- Same public Header, diagnostic receipt and accepted compiler metadata
supply Source membership and the concrete gate internally. The original raw
projection typing and actual terminal/table are retained pointwise inputs. -/
theorem terminal_at_header
    (receipt : CallableIndexedOwnedPublicPreparedTokenReadyNamedExpressionBounds.PublicReceipt header)
    {diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked)}
    (found : compiled.indexed.base.diagnostics = some diagnostics)
    {node : StatementNode} (statement : .statement node ∈ header.function.source.nodes)
    {assignment : AssignmentResolution}
    (target : assignment ∈ CompatiblePlaceMissingPreparationCoverage.targets node)
    {route : Route}
    (described : describe (.initial compiled.compatible.checked) compiled.compatible.checked.signatures
      header.function.source (.occurrence node.id.occurrence) assignment = .ok route)
    {fuel : Nat} {invalid : Word} {prepared : Prepared}
    (generated : prepare (.initial compiled.compatible.checked) fuel route invalid
      (fun valueType => receipt.original.prepared.diagnostics.placeReason header.named.signature.key
        (.occurrence node.id.occurrence) assignment.target.root (some valueType)) = .ok prepared)
    {sourceContext : SourceSemantics.Context}
    (signatures : sourceContext.signatures = compiled.compatible.checked.signatures)
    (sourceTyped : ∀ binder, rootBinder header.function.source assignment.target.root = .ok binder →
      SourceProjectionsHaveType header.function.source sourceContext binder.scheme.body
        assignment.target.projections assignment.target.type)
    {root leaf : TypeSystem.Ty}
    {path : PreparedPath compiled.compatible.checked header.function.source (.occurrence node.id.occurrence)
      root assignment.target.projections 0 prepared.steps prepared.keys leaf}
    (rootView : SourceCoreRawMetadata.runtimeType root = SourceCoreRawMetadata.runtimeType route.rootSourceType)
    {registry : SourceCoreRawMetadata.Registry}
    {extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry}
    {table : SourceCoreFaultSites.Table} (rebuilt : diagnostics.tableForRegistry registry extension = .ok table)
    {ambient : AmbientDefinitions compiled.compatible.checked.catalog.definitions}
    {functions : FunctionModel compiled.compatible.checked.catalog ambient}
    {mapping : GeneralHeap.LocationMap} {world : StoreTyping} {reason : Dynamic.SemanticFault} {token : Word}
    (terminal : MissingTerminal (registry := registry) functions mapping world path reason token) :
    ∃ rawValue diagnostic, reason = .missingMappingDefault rawValue ∧
      table.diagnostic? token = some diagnostic ∧ diagnostic.error = .typeMismatch rawValue none := by
  obtain ⟨rootKey, sources, issued, collected⟩ := inventory_at_header header found
  have missingEq : (fun valueType => receipt.original.prepared.diagnostics.placeReason header.named.signature.key
      (.occurrence node.id.occurrence) assignment.target.root (some valueType)) =
      (fun valueType => diagnostics.program.placeReason header.named.signature.key
        (.occurrence node.id.occurrence) assignment.target.root (some valueType)) := by
    funext valueType
    exact public_placeReason header receipt found _ _ _ _
  rw [missingEq] at generated
  exact CompatiblePlaceMissingTerminalDiagnostics.terminal_diagnostic issued collected statement target
    (CompatiblePlaceConcretePreparation.describe_concrete
      (CallableIndexedOwnedPublicCatalogClosedSources.compiled_closed compiled) described)
    described generated header.unique signatures sourceTyped rootView rebuilt terminal

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicPlaceMissingDiagnostics
