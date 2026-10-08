import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceMissingTerminalDiagnostics
import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceConcretePreparation

/-! The genuine catalog factory and accepted description supply the concrete
inventory gate. The same actual collection and prepared terminal then use the
existing coverage and raw diagnostic proofs. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePlaceMissingPreparedDiagnostics
open Core Frontend SourceInference CompatiblePayload CompatibleMixedRoute
open SourceCoreCompatibleDataPlaces SourceCoreCompatibleDataPlaceFaultSites

/-- Actual catalog preparation closes the concrete gate for this accepted
assignment description before the real inventory coverage is selected. -/
theorem coverage_of_catalog {context : SourceCoreCompatibleDataPlaceFaultSites.Context}
    {catalogSignatures : ProgramSignatures} {catalogFuel : Nat} {catalogTypes : List TypeSystem.Ty}
    {catalogMetadata : List SourceCoreRawMetadata.Metadata} {catalogLimits : SourceCoreRawMetadata.Limits}
    {catalogProfile : Bool}
    (catalogAccepted : SourceCoreCompatibleCatalog.prepare catalogSignatures catalogFuel catalogTypes
      catalogMetadata catalogLimits catalogProfile = .ok context.checked)
    {plan : Plan} {root : Key} {sources : List (Key × TypedSource)}
    {program : SourceCoreCompatibleDataPlaceFaultSites.Program context}
    (accepted : SourceCoreCompatibleDataPlaceFaultSites.prepare context plan root sources = .ok program)
    {owner : Key} {source : TypedSource}
    (collected : (owner, source) ∈ plan.specializations.map (fun specialized =>
      (specialized.key, specialized.function.typedBody)) ++ sources)
    {node : StatementNode} (statement : .statement node ∈ source.nodes)
    {assignment : AssignmentResolution} (target : assignment ∈ CompatiblePlaceMissingPreparationCoverage.targets node)
    {route : SourceCoreCompatibleDataPlaces.Route}
    (described : SourceCoreCompatibleDataPlaces.describe context context.checked.signatures source
      (.occurrence node.id.occurrence) assignment = .ok route)
    {layout : OrderedMapping.Layout} {key : ExpressionId} {valueType : TypeSystem.Ty}
    (index : .index layout key valueType ∈ route.steps) :
    ∃ keyNode site,
      source.lookupExpression? key = some keyNode ∧ site ∈ program.missing ∧
      site = ⟨owner, .occurrence node.id.occurrence, some assignment.target.root,
        keyNode.type, valueType, node.span,
        program.program.placeReason owner (.occurrence node.id.occurrence) assignment.target.root (some valueType)⟩ := by
  exact CompatiblePlaceMissingPreparationCoverage.prepare_coverage accepted collected statement target
    (CompatiblePlaceConcretePreparation.describe_concrete_of_prepare catalogAccepted described) described index

/-- A genuine catalog factory discharges the concrete gate for the same
actual prepared terminal and its own authenticated raw table error. -/
theorem terminal_of_catalog {context : SourceCoreCompatibleDataPlaceFaultSites.Context}
    {catalogSignatures : ProgramSignatures} {catalogFuel : Nat} {catalogTypes : List TypeSystem.Ty}
    {catalogMetadata : List SourceCoreRawMetadata.Metadata} {catalogLimits : SourceCoreRawMetadata.Limits}
    {catalogProfile : Bool}
    (catalogAccepted : SourceCoreCompatibleCatalog.prepare catalogSignatures catalogFuel catalogTypes
      catalogMetadata catalogLimits catalogProfile = .ok context.checked)
    {plan : SourceCoreCompatibleDataPlaceFaultSites.Plan} {rootKey : SourceCoreCompatibleDataPlaceFaultSites.Key}
    {sources : List (SourceCoreCompatibleDataPlaceFaultSites.Key × TypedSource)}
    {program : SourceCoreCompatibleDataPlaceFaultSites.Program context}
    (issued : SourceCoreCompatibleDataPlaceFaultSites.prepare context plan rootKey sources = .ok program)
    {owner : SourceCoreCompatibleDataPlaceFaultSites.Key} {source : TypedSource}
    (collected : (owner, source) ∈ plan.specializations.map (fun specialized =>
      (specialized.key, specialized.function.typedBody)) ++ sources)
    {node : StatementNode} (statement : .statement node ∈ source.nodes)
    {assignment : AssignmentResolution}
    (target : assignment ∈ CompatiblePlaceMissingPreparationCoverage.targets node)
    {route : Route}
    (described : describe context context.checked.signatures source (.occurrence node.id.occurrence) assignment = .ok route)
    {fuel : Nat} {invalid : Word} {prepared : Prepared}
    (generated : prepare context fuel route invalid
      (fun valueType => program.program.placeReason owner (.occurrence node.id.occurrence)
        assignment.target.root (some valueType)) = .ok prepared)
    {sourceContext : SourceSemantics.Context}
    (unique : NodeOccurrencesUnique source) (signatures : sourceContext.signatures = context.checked.signatures)
    (sourceTyped : ∀ binder, rootBinder source assignment.target.root = .ok binder →
      SourceProjectionsHaveType source sourceContext binder.scheme.body assignment.target.projections assignment.target.type)
    {root leaf : TypeSystem.Ty}
    {path : PreparedPath context.checked source (.occurrence node.id.occurrence) root assignment.target.projections
      0 prepared.steps prepared.keys leaf}
    (rootView : SourceCoreRawMetadata.runtimeType root = SourceCoreRawMetadata.runtimeType route.rootSourceType)
    {registry : SourceCoreRawMetadata.Registry} {extension : SourceCoreRawMetadata.Extends context.registry registry}
    {table : SourceCoreFaultSites.Table} (rebuilt : program.tableForRegistry registry extension = .ok table)
    {ambient : AmbientDefinitions context.checked.catalog.definitions}
    {functions : FunctionModel context.checked.catalog ambient}
    {mapping : GeneralHeap.LocationMap} {world : StoreTyping} {reason : Dynamic.SemanticFault} {token : Word}
    (terminal : MissingTerminal (registry := registry) functions mapping world path reason token) :
    ∃ rawValue diagnostic, reason = .missingMappingDefault rawValue ∧
      table.diagnostic? token = some diagnostic ∧ diagnostic.error = .typeMismatch rawValue none := by
  exact CompatiblePlaceMissingTerminalDiagnostics.terminal_diagnostic issued collected statement target
    (CompatiblePlaceConcretePreparation.describe_concrete_of_prepare catalogAccepted described) described
    generated unique signatures sourceTyped rootView rebuilt terminal

end Solcore.SourceSemantics.CoreLowering.CompatiblePlaceMissingPreparedDiagnostics
