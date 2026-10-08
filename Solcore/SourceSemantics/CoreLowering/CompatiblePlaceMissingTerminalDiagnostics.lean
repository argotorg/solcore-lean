import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceMissingPreparationCoverage
import Solcore.SourceSemantics.CoreLowering.CompatiblePathMissingProvider
import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceDescription

/-! Static Source projection typing aligns the selected prepared suffix with
an original described route index. Actual inventory coverage and checked
ranges then interpret that terminal's own raw mapping-header token. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePlaceMissingTerminalDiagnostics
open Core Frontend SourceInference CompatiblePayload CompatibleMixedRoute
open SourceCoreCompatibleDataPlaces

private theorem value_view {checked : Checked} {source : TypedSource}
    {root keySource valueSource sourceKey sourceValue : TypeSystem.Ty} {key : ExpressionId}
    {layout : OrderedMapping.Layout}
    (certificate : IndexSite checked source root keySource valueSource key layout)
    (view : SourceCoreRawMetadata.runtimeType root =
      SourceCoreRawMetadata.runtimeType (.mapping sourceKey sourceValue)) :
    SourceCoreRawMetadata.runtimeType valueSource = SourceCoreRawMetadata.runtimeType sourceValue := by
  have mappingView := certificate.view.symm.trans view
  simp only [SourceCoreRawMetadata.runtimeType, TypeSystem.Ty.mapping.injEq] at mappingView
  rw [mappingView.2, SourceCoreRawMetadata.runtimeType_idempotent]

private theorem value_normalized {checked : Checked} {source : TypedSource}
    {root keySource valueSource : TypeSystem.Ty} {key : ExpressionId} {layout : OrderedMapping.Layout}
    (certificate : IndexSite checked source root keySource valueSource key layout) :
    SourceCoreRawMetadata.runtimeType valueSource = valueSource := by
  have stable := congrArg SourceCoreRawMetadata.runtimeType certificate.view
  rw [SourceCoreRawMetadata.runtimeType_idempotent, certificate.view] at stable
  simp only [SourceCoreRawMetadata.runtimeType, TypeSystem.Ty.mapping.injEq] at stable
  exact stable.2.symm

/-- Eliminate only the actual static suffix membership, retaining the original
route value type and its genuine raw runtime view separately. -/
theorem original_index {checked : Checked} {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
    {context : SourceSemantics.Context}
    {terminalRoot keySource valueSource terminalLeaf : TypeSystem.Ty} {key : ExpressionId} {layout : OrderedMapping.Layout}
    {terminalProjections : List PlaceProjection} {terminalSteps : List PreparedStep} {terminalPosition : Nat}
    {terminalKeys : List (ExpressionId × Ty)} {comparison : Expr} {token : Word}
    {certificate : IndexSite checked source terminalRoot keySource valueSource key layout}
    {generated : CompatibleMapping.Index checked ⟨layout, key, terminalPosition, comparison, token⟩}
    {tail : PreparedPath checked source site valueSource terminalProjections (terminalPosition + 1)
      terminalSteps terminalKeys terminalLeaf}
    {root leaf originalRoot originalLeaf sourceRoot sourceLeaf : TypeSystem.Ty}
    {projections : List PlaceProjection} {position : Nat}
    {steps : List PreparedStep} {keys : List (ExpressionId × Ty)} {originalSteps : List Step}
    {path : PreparedPath checked source site root projections position steps keys leaf}
    (selected : IndexInPath (.index certificate generated tail) path)
    (original : Path checked source site originalRoot projections originalSteps originalLeaf)
    {fuel : Nat} {missing : TypeSystem.Ty → Word}
    (prepared : CompatibleMixedPreparation.Steps checked fuel missing originalSteps position steps keys)
    (signatures : context.signatures = checked.signatures)
    (originalView : SourceCoreRawMetadata.runtimeType originalRoot = SourceCoreRawMetadata.runtimeType sourceRoot)
    (view : SourceCoreRawMetadata.runtimeType root = SourceCoreRawMetadata.runtimeType sourceRoot)
    (typed : SourceProjectionsHaveType source context sourceRoot projections sourceLeaf) :
    ∃ originalValue, .index layout key originalValue ∈ originalSteps ∧
      SourceCoreRawMetadata.runtimeType originalValue = originalValue ∧
      SourceCoreRawMetadata.runtimeType originalValue = SourceCoreRawMetadata.runtimeType valueSource := by
  induction selected generalizing originalRoot originalLeaf originalSteps sourceRoot sourceLeaf with
  | here =>
    cases original with
    | index originalCertificate originalTail =>
      cases prepared with
      | index row source generated prepared =>
        cases typed with
        | index keyTyped restTyped =>
          exact ⟨_, List.mem_cons_self, value_normalized originalCertificate,
            (value_view originalCertificate originalView).trans (value_view certificate view).symm⟩
  | @member root field leaf name index signature arguments identity branches fieldType projections steps position keys
      nominal memberSelected memberCertificate tail found ih =>
    cases original with
    | member originalNominal originalSelected originalCertificate originalTail =>
      cases prepared with
      | member prepared =>
        cases typed with
        | member selectedType restTyped =>
          obtain ⟨originalValue, member, normalized, runtimeView⟩ := ih originalTail prepared
            (CompatiblePlaceKeyTyping.member_view signatures originalView originalNominal originalSelected originalCertificate selectedType)
            (CompatiblePlaceKeyTyping.member_view signatures view nominal memberSelected memberCertificate selectedType)
            restTyped
          exact ⟨originalValue, List.mem_cons_of_mem _ member, normalized, runtimeView⟩
  | @index root keySource valueSource leaf key layout projections steps position keys comparison missing
      indexCertificate indexGenerated tail found ih =>
    cases original with
    | index originalCertificate originalTail =>
      cases prepared with
      | index row source generated prepared =>
        cases typed with
        | index keyTyped restTyped =>
          obtain ⟨originalValue, member, normalized, runtimeView⟩ := ih originalTail prepared
            (value_view originalCertificate originalView) (value_view indexCertificate view) restTyped
          exact ⟨originalValue, List.mem_cons_of_mem _ member, normalized, runtimeView⟩

/-- The actual prepared unavailable mapping is interpreted by the same public
inventory and rebuilt raw table. All Source and compiler associations remain
attached to this statement, assignment and accepted description. -/
theorem terminal_diagnostic {context : SourceCoreCompatibleDataPlaceFaultSites.Context}
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
    (gate : CompatiblePlaceMissingPreparationCoverage.concrete source assignment = true)
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
  obtain ⟨binder, originalLeaf, description⟩ := CompatiblePlaceDescription.of_describe described
  obtain ⟨_, _, actualPath, actualProviders⟩ := prepared_of_success_with_providers description.routed generated
  have providers : Providers (fun valueType => program.program.placeReason owner (.occurrence node.id.occurrence)
      assignment.target.root (some valueType)) path := actualProviders
  have typed := sourceTyped binder description.binding
  have rootView : SourceCoreRawMetadata.runtimeType root = SourceCoreRawMetadata.runtimeType binder.scheme.body := by
    simpa only [description.rootSource] using rootView
  have original := CompatibleMixedRoute.of_routeSteps description.routed
  have generatedSteps := (CompatibleMixedPreparation.of_prepare generated).2.2
  obtain ⟨terminalRoot, keySource, valueSource, terminalLeaf, key, layout, terminalProjections,
    terminalSteps, terminalPosition, terminalKeys, comparison, base, certificate, indexGenerated, tail,
    selected, rawKey, rawValue, entries, header, nativeEntries, fallback, lookup, fields,
    keyView, valueView, _lookupTyped, _absent, _unavailable, fault, tokenEq⟩ := terminal
  obtain ⟨originalValue, index, normalized, runtimeView⟩ := original_index
    (certificate := certificate) (generated := indexGenerated) (tail := tail)
    selected original generatedSteps signatures rfl rootView typed
  have valueEq : originalValue = valueSource :=
    normalized.symm.trans (runtimeView.trans (value_normalized certificate))
  have provider := selected.provider (certificate := certificate) (generated := indexGenerated) (tail := tail) providers
  obtain ⟨keyNode, missingSite, found, member, actual⟩ :=
    CompatiblePlaceMissingPreparationCoverage.prepare_coverage issued collected statement target gate described index
  obtain ⟨typedNode, typedFound, typedKeyView⟩ := selected.key_view_of_typing
    (certificate := certificate) (generated := indexGenerated) (tail := tail) unique signatures rootView typed
  have nodes := Option.some.inj (found.symm.trans typedFound)
  have rawKeyView : SourceCoreRawMetadata.runtimeType rawKey = SourceCoreRawMetadata.runtimeType missingSite.keyType := by
    rw [actual]
    dsimp only
    simpa only [nodes, keyView, SourceCoreRawMetadata.runtimeType_idempotent] using typedKeyView
  have rawValueView : SourceCoreRawMetadata.runtimeType rawValue = SourceCoreRawMetadata.runtimeType missingSite.valueType := by
    rw [actual]
    dsimp only
    rw [valueEq, valueView, SourceCoreRawMetadata.runtimeType_idempotent]
  obtain ⟨diagnostic, foundDiagnostic, error⟩ := CompatiblePlaceMissingPreparationRanges.table_diagnostic
    issued rebuilt member fields.metadata rawKeyView rawValueView
  have token : token = missingSite.base.add header := by
    rw [tokenEq, provider, actual]
    dsimp only
    rw [valueEq]
  exact ⟨rawValue, diagnostic, fault, token ▸ foundDiagnostic, error⟩


end Solcore.SourceSemantics.CoreLowering.CompatiblePlaceMissingTerminalDiagnostics
