import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedAllocation
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.DiagnosticOrigins
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.PlaceReflection
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.PlaceKeys
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.MappingsAndEquality
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.BodyReadyState
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionReads
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.Paths
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.PlaceWriteback
import Solcore.Frontend.SourceCoreIndexedSession

/-!
# Compatible places: diagnostics

Missing and projection diagnostics of places, public observations and priority, and `CallableIndexedOwnedPublicFaultReceivers.Receiver`.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
/-! Diagnostic receivers retain the actual owning metadata registry and table.
Their construction requires no native execution or unrelated completion. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
open Core Frontend SourceInference
open CallableIndexedOwnedPublicFaultReceiverTables

/-- The metadata and diagnostics needed by public semantic bounds. -/
structure Result (checked : SourceCoreCompatibleCatalog.Checked) where
  context : SourceCoreCompatibleValues.Context
  contextOwner : context.checked = checked
  extension : SourceCoreRawMetadata.Extends checked.staticRegistry context.registry
  diagnostics : SourceCoreFaultSites.Table

/-- Metadata and a literal table, with issuance supplied separately by IssuedAt.
The carrier contains no native execution result. -/
structure Receiver {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCallableIndexedPrograms.Prepared checked) where
  entry : SourceCoreCallableIndexedPrograms.Entry prepared.layouts
  result : Result checked

namespace Receiver

/-- Existing actual runSource clients retain their literal context and table. -/
def of_completion {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
    (completion : SourceCoreCallableIndexedPrograms.Completion prepared) : Receiver prepared where
  entry := completion.entry
  result := ⟨completion.result.context, completion.result.contextOwner,
    completion.result.extension, completion.result.diagnostics⟩

instance {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : SourceCoreCallableIndexedPrograms.Prepared checked} :
    Coe (SourceCoreCallableIndexedPrograms.Completion prepared) (Receiver prepared) :=
  ⟨of_completion⟩

/-- Build the same static fallback or compatible table and callable suffix
that the public codec uses. Table completeness comes from real preparation. -/
theorem at_registry (compiled : SourceCoreUnifiedCompilation.Compiled)
    (entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts)
    (registry : SourceCoreRawMetadata.Registry)
    (extension : SourceCoreRawMetadata.Extends compiled.compatible.checked.staticRegistry registry) :
    ∃ receiver : Receiver compiled.indexed,
      receiver.entry = entry ∧ receiver.result.context.registry = registry ∧
      IssuedAt compiled.indexed receiver.entry receiver.result.context.registry
        receiver.result.extension receiver.result.diagnostics := by
  let values : SourceCoreCompatibleValues.Context := ⟨compiled.compatible.checked, registry, extension⟩
  cases present : compiled.indexed.base.diagnostics with
  | none =>
    let base : SourceCoreFaultSites.Table := {
      owner := entry.key.declaration
      resultType := entry.sourceResultType
      reads := []
      escapedReason := Word.zero }
    exact ⟨⟨entry, ⟨values, rfl, extension, appendCallable compiled.indexed base⟩⟩,
      rfl, rfl, base, by rw [present], rfl⟩
  | some diagnostics =>
    obtain ⟨base, rebuilt⟩ := CompatibleRegistryDiagnosticCompleteness.compiled_table_complete
      compiled present registry extension
    exact ⟨⟨entry, ⟨values, rfl, extension, appendCallable compiled.indexed base⟩⟩,
      rfl, rfl, base, by rw [present]; exact rebuilt, rfl⟩

/-- An exact metadata context obtained from actual public input encoding is
kept verbatim, including its authenticated checked catalog. -/
theorem at_context (compiled : SourceCoreUnifiedCompilation.Compiled)
    (entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts)
    (values : SourceCoreCompatibleValues.Context)
    (owner : values.checked = compiled.compatible.checked) :
    ∃ receiver : Receiver compiled.indexed,
      receiver.entry = entry ∧ receiver.result.context = values ∧
      IssuedAt compiled.indexed receiver.entry receiver.result.context.registry
        receiver.result.extension receiver.result.diagnostics := by
  have extension : SourceCoreRawMetadata.Extends compiled.compatible.checked.staticRegistry values.registry := by
    rw [← owner]
    exact values.extension
  cases present : compiled.indexed.base.diagnostics with
  | none =>
    let base : SourceCoreFaultSites.Table := {
      owner := entry.key.declaration
      resultType := entry.sourceResultType
      reads := []
      escapedReason := Word.zero }
    exact ⟨⟨entry, ⟨values, owner, extension, appendCallable compiled.indexed base⟩⟩,
      rfl, rfl, base, by rw [present], rfl⟩
  | some diagnostics =>
    obtain ⟨base, rebuilt⟩ := CompatibleRegistryDiagnosticCompleteness.compiled_table_complete
      compiled present values.registry extension
    exact ⟨⟨entry, ⟨values, owner, extension, appendCallable compiled.indexed base⟩⟩,
      rfl, rfl, base, by rw [present]; exact rebuilt, rfl⟩

end Receiver
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatiblePlaceMissingTerminalDiagnostics
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatiblePlaceProjectionDiagnosticPreparation
/-! Actual projected-place reasons retain the first fixed diagnostic issued by
preparation. Checked fresh numbers keep those rows outside zero and the
original escaped-control reason. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePlaceProjectionDiagnosticPreparation
open Core Frontend SourceInference CompatiblePayload
open SourceCoreCompatibleDataPlaceFaultSites

/-- The actual first fixed row for a retained projected-place entry. -/
structure FixedReceipt (original : List Word) (fixed : List (Word × Diagnostic))
    (place : SourceCoreDataPlaceFaultSites.Site) : Prop where
  positive : 0 < place.reason.val
  separate : ∀ token, token ∈ original → place.reason ≠ token
  found : fixed.find? (fun row => decide (row.1 = place.reason)) = some (place.reason, place.diagnostic)
  error : place.diagnostic.error = .invalidPlaceProjection

private structure Inventory (capacity next : Nat) (indices : List SourceCoreDataFaultSites.IndexSite)
    (places : List SourceCoreDataPlaceFaultSites.Site) (missing : List MissingSite)
    (original : List Word) (fixed : List (Word × Diagnostic)) : Prop where
  positive : 0 < next
  below : ∀ token, token ∈ original ++ fixed.map Prod.fst → token.val < next
  retained : ∀ place, place ∈ places → place.missingType = none → FixedReceipt original fixed place

private theorem Inventory.mono {capacity next : Nat} {indices : List SourceCoreDataFaultSites.IndexSite}
    {places : List SourceCoreDataPlaceFaultSites.Site} {missing : List MissingSite}
    {original : List Word} {fixed : List (Word × Diagnostic)}
    (inventory : Inventory capacity next indices places missing original fixed)
    {later : Nat} (grows : next ≤ later) : Inventory capacity later indices places missing original fixed := by
  refine ⟨by have := inventory.positive; omega, ?_, inventory.retained⟩
  intro token member
  have bounded := inventory.below token member
  omega

private theorem Inventory.append_missing {capacity next : Nat} {indices : List SourceCoreDataFaultSites.IndexSite}
    {places : List SourceCoreDataPlaceFaultSites.Site} {missing : List MissingSite}
    {original : List Word} {fixed : List (Word × Diagnostic)}
    (inventory : Inventory capacity next indices places missing original fixed) {site : MissingSite} :
    Inventory capacity next indices places (missing ++ [site]) original fixed :=
  ⟨inventory.positive, inventory.below, inventory.retained⟩

private theorem Inventory.index_range {capacity next : Nat} {indices : List SourceCoreDataFaultSites.IndexSite}
    {places : List SourceCoreDataPlaceFaultSites.Site} {missing : List MissingSite}
    {original : List Word} {fixed : List (Word × Diagnostic)}
    (inventory : Inventory capacity next indices places missing original fixed)
    {index : SourceCoreDataFaultSites.IndexSite} :
    Inventory capacity (next + capacity + 1) (indices ++ [index]) places missing original fixed := by
  have later := inventory.mono (later := next + capacity + 1) (by omega)
  exact ⟨later.positive, later.below, later.retained⟩

private theorem Inventory.place_range {capacity next : Nat} {indices : List SourceCoreDataFaultSites.IndexSite}
    {places : List SourceCoreDataPlaceFaultSites.Site} {missing : List MissingSite}
    {original : List Word} {fixed : List (Word × Diagnostic)}
    (inventory : Inventory capacity next indices places missing original fixed)
    {place : SourceCoreDataPlaceFaultSites.Site} {type : TypeSystem.Ty}
    (kind : place.missingType = some type) :
    Inventory capacity (next + capacity + 1) indices (places ++ [place]) missing original fixed := by
  have later := inventory.mono (later := next + capacity + 1) (by omega)
  refine ⟨later.positive, later.below, ?_⟩
  intro entry member none
  rcases List.mem_append.mp member with old | fresh
  · exact later.retained entry old none
  · have same := List.mem_singleton.mp fresh
    subst entry
    rw [kind] at none
    cases none

private theorem Inventory.place_fixed {capacity next : Nat} {indices : List SourceCoreDataFaultSites.IndexSite}
    {places : List SourceCoreDataPlaceFaultSites.Site} {missing : List MissingSite}
    {original : List Word} {fixed : List (Word × Diagnostic)}
    (inventory : Inventory capacity next indices places missing original fixed)
    {place : SourceCoreDataPlaceFaultSites.Site} (number : place.reason.val = next)
    (error : place.diagnostic.error = .invalidPlaceProjection) :
    Inventory capacity (next + 1) indices (places ++ [place]) missing original
      (fixed ++ [(place.reason, place.diagnostic)]) := by
  refine ⟨by have := inventory.positive; omega, ?_, ?_⟩
  · intro token member
    simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at member
    rcases member with old | old | rfl
    · have bounded := inventory.below token (List.mem_append_left _ old); omega
    · have bounded := inventory.below token (List.mem_append_right _ old); omega
    · omega
  · intro entry member kind
    rcases List.mem_append.mp member with old | fresh
    · have prior := inventory.retained entry old kind
      exact ⟨prior.positive, prior.separate, by rw [List.find?_append, prior.found]; rfl, prior.error⟩
    · have same := List.mem_singleton.mp fresh
      subst entry
      have absent : fixed.find? (fun row => decide (row.1 = place.reason)) = none := by
        apply List.find?_eq_none.mpr
        intro row member
        intro same
        have bounded := inventory.below row.1
          (List.mem_append_right _ (List.mem_map.mpr ⟨row, member, rfl⟩))
        have equal := congrArg Fin.val (of_decide_eq_true same)
        omega
      refine ⟨by have := inventory.positive; omega, ?_, ?_, error⟩
      · intro token member same
        have bounded := inventory.below token (List.mem_append_left _ member)
        have equal := congrArg Fin.val same
        omega
      · rw [List.find?_append, absent]
        simp

private theorem foldl_max_initial (values : List Nat) (start : Nat) : start ≤ values.foldl max start := by
  induction values generalizing start with
  | nil => exact Nat.le_refl _
  | cons head tail ih => exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

private theorem foldl_max_member (values : List Nat) {value : Nat} (member : value ∈ values) (start : Nat) :
    value ≤ values.foldl max start := by
  induction values generalizing start with
  | nil => cases member
  | cons head tail ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact Nat.le_trans (Nat.le_max_right _ _) (foldl_max_initial tail _)
    · exact ih member _

private theorem word_number {number : Nat} {reason : Word}
    (accepted : (match Word.ofNat? number with
      | some value => Except.ok value
      | none => Except.error SourceCoreCompatibleDataPlaceFaultSites.Error.reasonSpaceExhausted) = .ok reason) :
    reason.val = number := by
  split at accepted
  · rename_i converted
    have same := Except.ok.inj accepted
    subst reason
    unfold Word.ofNat? at converted
    split at converted
    · exact congrArg Fin.val (Option.some.inj converted).symm
    · cases converted
  · cases accepted

private theorem bind_ok {α β ε : Type} {value : Except ε α} {next : α → Except ε β} {result : β}
    (accepted : (value >>= next) = .ok result) :
    ∃ middle, value = .ok middle ∧ next middle = .ok result := by
  cases value with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem expression_resume {capacity next : Nat} {owner : Key} {source : TypedSource}
    {node : ExpressionNode} {mapping key : ExpressionId}
    {indices : List SourceCoreDataFaultSites.IndexSite} {places : List SourceCoreDataPlaceFaultSites.Site}
    {missing : List MissingSite} {fixed : List (Word × Diagnostic)} {seen : List ExpressionId}
    {original : List Word} {reason : Word}
    (inventory : Inventory capacity next indices places missing original fixed)
    {outcome : ForInStep (Nat × List SourceCoreDataFaultSites.IndexSite × List SourceCoreDataPlaceFaultSites.Site ×
      List MissingSite × List (Word × Diagnostic) × List ExpressionId)}
    (ran : (do
      let baseNode ← match source.lookupExpression? mapping with
        | some base => pure base
        | none => throw (SourceCoreCompatibleDataPlaceFaultSites.Error.lowering (.missingExpression mapping))
      let (keyType, valueType) ← match SourceCoreRawMetadata.runtimeType baseNode.type with
        | .mapping keyType valueType => pure (keyType, valueType)
        | _ => throw (SourceCoreCompatibleDataPlaceFaultSites.Error.lowering (.missingExpression key))
      unless SourceCoreRawMetadata.runtimeType node.type = valueType do
        throw (SourceCoreCompatibleDataPlaceFaultSites.Error.lowering (.missingExpression node.id))
      pure (.yield (next, indices, places,
        missing ++ [⟨owner, .occurrence node.id.occurrence, none, keyType, node.type, node.span, reason⟩],
        fixed, node.id :: seen))) = (Except.ok outcome : Except SourceCoreCompatibleDataPlaceFaultSites.Error _)) :
    ∃ updated, outcome = .yield updated ∧
      Inventory capacity updated.1 updated.2.1 updated.2.2.1 updated.2.2.2.1
        original updated.2.2.2.2.1 := by
  split at ran
  · rename_i base found
    try dsimp only [pure, Except.pure, bind, Except.bind] at ran
    split at ran
    · try dsimp only [pure, Except.pure, bind, Except.bind] at ran
      split at ran
      · exact ⟨_, (Except.ok.inj ran).symm, inventory.append_missing⟩
      · change (Except.error _ : Except SourceCoreCompatibleDataPlaceFaultSites.Error _) = .ok outcome at ran
        cases ran
    · change (Except.error _ : Except SourceCoreCompatibleDataPlaceFaultSites.Error _) = .ok outcome at ran
      cases ran
  · change (Except.error _ : Except SourceCoreCompatibleDataPlaceFaultSites.Error _) = .ok outcome at ran
    cases ran

private theorem place_resume {capacity next : Nat} {owner : Key} {source : TypedSource}
    {node : StatementNode} {assignment : AssignmentResolution} {key : ExpressionId} {valueType : TypeSystem.Ty}
    {indices : List SourceCoreDataFaultSites.IndexSite} {places : List SourceCoreDataPlaceFaultSites.Site}
    {missing : List MissingSite} {fixed : List (Word × Diagnostic)}
    {original : List Word} {reason : Word}
    (inventory : Inventory capacity next indices places missing original fixed)
    {outcome : ForInStep (Nat × List SourceCoreDataPlaceFaultSites.Site × List MissingSite)}
    (ran : (do
      let keyNode ← match source.lookupExpression? key with
        | some keyNode => pure keyNode
        | none => throw (SourceCoreCompatibleDataPlaceFaultSites.Error.lowering (.missingExpression key))
      pure (.yield (next, places,
        missing ++ [⟨owner, .occurrence node.id.occurrence, some assignment.target.root,
          keyNode.type, valueType, node.span, reason⟩]))) = (Except.ok outcome : Except SourceCoreCompatibleDataPlaceFaultSites.Error _)) :
    ∃ updated, outcome = .yield updated ∧
      Inventory capacity updated.1 indices updated.2.1 updated.2.2 original fixed := by
  split at ran
  · try dsimp only [pure, Except.pure, bind, Except.bind] at ran
    exact ⟨_, (Except.ok.inj ran).symm, inventory.append_missing⟩
  · change (Except.error _ : Except SourceCoreCompatibleDataPlaceFaultSites.Error _) = .ok outcome at ran
    cases ran

private theorem route_ranges {capacity next : Nat} {owner : Key} {source : TypedSource}
    {node : StatementNode} {assignment : AssignmentResolution}
    {indices : List SourceCoreDataFaultSites.IndexSite} {places : List SourceCoreDataPlaceFaultSites.Site}
    {missing : List MissingSite} {fixed : List (Word × Diagnostic)} {original : List Word}
    {steps : List SourceCoreCompatibleDataPlaces.Step}
    {issue : Nat → Except SourceCoreCompatibleDataPlaceFaultSites.Error Word}
    (_wordEq : ∀ number, issue number = match Word.ofNat? number with
      | some value => Except.ok value
      | none => Except.error SourceCoreCompatibleDataPlaceFaultSites.Error.reasonSpaceExhausted)
    (inventory : Inventory capacity next indices places missing original fixed)
    {result : Nat × List SourceCoreDataPlaceFaultSites.Site × List MissingSite}
    (ran : forIn steps (next, places, missing) (fun step current => do
      let mut next := current.1
      let mut places := current.2.1
      let mut missing := current.2.2
      match step with
      | .index _ key valueType =>
          let reason ← match places.find? (fun previous => decide
              (previous.owner = owner ∧ previous.location = .occurrence node.id.occurrence ∧
               previous.binder = assignment.target.root ∧ previous.missingType = some valueType)) with
            | some previous => pure previous.reason
            | none => do
                let reason ← issue next
                discard <| issue (next + (capacity + 1) - 1)
                next := next + (capacity + 1)
                let diagnostic : Diagnostic := ⟨.typeMismatch valueType none,
                  .occurrence node.id.occurrence, some node.span⟩
                places := places ++ [⟨owner, .occurrence node.id.occurrence, assignment.target.root,
                  some valueType, reason, diagnostic⟩]
                pure reason
          let keyNode ← match source.lookupExpression? key with
            | some keyNode => pure keyNode | none => throw (SourceCoreCompatibleDataPlaceFaultSites.Error.lowering (.missingExpression key))
          missing := missing ++ [⟨owner, .occurrence node.id.occurrence, some assignment.target.root,
            keyNode.type, valueType, node.span, reason⟩]
      | _ => pure ()
      pure (.yield (next, places, missing))) = Except.ok result) :
    Inventory capacity result.1 indices result.2.1 result.2.2 original fixed := by
  apply CompatibleMemberCertificates.forIn_preserves ran (fun _ current =>
    Inventory capacity current.1 indices current.2.1 current.2.2 original fixed) inventory
  intro seen step remaining current outcome _split previous ran
  obtain ⟨next, places, missing⟩ := current
  dsimp only at ran
  cases step with
  | member => exact ⟨_, (Except.ok.inj ran).symm, previous⟩
  | index layout key valueType =>
    dsimp only at ran
    split at ran
    · rename_i _prior _found
      try dsimp only [pure, Except.pure, bind, Except.bind] at ran
      exact place_resume previous ran
    · obtain ⟨reason, _generated, ran⟩ := bind_ok ran
      obtain ⟨_endpoint, _checked, ran⟩ := bind_ok ran
      try dsimp only [pure, Except.pure, bind, Except.bind] at ran
      have issued := previous.place_range (place := ⟨owner, .occurrence node.id.occurrence,
        assignment.target.root, some valueType, reason,
        ⟨.typeMismatch valueType none, .occurrence node.id.occurrence, some node.span⟩⟩) rfl
      simp only [Nat.add_assoc] at issued
      exact place_resume issued ran

/-- Every actual None-place entry keeps its first fixed diagnostic and lies
outside zero and the original escaped-control reason. -/
theorem prepare_fixed {context : SourceCoreCompatibleDataPlaceFaultSites.Context} {plan : Plan} {root : Key}
    {sources : List (Key × TypedSource)} {program : SourceCoreCompatibleDataPlaceFaultSites.Program context}
    (accepted : SourceCoreCompatibleDataPlaceFaultSites.prepare context plan root sources = .ok program) :
    ∀ place, place ∈ program.program.places → place.missingType = none →
      0 < place.reason.val ∧ place.reason ≠ program.program.rootTable.escapedReason ∧
      program.fixed.find? (fun row => decide (row.1 = place.reason)) = some (place.reason, place.diagnostic) ∧
      place.diagnostic.error = .invalidPlaceProjection := by
  unfold SourceCoreCompatibleDataPlaceFaultSites.prepare at accepted
  obtain ⟨base, _baseAccepted, accepted⟩ := bind_ok accepted
  obtain ⟨state, loop, accepted⟩ := bind_ok accepted
  let original := base.rootTable.reads.map (·.reason) ++ [base.rootTable.escapedReason]
  let capacity := context.registry.limits.maxEntries
  let invariant := fun (_ : List (Key × TypedSource))
    (state : Nat × List SourceCoreDataFaultSites.IndexSite × List SourceCoreDataPlaceFaultSites.Site ×
      List MissingSite × List (Word × Diagnostic)) =>
    Inventory capacity state.1 state.2.1 state.2.2.1 state.2.2.2.1 original state.2.2.2.2
  have generated : invariant (plan.specializations.map (fun specialized =>
      (specialized.key, specialized.function.typedBody)) ++ sources) state := by
    apply CompatibleMemberCertificates.forIn_preserves loop invariant
    · change Inventory capacity _ [] [] [] original base.rootTable.additional
      refine ⟨by omega, ?_, ?_⟩
      · intro token member
        have used : token.val ∈ base.rootTable.reads.map (·.reason.val) ++
              base.rootTable.additional.map (·.1.val) ++ [base.rootTable.escapedReason.val] := by
          simp only [original, List.mem_append, List.mem_map, List.mem_singleton] at member ⊢
          grind
        have bounded := foldl_max_member _ used 0
        omega
      · intro place member; cases member
    · intro seen item remaining current outcome _split previous ran
      obtain ⟨next, indices, places, missing, fixed⟩ := current
      obtain ⟨owner, source⟩ := item
      dsimp only at ran
      by_cases ownerMismatch : source.owner ≠ owner.declaration
      · rw [if_pos ownerMismatch] at ran
        change (Except.error (.sourceOwnerMismatch owner.declaration source.owner) :
          Except SourceCoreCompatibleDataPlaceFaultSites.Error _) = .ok outcome at ran
        cases ran
      · rw [if_neg ownerMismatch] at ran
        obtain ⟨current, nodesLoop, finished⟩ := bind_ok ran
        refine ⟨_, (Except.ok.inj finished).symm, ?_⟩
        let nodeInvariant := fun (_ : List Node)
          (state : Nat × List SourceCoreDataFaultSites.IndexSite × List SourceCoreDataPlaceFaultSites.Site ×
            List MissingSite × List (Word × Diagnostic) × List ExpressionId) =>
          Inventory capacity state.1 state.2.1 state.2.2.1 state.2.2.2.1 original state.2.2.2.2.1
        change nodeInvariant source.nodes current
        apply CompatibleMemberCertificates.forIn_preserves nodesLoop nodeInvariant previous
        intro seen retained remaining current outcome _split previous ran
        obtain ⟨next, indices, places, missing, fixed, seenIndices⟩ := current
        dsimp only at ran
        cases retained with
        | expression node =>
          cases form : node.form <;> simp only [form] at ran
          all_goals first
            | exact ⟨_, (Except.ok.inj ran).symm, previous⟩
            | skip
          case index mapping key =>
            by_cases nodeOwner : node.id.occurrence.owner ≠ source.owner
            · rw [if_pos nodeOwner] at ran
              change (Except.error (.ownerMismatch node.id) : Except SourceCoreCompatibleDataPlaceFaultSites.Error _) = .ok outcome at ran
              cases ran
            · rw [if_neg nodeOwner] at ran
              by_cases mappingOwner : mapping.occurrence.owner ≠ source.owner
              · rw [if_pos mappingOwner] at ran
                change (Except.error (.ownerMismatch mapping) : Except SourceCoreCompatibleDataPlaceFaultSites.Error _) = .ok outcome at ran
                cases ran
              · rw [if_neg mappingOwner] at ran
                by_cases keyOwner : key.occurrence.owner ≠ source.owner
                · rw [if_pos keyOwner] at ran
                  change (Except.error (.ownerMismatch key) : Except SourceCoreCompatibleDataPlaceFaultSites.Error _) = .ok outcome at ran
                  cases ran
                · rw [if_neg keyOwner] at ran
                  by_cases duplicate : seenIndices.contains node.id = true
                  · rw [if_pos duplicate] at ran
                    change (Except.error (.duplicateOccurrence node.id) : Except SourceCoreCompatibleDataPlaceFaultSites.Error _) = .ok outcome at ran
                    cases ran
                  · rw [if_neg duplicate] at ran
                    split at ran
                    · rename_i _prior _found
                      try dsimp only [pure, Except.pure, bind, Except.bind] at ran
                      exact expression_resume previous ran
                    · obtain ⟨reason, _generated, ran⟩ := bind_ok ran
                      obtain ⟨_endpoint, _checked, ran⟩ := bind_ok ran
                      try dsimp only [pure, Except.pure, bind, Except.bind] at ran
                      have issued := previous.index_range (index := ⟨owner, node.id, reason,
                        ⟨.typeMismatch node.type none, .occurrence node.id.occurrence, some node.span⟩⟩)
                      simp only [Nat.add_assoc] at issued
                      exact expression_resume issued ran
        | statement node =>
          obtain ⟨current, targetsLoop, finished⟩ := bind_ok ran
          refine ⟨_, (Except.ok.inj finished).symm, ?_⟩
          change Inventory capacity current.1 indices current.2.1 current.2.2.1
            original current.2.2.2
          apply CompatibleMemberCertificates.forIn_preserves targetsLoop (fun _ current =>
            Inventory capacity current.1 indices current.2.1 current.2.2.1
              original current.2.2.2) previous
          intro seen assignment remaining current outcome _split previous ran
          obtain ⟨next, places, missing, fixed⟩ := current
          dsimp only at ran
          split at ran
          · obtain ⟨route, _described, ran⟩ := bind_ok ran
            split at ran
            · obtain ⟨current, stepsLoop, finished⟩ := bind_ok ran
              exact ⟨_, (Except.ok.inj finished).symm, route_ranges (owner := owner) (source := source) (node := node) (assignment := assignment) (steps := route.steps) (fun _ => rfl) previous stepsLoop⟩
            · obtain ⟨reason, generated, ran⟩ := bind_ok ran
              have number := word_number generated
              have issued := previous.place_fixed (place := ⟨owner, .occurrence node.id.occurrence,
                assignment.target.root, none, reason,
                ⟨.invalidPlaceProjection, .occurrence node.id.occurrence, some node.span⟩⟩) number rfl
              try dsimp only [pure, Except.pure, bind, Except.bind] at ran
              obtain ⟨current, stepsLoop, finished⟩ := bind_ok ran
              refine ⟨_, (Except.ok.inj finished).symm, ?_⟩
              apply route_ranges (owner := owner) (source := source) (node := node) (assignment := assignment) (steps := route.steps) (fun _ => rfl) _ stepsLoop
              simpa only [List.map_append, List.map_cons, List.map_nil, List.append_assoc] using issued
          · exact ⟨_, (Except.ok.inj ran).symm, previous⟩
  obtain ⟨extra, _extraAccepted, finished⟩ := bind_ok accepted
  have same := Except.ok.inj finished
  subst program
  obtain ⟨next, indices, places, missing, fixed⟩ := state
  change Inventory capacity next indices places missing original fixed at generated
  intro place member kind
  have receipt := generated.retained place member kind
  exact ⟨receipt.positive, receipt.separate _
    (List.mem_append_right _ (List.mem_singleton_self _)), receipt.found, receipt.error⟩

/-- The real rebuilt table preserves the first fixed row before later
missing-default rows. Its exact error is the emitted projection rejection. -/
theorem table_diagnostic {context : SourceCoreCompatibleDataPlaceFaultSites.Context}
    {plan : Plan} {root : Key} {sources : List (Key × TypedSource)}
    {program : SourceCoreCompatibleDataPlaceFaultSites.Program context}
    (accepted : SourceCoreCompatibleDataPlaceFaultSites.prepare context plan root sources = .ok program)
    {place : SourceCoreDataPlaceFaultSites.Site} (member : place ∈ program.program.places)
    (kind : place.missingType = none)
    {registry : SourceCoreRawMetadata.Registry}
    {extension : SourceCoreRawMetadata.Extends program.context.registry registry}
    {table : SourceCoreFaultSites.Table} (rebuilt : program.tableForRegistry registry extension = .ok table) :
    table.diagnostic? place.reason = some place.diagnostic ∧
      place.diagnostic.error = .invalidPlaceProjection := by
  obtain ⟨positive, separate, found, error⟩ := prepare_fixed accepted place member kind
  unfold SourceCoreCompatibleDataPlaceFaultSites.Program.tableForRegistry at rebuilt
  obtain ⟨extra, _generated, finished⟩ := bind_ok rebuilt
  have same := Except.ok.inj finished
  subst table
  have nonzero : place.reason ≠ Word.zero := by
    intro zero
    have equal := congrArg Fin.val zero
    change place.reason.val = 0 at equal
    omega
  refine ⟨?_, error⟩
  simp only [SourceCoreFaultSites.Table.diagnostic?, nonzero, separate, if_false,
    List.find?_append, found]
  rfl

end Solcore.SourceSemantics.CoreLowering.CompatiblePlaceProjectionDiagnosticPreparation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatiblePlaceProjectionDiagnosticCoverage
/-! Accepted preparation retains the first projected-target place entry for
each actual concrete assignment occurrence. Duplicate sites use the entry
already selected by the original producer. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePlaceProjectionDiagnosticCoverage
open Core Frontend SourceInference CompatiblePayload
open SourceCoreCompatibleDataPlaceFaultSites

abbrev targets := CompatiblePlaceMissingPreparationCoverage.targets
abbrev concrete := CompatiblePlaceMissingPreparationCoverage.concrete

private def selects (owner : Key) (node : StatementNode) (assignment : AssignmentResolution)
    (entry : SourceCoreDataPlaceFaultSites.Site) : Bool :=
  decide (entry.owner = owner ∧ entry.location = .occurrence node.id.occurrence ∧
    entry.binder = assignment.target.root ∧ entry.missingType = none)

private structure Growth (places later : List SourceCoreDataPlaceFaultSites.Site)
    (missing more : List MissingSite) : Prop where
  places : ∃ suffix, later = places ++ suffix
  missing : ∃ suffix, more = missing ++ suffix

private theorem Growth.refl (places : List SourceCoreDataPlaceFaultSites.Site)
    (missing : List MissingSite) : Growth places places missing missing :=
  ⟨⟨[], (List.append_nil _).symm⟩, ⟨[], (List.append_nil _).symm⟩⟩

private theorem Growth.trans {first middle last : List SourceCoreDataPlaceFaultSites.Site}
    {before current after : List MissingSite}
    (one : Growth first middle before current) (two : Growth middle last current after) :
    Growth first last before after := by
  obtain ⟨left, rfl⟩ := one.places
  obtain ⟨right, rfl⟩ := two.places
  obtain ⟨leftMissing, rfl⟩ := one.missing
  obtain ⟨rightMissing, rfl⟩ := two.missing
  exact ⟨⟨left ++ right, List.append_assoc _ _ _⟩,
    ⟨leftMissing ++ rightMissing, List.append_assoc _ _ _⟩⟩

/-- The actual first matching uninitialized-target entry. Its diagnostic
span is the one retained by preparation, including genuine earlier reuse. -/
structure Receipt (owner : Key) (node : StatementNode) (assignment : AssignmentResolution)
    (places : List SourceCoreDataPlaceFaultSites.Site) (missing : List MissingSite) : Prop where
  retained : ∃ entry, places.find? (selects owner node assignment) = some entry

private theorem Receipt.grows {owner : Key} {node : StatementNode} {assignment : AssignmentResolution}
    {places later : List SourceCoreDataPlaceFaultSites.Site} {missing more : List MissingSite}
    (receipt : Receipt owner node assignment places missing)
    (growth : Growth places later missing more) : Receipt owner node assignment later more := by
  obtain ⟨entry, found⟩ := receipt.retained
  obtain ⟨suffix, rfl⟩ := growth.places
  exact ⟨⟨entry, by rw [List.find?_append, found]; rfl⟩⟩

private theorem receipt_of_any {owner : Key} {node : StatementNode} {assignment : AssignmentResolution}
    {places : List SourceCoreDataPlaceFaultSites.Site} {missing : List MissingSite}
    (present : places.any (selects owner node assignment) = true) :
    Receipt owner node assignment places missing := by
  cases found : places.find? (selects owner node assignment) with
  | some entry => exact ⟨⟨entry, found⟩⟩
  | none =>
    obtain ⟨entry, member, selected⟩ := List.any_eq_true.mp present
    have absent := List.find?_eq_none.mp found entry member
    exact False.elim (absent selected)

private theorem bind_ok {α β ε : Type} {value : Except ε α} {next : α → Except ε β} {result : β}
    (accepted : (value >>= next) = .ok result) :
    ∃ middle, value = .ok middle ∧ next middle = .ok result := by
  cases value with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem forIn_receipts {α β ε : Type} {items : List α} {initial final : β}
    {step : α → β → Except ε (ForInStep β)}
    (accepted : forIn items initial step = .ok final)
    (grows : β → β → Prop) (reflexive : ∀ state, grows state state)
    (transitive : ∀ first middle last, grows first middle → grows middle last → grows first last)
    (receipt : α → β → Prop)
    (transport : ∀ item before after, receipt item before → grows before after → receipt item after)
    (next : ∀ seen item remaining state outcome,
      items = seen ++ item :: remaining → step item state = .ok outcome →
      ∃ updated, outcome = .yield updated ∧ grows state updated ∧ receipt item updated) :
    grows initial final ∧ ∀ item, item ∈ items → receipt item final := by
  apply CompatibleMemberCertificates.forIn_preserves accepted
    (fun seen state => grows initial state ∧ ∀ item, item ∈ seen → receipt item state)
  · exact ⟨reflexive _, fun _ member => False.elim (List.not_mem_nil member)⟩
  · intro seen item remaining state outcome split previous ran
    obtain ⟨updated, actual, growth, current⟩ := next seen item remaining state outcome split ran
    refine ⟨updated, actual, transitive _ _ _ previous.1 growth, ?_⟩
    intro prior member
    rcases List.mem_append.mp member with old | new
    · exact transport prior state updated (previous.2 prior old) growth
    · exact List.mem_singleton.mp new ▸ current

private theorem route_receipts {capacity next : Nat} {owner : Key} {source : TypedSource}
    {node : StatementNode} {assignment : AssignmentResolution}
    {places : List SourceCoreDataPlaceFaultSites.Site} {missing : List MissingSite}
    {steps : List SourceCoreCompatibleDataPlaces.Step}
    {issue : Nat → Except SourceCoreCompatibleDataPlaceFaultSites.Error Word}
    {result : Nat × List SourceCoreDataPlaceFaultSites.Site × List MissingSite}
    (ran : forIn steps (next, places, missing) (fun step current => do
      let mut next := current.1
      let mut places := current.2.1
      let mut missing := current.2.2
      match step with
      | .index _ key valueType =>
          let reason ← match places.find? (fun previous => decide
              (previous.owner = owner ∧ previous.location = .occurrence node.id.occurrence ∧
               previous.binder = assignment.target.root ∧ previous.missingType = some valueType)) with
            | some previous => pure previous.reason
            | none => do
                let reason ← issue next
                discard <| issue (next + (capacity + 1) - 1)
                next := next + (capacity + 1)
                let diagnostic : Diagnostic := ⟨.typeMismatch valueType none,
                  .occurrence node.id.occurrence, some node.span⟩
                places := places ++ [⟨owner, .occurrence node.id.occurrence, assignment.target.root,
                  some valueType, reason, diagnostic⟩]
                pure reason
          let keyNode ← match source.lookupExpression? key with
            | some keyNode => pure keyNode | none => throw (SourceCoreCompatibleDataPlaceFaultSites.Error.lowering (.missingExpression key))
          missing := missing ++ [⟨owner, .occurrence node.id.occurrence, some assignment.target.root,
            keyNode.type, valueType, node.span, reason⟩]
      | _ => pure ()
      pure (.yield (next, places, missing))) = Except.ok result) :
    Growth places result.2.1 missing result.2.2 := by
  apply CompatibleMemberCertificates.forIn_preserves ran (fun _ current =>
    Growth places current.2.1 missing current.2.2) (Growth.refl _ _)
  intro seen step remaining current outcome _split previous ran
  obtain ⟨next, places, missing⟩ := current
  dsimp only at ran
  cases step with
  | member => exact ⟨_, (Except.ok.inj ran).symm, previous⟩
  | index layout key valueType =>
    dsimp only at ran
    split at ran
    · try dsimp only [pure, Except.pure, bind, Except.bind] at ran
      split at ran
      · try dsimp only [pure, Except.pure, bind, Except.bind] at ran
        exact ⟨_, (Except.ok.inj ran).symm,
          previous.trans ⟨⟨[], (List.append_nil _).symm⟩, ⟨[_], rfl⟩⟩⟩
      · change (Except.error _ : Except SourceCoreCompatibleDataPlaceFaultSites.Error _) = .ok outcome at ran
        cases ran
    · obtain ⟨reason, _generated, ran⟩ := bind_ok ran
      obtain ⟨_endpoint, _checked, ran⟩ := bind_ok ran
      try dsimp only [pure, Except.pure, bind, Except.bind] at ran
      split at ran
      · try dsimp only [pure, Except.pure, bind, Except.bind] at ran
        exact ⟨_, (Except.ok.inj ran).symm,
          previous.trans ⟨⟨[_], rfl⟩, ⟨[_], rfl⟩⟩⟩
      · change (Except.error _ : Except SourceCoreCompatibleDataPlaceFaultSites.Error _) = .ok outcome at ran
        cases ran

private def AssignmentReceipt (context : SourceCoreCompatibleDataPlaceFaultSites.Context)
    (owner : Key) (source : TypedSource) (node : StatementNode) (assignment : AssignmentResolution)
    (places : List SourceCoreDataPlaceFaultSites.Site) (missing : List MissingSite) : Prop :=
  ∀ route, concrete source assignment = true →
    SourceCoreCompatibleDataPlaces.describe context context.checked.signatures source
      (.occurrence node.id.occurrence) assignment = .ok route →
    route.steps ≠ [] → Receipt owner node assignment places missing

private def NodeReceipt (context : SourceCoreCompatibleDataPlaceFaultSites.Context)
    (owner : Key) (source : TypedSource) (retained : Node)
    (places : List SourceCoreDataPlaceFaultSites.Site) (missing : List MissingSite) : Prop :=
  match retained with
  | .statement node => ∀ assignment, assignment ∈ targets node →
      AssignmentReceipt context owner source node assignment places missing
  | .expression _ => True

private def SourceReceipt (context : SourceCoreCompatibleDataPlaceFaultSites.Context)
    (item : Key × TypedSource) (places : List SourceCoreDataPlaceFaultSites.Site)
    (missing : List MissingSite) : Prop :=
  ∀ retained, retained ∈ item.2.nodes → NodeReceipt context item.1 item.2 retained places missing

private theorem AssignmentReceipt.grows {context : SourceCoreCompatibleDataPlaceFaultSites.Context}
    {owner : Key} {source : TypedSource} {node : StatementNode} {assignment : AssignmentResolution}
    {places later : List SourceCoreDataPlaceFaultSites.Site} {missing more : List MissingSite}
    (receipt : AssignmentReceipt context owner source node assignment places missing)
    (growth : Growth places later missing more) :
    AssignmentReceipt context owner source node assignment later more := by
  intro route concrete described nonempty
  exact (receipt route concrete described nonempty).grows growth

private theorem NodeReceipt.grows {context : SourceCoreCompatibleDataPlaceFaultSites.Context}
    {owner : Key} {source : TypedSource} {retained : Node}
    {places later : List SourceCoreDataPlaceFaultSites.Site} {missing more : List MissingSite}
    (receipt : NodeReceipt context owner source retained places missing)
    (growth : Growth places later missing more) :
    NodeReceipt context owner source retained later more := by
  cases retained with
  | expression => trivial
  | statement => exact fun assignment member => (receipt assignment member).grows growth

private theorem SourceReceipt.grows {context : SourceCoreCompatibleDataPlaceFaultSites.Context}
    {item : Key × TypedSource}
    {places later : List SourceCoreDataPlaceFaultSites.Site} {missing more : List MissingSite}
    (receipt : SourceReceipt context item places missing)
    (growth : Growth places later missing more) : SourceReceipt context item later more :=
  fun retained member => (receipt retained member).grows growth

private theorem expression_growth {next : Nat} {owner : Key} {source : TypedSource}
    {node : ExpressionNode} {mapping key : ExpressionId}
    {indices : List SourceCoreDataFaultSites.IndexSite} {places : List SourceCoreDataPlaceFaultSites.Site}
    {missing : List MissingSite} {fixed : List (Word × Diagnostic)} {seen : List ExpressionId}
    {reason : Word}
    {outcome : ForInStep (Nat × List SourceCoreDataFaultSites.IndexSite × List SourceCoreDataPlaceFaultSites.Site ×
      List MissingSite × List (Word × Diagnostic) × List ExpressionId)}
    (ran : (do
      let baseNode ← match source.lookupExpression? mapping with
        | some base => pure base
        | none => throw (SourceCoreCompatibleDataPlaceFaultSites.Error.lowering (.missingExpression mapping))
      let (keyType, valueType) ← match SourceCoreRawMetadata.runtimeType baseNode.type with
        | .mapping keyType valueType => pure (keyType, valueType)
        | _ => throw (SourceCoreCompatibleDataPlaceFaultSites.Error.lowering (.missingExpression key))
      unless SourceCoreRawMetadata.runtimeType node.type = valueType do
        throw (SourceCoreCompatibleDataPlaceFaultSites.Error.lowering (.missingExpression node.id))
      pure (.yield (next, indices, places,
        missing ++ [⟨owner, .occurrence node.id.occurrence, none, keyType, node.type, node.span, reason⟩],
        fixed, node.id :: seen))) = (Except.ok outcome : Except SourceCoreCompatibleDataPlaceFaultSites.Error _)) :
    ∃ updated, outcome = .yield updated ∧ Growth places updated.2.2.1 missing updated.2.2.2.1 := by
  split at ran
  · try dsimp only [pure, Except.pure, bind, Except.bind] at ran
    split at ran
    · try dsimp only [pure, Except.pure, bind, Except.bind] at ran
      split at ran
      · exact ⟨_, (Except.ok.inj ran).symm, ⟨⟨[], (List.append_nil _).symm⟩, ⟨[_], rfl⟩⟩⟩
      · change (Except.error _ : Except SourceCoreCompatibleDataPlaceFaultSites.Error _) = .ok outcome at ran
        cases ran
    · change (Except.error _ : Except SourceCoreCompatibleDataPlaceFaultSites.Error _) = .ok outcome at ran
      cases ran
  · change (Except.error _ : Except SourceCoreCompatibleDataPlaceFaultSites.Error _) = .ok outcome at ran
    cases ran

/-- Every actual concrete projected target has the real first None-place
entry retained by the accepted producer. -/
theorem prepare_coverage {context : SourceCoreCompatibleDataPlaceFaultSites.Context}
    {plan : Plan} {root : Key} {sources : List (Key × TypedSource)}
    {program : SourceCoreCompatibleDataPlaceFaultSites.Program context}
    (accepted : SourceCoreCompatibleDataPlaceFaultSites.prepare context plan root sources = .ok program)
    {owner : Key} {source : TypedSource}
    (collected : (owner, source) ∈ plan.specializations.map (fun specialized =>
      (specialized.key, specialized.function.typedBody)) ++ sources)
    {node : StatementNode} (statement : .statement node ∈ source.nodes)
    {assignment : AssignmentResolution} (target : assignment ∈ targets node)
    (gate : concrete source assignment = true)
    {route : SourceCoreCompatibleDataPlaces.Route}
    (described : SourceCoreCompatibleDataPlaces.describe context context.checked.signatures source
      (.occurrence node.id.occurrence) assignment = .ok route)
    (nonempty : route.steps ≠ []) :
    ∃ entry, entry ∈ program.program.places ∧ entry.missingType = none ∧
      program.program.places.find? (fun previous => decide
        (previous.owner = owner ∧ previous.location = .occurrence node.id.occurrence ∧
          previous.binder = assignment.target.root ∧ previous.missingType = none)) = some entry ∧
      program.program.placeReason owner (.occurrence node.id.occurrence) assignment.target.root none = entry.reason := by
  unfold SourceCoreCompatibleDataPlaceFaultSites.prepare at accepted
  obtain ⟨base, _baseAccepted, accepted⟩ := bind_ok accepted
  obtain ⟨state, loop, accepted⟩ := bind_ok accepted
  have generated :
      ∀ item, item ∈ plan.specializations.map (fun specialized =>
        (specialized.key, specialized.function.typedBody)) ++ sources →
      SourceReceipt context item state.2.2.1 state.2.2.2.1 := by
    apply (forIn_receipts loop
      (fun before after => Growth before.2.2.1 after.2.2.1 before.2.2.2.1 after.2.2.2.1)
      (fun _ => Growth.refl _ _) (fun _ _ _ => Growth.trans)
      (fun item state => SourceReceipt context item state.2.2.1 state.2.2.2.1)
      (fun _ _ _ receipt growth => receipt.grows growth) ?_).2
    intro seen item remaining current outcome _split ran
    obtain ⟨next, indices, places, missing, fixed⟩ := current
    obtain ⟨owner, source⟩ := item
    dsimp only at ran
    by_cases ownerMismatch : source.owner ≠ owner.declaration
    · rw [if_pos ownerMismatch] at ran
      change (Except.error (.sourceOwnerMismatch owner.declaration source.owner) :
        Except SourceCoreCompatibleDataPlaceFaultSites.Error _) = .ok outcome at ran
      cases ran
    · rw [if_neg ownerMismatch] at ran
      obtain ⟨current, nodesLoop, finished⟩ := bind_ok ran
      have nodes : Growth places current.2.2.1 missing current.2.2.2.1 ∧
          ∀ retained, retained ∈ source.nodes →
            NodeReceipt context owner source retained current.2.2.1 current.2.2.2.1 := by
        apply forIn_receipts nodesLoop
          (fun before after => Growth before.2.2.1 after.2.2.1 before.2.2.2.1 after.2.2.2.1)
          (fun _ => Growth.refl _ _) (fun _ _ _ => Growth.trans)
          (fun retained state => NodeReceipt context owner source retained state.2.2.1 state.2.2.2.1)
        · exact fun _ _ _ receipt growth => receipt.grows growth
        · intro seen retained remaining current outcome _split ran
          obtain ⟨next, indices, places, missing, fixed, seenIndices⟩ := current
          dsimp only at ran
          cases retained with
          | expression node =>
            cases form : node.form <;> simp only [form] at ran
            all_goals first
              | exact ⟨_, (Except.ok.inj ran).symm, Growth.refl _ _, True.intro⟩
              | skip
            case index mapping key =>
              by_cases nodeOwner : node.id.occurrence.owner ≠ source.owner
              · rw [if_pos nodeOwner] at ran
                change (Except.error (.ownerMismatch node.id) : Except SourceCoreCompatibleDataPlaceFaultSites.Error _) = .ok outcome at ran
                cases ran
              · rw [if_neg nodeOwner] at ran
                by_cases mappingOwner : mapping.occurrence.owner ≠ source.owner
                · rw [if_pos mappingOwner] at ran
                  change (Except.error (.ownerMismatch mapping) : Except SourceCoreCompatibleDataPlaceFaultSites.Error _) = .ok outcome at ran
                  cases ran
                · rw [if_neg mappingOwner] at ran
                  by_cases keyOwner : key.occurrence.owner ≠ source.owner
                  · rw [if_pos keyOwner] at ran
                    change (Except.error (.ownerMismatch key) : Except SourceCoreCompatibleDataPlaceFaultSites.Error _) = .ok outcome at ran
                    cases ran
                  · rw [if_neg keyOwner] at ran
                    by_cases duplicate : seenIndices.contains node.id = true
                    · rw [if_pos duplicate] at ran
                      change (Except.error (.duplicateOccurrence node.id) : Except SourceCoreCompatibleDataPlaceFaultSites.Error _) = .ok outcome at ran
                      cases ran
                    · rw [if_neg duplicate] at ran
                      split at ran
                      · try dsimp only [pure, Except.pure, bind, Except.bind] at ran
                        obtain ⟨updated, actual, growth⟩ := expression_growth ran
                        exact ⟨updated, actual, growth, True.intro⟩
                      · obtain ⟨reason, _generated, ran⟩ := bind_ok ran
                        obtain ⟨endpoint, _checked, ran⟩ := bind_ok ran
                        try dsimp only [pure, Except.pure, bind, Except.bind] at ran
                        obtain ⟨updated, actual, growth⟩ := expression_growth ran
                        exact ⟨updated, actual, growth, True.intro⟩
          | statement node =>
            obtain ⟨current, targetsLoop, finished⟩ := bind_ok ran
            have assignments : Growth places current.2.1 missing current.2.2.1 ∧
                ∀ assignment, assignment ∈ targets node →
                  AssignmentReceipt context owner source node assignment current.2.1 current.2.2.1 := by
              apply forIn_receipts targetsLoop
                (fun before after => Growth before.2.1 after.2.1 before.2.2.1 after.2.2.1)
                (fun _ => Growth.refl _ _) (fun _ _ _ => Growth.trans)
                (fun assignment state => AssignmentReceipt context owner source node assignment state.2.1 state.2.2.1)
              · exact fun _ _ _ receipt growth => receipt.grows growth
              · intro seen assignment remaining current outcome _split ran
                obtain ⟨next, places, missing, fixed⟩ := current
                dsimp only at ran
                split at ran
                · rename_i visited
                  obtain ⟨route, actualDescription, ran⟩ := bind_ok ran
                  split at ran
                  · rename_i skippedPlace
                    obtain ⟨updated, stepsLoop, finished⟩ := bind_ok ran
                    have growth := route_receipts (owner := owner) (source := source)
                      (node := node) (assignment := assignment) (steps := route.steps) stepsLoop
                    refine ⟨_, (Except.ok.inj finished).symm, growth, ?_⟩
                    intro requested _concrete described nonempty
                    rw [described] at actualDescription
                    have same := Except.ok.inj actualDescription
                    subst route
                    have present : places.any (selects owner node assignment) = true := by
                      have notEmpty : requested.steps.isEmpty = false := List.isEmpty_eq_false_iff.mpr nonempty
                      change places.any (fun previous => decide
                        (previous.owner = owner ∧ previous.location = .occurrence node.id.occurrence ∧
                          previous.binder = assignment.target.root ∧ previous.missingType = none)) = true
                      simpa only [notEmpty, Bool.false_or] using skippedPlace
                    exact (receipt_of_any present).grows growth
                  · obtain ⟨reason, _generated, ran⟩ := bind_ok ran
                    try dsimp only [pure, Except.pure, bind, Except.bind] at ran
                    obtain ⟨updated, stepsLoop, finished⟩ := bind_ok ran
                    have growth := route_receipts (owner := owner) (source := source)
                      (node := node) (assignment := assignment) (steps := route.steps) stepsLoop
                    refine ⟨_, (Except.ok.inj finished).symm,
                      (Growth.mk ⟨[_], rfl⟩ ⟨[], (List.append_nil _).symm⟩).trans growth, ?_⟩
                    intro requested _concrete described _nonempty
                    rw [described] at actualDescription
                    have same := Except.ok.inj actualDescription
                    subst route
                    have created : Receipt owner node assignment (places ++ [⟨owner,
                      .occurrence node.id.occurrence, assignment.target.root, none, reason,
                      ⟨.invalidPlaceProjection, .occurrence node.id.occurrence, some node.span⟩⟩]) missing := by
                      apply receipt_of_any
                      simp [List.any_append, selects]
                    exact created.grows growth
                · rename_i skipped
                  refine ⟨_, (Except.ok.inj ran).symm, Growth.refl _ _, ?_⟩
                  intro route required
                  change concrete source assignment ≠ true at skipped
                  exact False.elim (skipped required)
            exact ⟨_, (Except.ok.inj finished).symm, assignments.1, assignments.2⟩
      exact ⟨_, (Except.ok.inj finished).symm, nodes.1, nodes.2⟩
  obtain ⟨extra, _extraAccepted, finished⟩ := bind_ok accepted
  have same := Except.ok.inj finished
  subst program
  obtain ⟨next, indices, places, missing, fixed⟩ := state
  have receipt := generated (owner, source) collected (.statement node) statement assignment target
    route gate described nonempty
  obtain ⟨entry, found⟩ := receipt.retained
  have selected := of_decide_eq_true (List.find?_some
    (p := fun previous : SourceCoreDataPlaceFaultSites.Site => decide
      (previous.owner = owner ∧ previous.location = .occurrence node.id.occurrence ∧
        previous.binder = assignment.target.root ∧ previous.missingType = none)) found)
  exact ⟨entry, List.mem_of_find?_eq_some found, selected.2.2.2, found, by
    unfold SourceCoreDataPlaceFaultSites.Program.placeReason
    change (match places.find? (selects owner node assignment) with
      | some candidate => candidate.reason | none => Word.zero) = entry.reason
    rw [found]⟩

end Solcore.SourceSemantics.CoreLowering.CompatiblePlaceProjectionDiagnosticCoverage
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatiblePublicDiagnosticPriority
/-! Actual preparation and table rebuilding retain the diagnostic priorities
for original reads and authenticated missing-default tokens. Source occurrence
association and successful public compiler preparation remain separate receipts. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePublicDiagnosticPriority
open Core Frontend SourceInference CompatiblePayload
open SourceCoreCompatibleDataPlaceFaultSites CompatiblePlaceMissingReservedReceipts
open CallableIndexedOwnedPublicFaultReceiverTables

/-- Rebuilding against the actual receiving registry cannot let an expanded
mapping diagnostic shadow an original read. -/
theorem read_extra_different {context : SourceCoreCompatibleDataPlaceFaultSites.Context}
    {plan : Plan} {root : Key} {program : SourceCoreCompatibleDataPlaceFaultSites.Program context}
    {base : SourceCoreProgramFaultSites.Program} {initialExtra : List (Word × Diagnostic)}
    (reserved : ReservedAt context plan root program base initialExtra)
    {registry : SourceCoreRawMetadata.Registry}
    {extension : SourceCoreRawMetadata.Extends program.context.registry registry}
    {table : SourceCoreFaultSites.Table} (rebuilt : program.tableForRegistry registry extension = .ok table)
    {read : SourceCoreFaultSites.ReadSite} (readMember : read ∈ base.rootTable.reads)
    {row : Word × Diagnostic} (origin : MissingDiagnosticOrigin registry program.missing row) :
    read.reason ≠ row.1 := by
  obtain ⟨site, siteMember, rawKey, rawValue, header, lookup, _keys, _values, within, token, _diagnostic⟩ :=
    origin.mapping_header
  have metadata : MetadataRep registry (.mapping rawKey rawValue) header := ⟨lookup⟩
  have limits : registry.limits.maxEntries = context.registry.limits.maxEntries :=
    congrArg SourceCoreRawMetadata.Limits.maxEntries extension.limits
  have bounded := Nat.le_trans (CompatiblePlaceMissingDiagnosticRows.metadata_headerBound metadata)
    (CompatiblePlaceMissingDiagnosticRows.tableForRegistry_budget rebuilt)
  have positive : 0 < header.val := by
    by_cases zero : header.val = 0
    · exact False.elim (metadata.nonzero (Fin.ext zero))
    · omega
  have number : (site.base.add header).val = site.base.val + header.val := by
    change (site.base.val + header.val) % wordModulus = site.base.val + header.val
    exact Nat.mod_eq_of_lt within
  intro same
  have equal := congrArg Fin.val (same.trans token.symm)
  rw [number] at equal
  have outside := reserved.readsOutside site siteMember read readMember
  rw [limits] at bounded
  rcases outside with before | after <;> omega

/-- The base producer's exact binder, occurrence and span remain selected
through the actual fixed prefix and receiving-registry expansion. -/
theorem read_diagnostic {context : SourceCoreCompatibleDataPlaceFaultSites.Context}
    {plan : Plan} {root : Key} {program : SourceCoreCompatibleDataPlaceFaultSites.Program context}
    {base : SourceCoreProgramFaultSites.Program} {initialExtra : List (Word × Diagnostic)}
    (reserved : ReservedAt context plan root program base initialExtra)
    {registry : SourceCoreRawMetadata.Registry}
    {extension : SourceCoreRawMetadata.Extends program.context.registry registry}
    {table : SourceCoreFaultSites.Table} (rebuilt : program.tableForRegistry registry extension = .ok table)
    {read : SourceCoreFaultSites.ReadSite} (member : read ∈ base.rootTable.reads) :
    table.diagnostic? read.reason = some {
      error := .uninitializedLocal read.binder
      site := .occurrence read.expression.occurrence
      span := some read.span } := by
  obtain ⟨positive, ordinary, _initialBoundary, found, _initialDecoded⟩ :=
    SourceCoreProgramFaultSites.prepare_read_diagnostic reserved.baseAccepted member
  obtain ⟨extra, _extraAccepted, actual, origins⟩ := program.tableForRegistry_receipt rebuilt
  have absent : (program.fixed ++ extra).find? (fun item => decide (item.1 = read.reason)) = none := by
    apply List.find?_eq_none.mpr
    intro row rowMember matched
    have same : read.reason = row.1 := (of_decide_eq_true matched).symm
    rcases List.mem_append.mp rowMember with fixed | missing
    · exact reserved.readSafe read member row fixed same
    · exact read_extra_different reserved rebuilt member (origins row missing) same
  rw [actual, reserved.sameRoot]
  exact SourceCoreFaultSites.Table.read_diagnostic positive ordinary absent found

/-- The actual reserved endpoint bounds every genuine receiving metadata
header, so its emitted missing-default token precedes the callable minimum. -/
theorem missing_token_below {context : SourceCoreCompatibleDataPlaceFaultSites.Context}
    {plan : Plan} {root : Key} {program : SourceCoreCompatibleDataPlaceFaultSites.Program context}
    {base : SourceCoreProgramFaultSites.Program} {initialExtra : List (Word × Diagnostic)}
    (reserved : ReservedAt context plan root program base initialExtra)
    {registry : SourceCoreRawMetadata.Registry}
    {extension : SourceCoreRawMetadata.Extends program.context.registry registry}
    {table : SourceCoreFaultSites.Table} (rebuilt : program.tableForRegistry registry extension = .ok table)
    {site : MissingSite} (member : site ∈ program.missing)
    {rawKey rawValue : TypeSystem.Ty} {header : Word}
    (metadata : MetadataRep registry (.mapping rawKey rawValue) header) :
    (site.base.add header).val < program.nextReason := by
  have limits : registry.limits.maxEntries = context.registry.limits.maxEntries :=
    congrArg SourceCoreRawMetadata.Limits.maxEntries extension.limits
  have bounded := Nat.le_trans (CompatiblePlaceMissingDiagnosticRows.metadata_headerBound metadata)
    (CompatiblePlaceMissingDiagnosticRows.tableForRegistry_budget rebuilt)
  rw [limits] at bounded
  rw [token_nonWrapping _ _ _ (reserved.legacy.1.reserved site member) bounded]
  have below := reserved.missingBelow site member
  omega

/-- Public fault observation uses the actual rebuilt base and the actual
callable allocation at the preparation's final reason boundary. -/
theorem receiver_read_diagnostic {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver prepared}
    (receiver : IssuedAt prepared completion.entry completion.result.context.registry
      completion.result.extension completion.result.diagnostics)
    {plan : Plan} {root : Key} {sources : List (Key × TypedSource)}
    {issued : SourceCoreCompatibleDataPlaceFaultSites.Program (SourceCoreCompatibleValues.Context.initial checked)}
    (accepted : SourceCoreCompatibleDataPlaceFaultSites.prepare (SourceCoreCompatibleValues.Context.initial checked)
      plan root sources = .ok issued)
    (present : prepared.base.diagnostics = some issued)
    {callablePlan : SourceCoreStageCodebook.Plan} {contracts : SourceCoreStageCodebook.Table}
    {callable : SourceCoreCallableFaultSites.Program}
    (allocated : SourceCoreCallableFaultSites.prepare callablePlan contracts issued.program.rootTable issued.nextReason = .ok callable)
    (callablePresent : prepared.base.callableDiagnostics = some callable)
    {read : SourceCoreFaultSites.ReadSite} (member : read ∈ issued.program.rootTable.reads) :
    completion.result.diagnostics.diagnostic? read.reason = some {
      error := .uninitializedLocal read.binder
      site := .occurrence read.expression.occurrence
      span := some read.span } := by
  obtain ⟨actual, rebuilt, table⟩ := receiver
  rw [present] at rebuilt
  obtain ⟨base, extra, reserved⟩ := CompatiblePlaceMissingPreparationRanges.prepare_reserved_receipt accepted
  have member : read ∈ base.rootTable.reads := by simpa only [reserved.sameRoot] using member
  rw [table, CompatibleCallableDiagnosticBounds.append_diagnostic allocated callablePresent
    (reserved.readsBelow read member)]
  exact read_diagnostic reserved rebuilt member

/-- A genuine missing site and raw metadata retain their error through the
same public receiver. Duplicate tokens keep the producer's selected span. -/
theorem receiver_missing_diagnostic {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver prepared}
    (receiver : IssuedAt prepared completion.entry completion.result.context.registry
      completion.result.extension completion.result.diagnostics)
    {plan : Plan} {root : Key} {sources : List (Key × TypedSource)}
    {issued : SourceCoreCompatibleDataPlaceFaultSites.Program (SourceCoreCompatibleValues.Context.initial checked)}
    (accepted : SourceCoreCompatibleDataPlaceFaultSites.prepare (SourceCoreCompatibleValues.Context.initial checked)
      plan root sources = .ok issued)
    (present : prepared.base.diagnostics = some issued)
    {callablePlan : SourceCoreStageCodebook.Plan} {contracts : SourceCoreStageCodebook.Table}
    {callable : SourceCoreCallableFaultSites.Program}
    (allocated : SourceCoreCallableFaultSites.prepare callablePlan contracts issued.program.rootTable issued.nextReason = .ok callable)
    (callablePresent : prepared.base.callableDiagnostics = some callable)
    {site : MissingSite} (member : site ∈ issued.missing)
    {rawKey rawValue : TypeSystem.Ty} {header : Word}
    (metadata : MetadataRep completion.result.context.registry (.mapping rawKey rawValue) header)
    (keyView : SourceCoreRawMetadata.runtimeType rawKey = SourceCoreRawMetadata.runtimeType site.keyType)
    (valueView : SourceCoreRawMetadata.runtimeType rawValue = SourceCoreRawMetadata.runtimeType site.valueType) :
    ∃ diagnostic, completion.result.diagnostics.diagnostic? (site.base.add header) = some diagnostic ∧
      diagnostic.error = .typeMismatch rawValue none := by
  obtain ⟨actual, rebuilt, table⟩ := receiver
  rw [present] at rebuilt
  obtain ⟨base, extra, reserved⟩ := CompatiblePlaceMissingPreparationRanges.prepare_reserved_receipt accepted
  rw [table, CompatibleCallableDiagnosticBounds.append_diagnostic allocated callablePresent
    (missing_token_below reserved rebuilt member metadata)]
  exact CompatiblePlaceMissingPreparationRanges.table_diagnostic accepted rebuilt member metadata keyView valueView

end Solcore.SourceSemantics.CoreLowering.CompatiblePublicDiagnosticPriority
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatiblePublicCallableAllocationReceipts
/-! The actual compatible factory retains its optional callable allocation.
Sealed compilation supplies the producer receipts used by decoder priority;
the selected Source occurrence remains an independent authentic receipt. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePublicCallableAllocationReceipts
open Core Frontend SourceInference
open CallableIndexedOwnedPublicFaultReceiverTables

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β}
    {value : β} (accepted : action >>= next = .ok value) :
    ∃ intermediate, action = .ok intermediate ∧ next intermediate = .ok value := by
  cases action with
  | error error => cases accepted
  | ok intermediate => exact ⟨intermediate, rfl, accepted⟩

private theorem mapError_ok {α ε δ : Type} {action : Except ε α} {f : ε → δ} {value : α}
    (accepted : action.mapError f = .ok value) : action = .ok value := by
  cases action <;> cases accepted <;> rfl

/-- Optional absence and actual checked allocation retain their original cases. -/
def AllocationAt {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCompatibleFunctions.Prepared checked)
    (issued : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial checked)) : Prop :=
  match prepared.callableDiagnostics with
  | none => True
  | some callable => ∃ contracts, SourceCoreCallableFaultSites.prepare prepared.plan contracts
      issued.program.rootTable issued.nextReason = .ok callable

theorem of_catalog {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {checked : SourceCoreCompatibleCatalog.Checked} {ownership : checked.signatures = program.signatures}
    {fuel : Nat} {prepared : SourceCoreCompatibleFunctions.Prepared checked}
    {issued : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial checked)}
    (accepted : SourceCoreCompatibleFunctions.prepareWithCatalog program plan checked ownership fuel = .ok prepared)
    (present : prepared.diagnostics = some issued) : AllocationAt prepared issued := by
  unfold SourceCoreCompatibleFunctions.prepareWithCatalog at accepted
  obtain ⟨executable, _, accepted⟩ := bind_ok accepted
  obtain ⟨locals0, _, accepted⟩ := bind_ok accepted
  obtain ⟨contexts, _, accepted⟩ := bind_ok accepted
  obtain ⟨functions, _, accepted⟩ := bind_ok accepted
  split at accepted
  · cases accepted
    cases present
  · obtain ⟨diagnostics, _, accepted⟩ := bind_ok accepted
    split at accepted
    · obtain ⟨contracts, _, accepted⟩ := bind_ok accepted
      obtain ⟨callable, allocated, accepted⟩ := bind_ok accepted
      simp only [pure, Except.pure, bind, Except.bind] at accepted
      obtain ⟨locals, _, accepted⟩ := bind_ok accepted
      obtain ⟨closures, _, accepted⟩ := bind_ok accepted
      obtain ⟨sourceInputs, _, accepted⟩ := bind_ok accepted
      obtain ⟨entries, _, accepted⟩ := bind_ok accepted
      cases accepted
      cases present
      exact ⟨contracts, mapError_ok allocated⟩
    · simp only [pure, Except.pure, bind, Except.bind] at accepted
      obtain ⟨closures, _, accepted⟩ := bind_ok accepted
      obtain ⟨sourceInputs, _, accepted⟩ := bind_ok accepted
      obtain ⟨entries, _, accepted⟩ := bind_ok accepted
      cases accepted
      trivial

theorem of_automatic {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan} {fuel : Nat}
    {automatic : SourceCoreCompatibleFunctions.Automatic}
    {issued : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial automatic.checked)}
    (accepted : SourceCoreCompatibleFunctions.prepare program plan fuel = .ok automatic)
    (present : automatic.prepared.diagnostics = some issued) : AllocationAt automatic.prepared issued := by
  unfold SourceCoreCompatibleFunctions.prepare at accepted
  obtain ⟨executable, _, accepted⟩ := bind_ok accepted
  obtain ⟨locals, _, accepted⟩ := bind_ok accepted
  dsimp only at accepted
  split at accepted
  · cases accepted
  · obtain ⟨base, made, accepted⟩ := bind_ok accepted
    cases accepted
    exact of_catalog made present

theorem of_compiled (compiled : SourceCoreUnifiedCompilation.Compiled)
    {issued : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked)}
    (present : compiled.indexed.base.diagnostics = some issued) : AllocationAt compiled.indexed.base issued := by
  rw [SourceCoreUnifiedPreparationCertificates.indexed_base compiled.indexedPrepared] at present ⊢
  exact of_automatic compiled.compatiblePrepared present

/-- A token below the real producer endpoint stays below an actual callable
allocation, including the genuine absent-table case. -/
theorem AllocationAt.below {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
    {issued : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial checked)}
    (allocation : AllocationAt prepared.base issued) {token : Word}
    (below : token.val < issued.nextReason) : BelowCallable prepared token := by
  cases present : prepared.base.callableDiagnostics with
  | none => simp only [BelowCallable, present]
  | some callable =>
    obtain ⟨contracts, allocated⟩ := (by simpa only [AllocationAt, present] using allocation :
      ∃ contracts, SourceCoreCallableFaultSites.prepare prepared.base.plan contracts
        issued.program.rootTable issued.nextReason = .ok callable)
    exact (by simpa only [BelowCallable, present] using
      CompatibleCallableDiagnosticBounds.below_unknown allocated below)

/-- Actual sealed compilation discharges diagnostic and callable preparation;
the member is still the genuine issued read selected by its Source adapter. -/
theorem receiver_read_diagnostic (compiled : SourceCoreUnifiedCompilation.Compiled)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
      completion.result.extension completion.result.diagnostics)
    {issued : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked)}
    (present : compiled.indexed.base.diagnostics = some issued)
    {read : SourceCoreFaultSites.ReadSite} (member : read ∈ issued.program.rootTable.reads) :
    completion.result.diagnostics.diagnostic? read.reason = some {
      error := .uninitializedLocal read.binder
      site := .occurrence read.expression.occurrence
      span := some read.span } := by
  obtain ⟨root, sources, accepted⟩ := CallableIndexedOwnedPublicDiagnosticReceipts.compiled_diagnostics compiled present
  obtain ⟨base, extra, reserved⟩ := CompatiblePlaceMissingPreparationRanges.prepare_reserved_receipt accepted
  have actualMember : read ∈ base.rootTable.reads := by simpa only [reserved.sameRoot] using member
  obtain ⟨actual, rebuilt, table⟩ := receiver
  rw [present] at rebuilt
  rw [table, appendCallable_diagnostic_of_below ((of_compiled compiled present).below
    (reserved.readsBelow read actualMember))]
  exact CompatiblePublicDiagnosticPriority.read_diagnostic reserved rebuilt actualMember

/-- The same factory receipts preserve the raw missing-default error. The
actual selected MissingSite and receiving metadata remain required. -/
theorem receiver_missing_diagnostic (compiled : SourceCoreUnifiedCompilation.Compiled)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
      completion.result.extension completion.result.diagnostics)
    {issued : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked)}
    (present : compiled.indexed.base.diagnostics = some issued)
    {site : SourceCoreCompatibleDataPlaceFaultSites.MissingSite} (member : site ∈ issued.missing)
    {rawKey rawValue : TypeSystem.Ty} {header : Word}
    (metadata : CompatiblePayload.MetadataRep completion.result.context.registry (.mapping rawKey rawValue) header)
    (keyView : SourceCoreRawMetadata.runtimeType rawKey = SourceCoreRawMetadata.runtimeType site.keyType)
    (valueView : SourceCoreRawMetadata.runtimeType rawValue = SourceCoreRawMetadata.runtimeType site.valueType) :
    ∃ diagnostic, completion.result.diagnostics.diagnostic? (site.base.add header) = some diagnostic ∧
      diagnostic.error = .typeMismatch rawValue none := by
  obtain ⟨root, sources, accepted⟩ := CallableIndexedOwnedPublicDiagnosticReceipts.compiled_diagnostics compiled present
  obtain ⟨base, extra, reserved⟩ := CompatiblePlaceMissingPreparationRanges.prepare_reserved_receipt accepted
  obtain ⟨actual, rebuilt, table⟩ := receiver
  rw [present] at rebuilt
  rw [table, appendCallable_diagnostic_of_below ((of_compiled compiled present).below
    (CompatiblePublicDiagnosticPriority.missing_token_below reserved rebuilt member metadata))]
  exact CompatiblePlaceMissingPreparationRanges.table_diagnostic accepted rebuilt member metadata keyView valueView

end Solcore.SourceSemantics.CoreLowering.CompatiblePublicCallableAllocationReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatiblePublicContextualDiagnosticObservations
/-! Finite public decoder compositions use the actual contextual source
inventory and receiving table. Primitive failure paths and reached heap
associations remain independent receipts. Issuer raw types are retained. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePublicContextualDiagnosticObservations
open Core Frontend SourceInference
open CallableIndexedOwnedPublicFaultReceiverTables
open CallableIndexedOwnedContextualDiagnosticSources

abbrev Key := SourceSpecialization.SpecializationKey

/-- A genuine canonical local occurrence uses its actual globally issued read
token. The sealed factory supplies contextual no-index priority and the actual
receiving table supplies the same binder, occurrence and span. -/
theorem receiver_local_read_diagnostic (compiled : SourceCoreUnifiedCompilation.Compiled)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
      completion.result.extension completion.result.diagnostics)
    {issued : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked)}
    (present : compiled.indexed.base.diagnostics = some issued)
    {owner : Key} {row : SourceSpecialization.SpecializedFunction}
    (record : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan owner = .ok row)
    (unique : SourceSemantics.NodeOccurrencesUnique row.function.typedBody)
    {id : ExpressionId} {node : ExpressionNode} {name : String} {binder : Resolved.LocalId}
    (contains : SourceSemantics.ContainsExpression row.function.typedBody id node)
    (form : node.form = .reference name (.local binder))
    {own : SourceCoreProgramFaultSites.Function}
    (ownFound : issued.program.base.find? owner = some own) :
    ∃ read : SourceCoreFaultSites.ReadSite,
      read.expression = id ∧ read.binder = binder ∧ read.span = node.span ∧
      issued.program.reasonAt owner id = read.reason ∧
      read ∈ issued.program.rootTable.reads ∧
      completion.result.diagnostics.diagnostic? read.reason = some {
        error := .uninitializedLocal binder
        site := .occurrence id.occurrence
        span := some node.span } := by
  have factory := CallableIndexedOwnedContextualDiagnosticSources.of_compiled compiled present
  have noIndex := CompatibleContextualDiagnosticIndexOrigins.FactoryAt.no_index_at_read
    factory record unique contains form
  obtain ⟨locals0, root, remaining, _roots, _contexts, accepted⟩ := factory.actual
  obtain ⟨base, extra, reserved⟩ := CompatiblePlaceMissingPreparationRanges.prepare_reserved_receipt accepted
  have baseAccepted := CallableIndexedOwnedPublicDiagnosticReceipts.data_place_base accepted
  obtain ⟨read, _ownRead, expression, binderEq, spanEq, ownReason, rootMember,
    _positive, _ordinary, _noAdditional, _byReason, _baseDecoded⟩ :=
    SourceCoreProgramFaultSites.prepare_local_read baseAccepted record ownFound contains.1 form
  have expressionEq : read.expression = id := expression.trans contains.2
  have sameExpressionBase : issued.program.expressions.base = issued.program.base :=
    reserved.sameExpressionBase.trans reserved.sameBase.symm
  have token : issued.program.reasonAt owner id = read.reason := by
    unfold SourceCoreDataPlaceFaultSites.Program.reasonAt SourceCoreDataFaultSites.Program.reasonAt
    rw [noIndex, sameExpressionBase, ownFound]
    simpa only [contains.2] using ownReason
  have readsSame : issued.program.rootTable.reads = issued.program.base.rootTable.reads := by
    rw [reserved.sameRoot, reserved.sameBase]
  have member : read ∈ issued.program.rootTable.reads := by rw [readsSame]; exact rootMember
  have decoded := CompatiblePublicCallableAllocationReceipts.receiver_read_diagnostic
    compiled receiver present member
  exact ⟨read, expressionEq, binderEq, spanEq, token, member,
    by simpa only [expressionEq, binderEq, spanEq] using decoded⟩

/-- The selected index retains its literal issuer independently of missing
mapping metadata and decoding. The actual provider base equals the invoked
reason; no decoded span or issuer raw type equality is inferred. -/
theorem receiver_index_missing_diagnostic (compiled : SourceCoreUnifiedCompilation.Compiled)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
      completion.result.extension completion.result.diagnostics)
    {issued : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked)}
    (present : compiled.indexed.base.diagnostics = some issued)
    {owner : Key} {row : SourceSpecialization.SpecializedFunction}
    (record : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan owner = .ok row)
    (unique : SourceSemantics.NodeOccurrencesUnique row.function.typedBody)
    {node : ExpressionNode} {base key : ExpressionId}
    (contains : SourceSemantics.ContainsExpression row.function.typedBody node.id node)
    (form : node.form = .index base key)
    {missing : SourceCoreCompatibleDataPlaceFaultSites.MissingSite}
    (member : missing ∈ issued.missing)
    (providerBase : missing.base = issued.program.reasonAt owner node.id)
    {rawKey rawValue : TypeSystem.Ty} {header : Word}
    (metadata : CompatiblePayload.MetadataRep completion.result.context.registry
      (.mapping rawKey rawValue) header)
    (keyView : SourceCoreRawMetadata.runtimeType rawKey = SourceCoreRawMetadata.runtimeType missing.keyType)
    (valueView : SourceCoreRawMetadata.runtimeType rawValue = SourceCoreRawMetadata.runtimeType missing.valueType) :
    ∃ site : SourceCoreDataFaultSites.IndexSite,
      issued.program.expressions.indices.find?
        (fun candidate => decide (candidate.owner = owner ∧ candidate.expression = node.id)) = some site ∧
      site.owner = owner ∧ site.expression = node.id ∧
      issued.program.reasonAt owner node.id = site.reason ∧
      (∃ actual issuer actualBase actualKey,
        (owner, actual) ∈ (compiled.indexed.base.plan.specializations.map
          (fun row => (row.key, row.function.typedBody)) ++
          compiled.indexed.base.contexts.map (fun item => (item.caller.key, item.source))) ∧
        actual.owner = owner.declaration ∧ SourceSemantics.ContainsExpression actual node.id issuer ∧
        issuer.form = .index actualBase actualKey ∧ node.form = .index actualBase actualKey ∧
        issuer.span = node.span ∧
        site.diagnostic = ⟨.typeMismatch issuer.type none, .occurrence node.id.occurrence, some node.span⟩) ∧
      ∃ diagnostic,
        completion.result.diagnostics.diagnostic? (site.reason.add header) = some diagnostic ∧
        diagnostic.error = .typeMismatch rawValue none := by
  have factory := CallableIndexedOwnedContextualDiagnosticSources.of_compiled compiled present
  obtain ⟨site, found, ownerEq, expressionEq, origin⟩ :=
    CompatibleContextualDiagnosticIndexOrigins.FactoryAt.index_selected_origin
      factory record unique contains form
  have reason : issued.program.reasonAt owner node.id = site.reason := by
    unfold SourceCoreDataPlaceFaultSites.Program.reasonAt SourceCoreDataFaultSites.Program.reasonAt
    rw [found]
  obtain ⟨diagnostic, decoded, error⟩ :=
    CompatiblePublicCallableAllocationReceipts.receiver_missing_diagnostic
      compiled receiver present member metadata keyView valueView
  have baseEq : missing.base = site.reason := providerBase.trans reason
  exact ⟨site, found, ownerEq, expressionEq, reason, origin, diagnostic,
    by simpa only [baseEq] using decoded, error⟩

end Solcore.SourceSemantics.CoreLowering.CompatiblePublicContextualDiagnosticObservations
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatiblePublicContextualMissingDiagnosticObservations
/-! Actual canonical missing rows identify the first received diagnostic's
occurrence and span. Raw receiving metadata and its canonical base view remain
independent certificates. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePublicContextualMissingDiagnosticObservations
open Core Frontend SourceInference CompatiblePayload
open SourceCoreCompatibleDataPlaceFaultSites
open CompatibleExpressionMissingSourceReceipts
open CallableIndexedOwnedContextualDiagnosticSources
open CallableIndexedOwnedPublicFaultReceiverTables

abbrev Key := SourceSpecialization.SpecializationKey

/-- This is the genuine base lookup and raw mapping view at the canonical
Source. Receiving metadata does not supply this association. -/
def CanonicalMappingView (source : TypedSource) (base : ExpressionId)
    (rawKey rawValue : TypeSystem.Ty) : Prop :=
  ∃ node, source.lookupExpression? base = some node ∧
    SourceCoreRawMetadata.runtimeType node.type =
      .mapping (SourceCoreRawMetadata.runtimeType rawKey) (SourceCoreRawMetadata.runtimeType rawValue)

/-- The same accepted suffix and actual canonical lookup supply its two
runtime views, preserving the independent receiving raw types. -/
theorem ExpressionAt.receiving_views {indices : List SourceCoreDataFaultSites.IndexSite}
    {owner : Key} {source : TypedSource} {node : ExpressionNode} {missing : MissingSite}
    (receipt : ExpressionAt indices owner source node missing)
    {base key : ExpressionId} (form : node.form = .index base key)
    {rawKey rawValue : TypeSystem.Ty} (view : CanonicalMappingView source base rawKey rawValue) :
    SourceCoreRawMetadata.runtimeType rawKey = SourceCoreRawMetadata.runtimeType missing.keyType ∧
    SourceCoreRawMetadata.runtimeType rawValue = SourceCoreRawMetadata.runtimeType missing.valueType := by
  obtain ⟨actualBase, actualKey, baseNode, keyType, valueType, selected,
    actualForm, found, mappingView, valueView, _selected, rowEq⟩ := receipt
  obtain ⟨rfl, rfl⟩ := ExpressionForm.index.inj (actualForm.symm.trans form)
  obtain ⟨canonicalBase, canonicalFound, canonicalView⟩ := view
  have sameNode := Option.some.inj (found.symm.trans canonicalFound)
  subst canonicalBase
  have components := TypeSystem.Ty.mapping.inj (mappingView.symm.trans canonicalView)
  rw [rowEq]
  refine ⟨?_, components.2.symm.trans valueView.symm⟩
  rw [components.1]
  exact (SourceCoreRawMetadata.runtimeType_idempotent rawKey).symm

/-- The actual FIRST matching row is an expanded missing row. Its genuine
Source ownership identifies the exact occurrence and span. -/
theorem FactoryAt.table_expression_missing_diagnostic
    {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : SourceCoreCompatibleFunctions.Prepared checked}
    {issued : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial checked)}
    (factory : FactoryAt prepared issued) {owner : Key} {function : SourceSpecialization.SpecializedFunction}
    (record : SourceCompilationPlan.exactSpecialization prepared.plan owner = .ok function)
    (unique : NodeOccurrencesUnique function.function.typedBody)
    {node : ExpressionNode} {base key : ExpressionId}
    (contains : ContainsExpression function.function.typedBody node.id node)
    (form : node.form = .index base key)
    {registry : SourceCoreRawMetadata.Registry} {rawKey rawValue : TypeSystem.Ty} {header : Word}
    (view : CanonicalMappingView function.function.typedBody base rawKey rawValue)
    {extension : SourceCoreRawMetadata.Extends issued.context.registry registry}
    {table : SourceCoreFaultSites.Table} (rebuilt : issued.tableForRegistry registry extension = .ok table)
    (metadata : MetadataRep registry (.mapping rawKey rawValue) header) :
    ∃ missing, missing ∈ issued.missing ∧
      ExpressionAt issued.program.expressions.indices owner function.function.typedBody node missing ∧
      missing.base = issued.program.reasonAt owner node.id ∧
      table.diagnostic? (missing.base.add header) = some {
        error := .typeMismatch rawValue none,
        site := .occurrence node.id.occurrence, span := some node.span } := by
  obtain ⟨missing, member, receipt, providerBase⟩ :=
    CompatibleContextualDiagnosticMissingOrigins.FactoryAt.expression_missing_at factory record contains form
  obtain ⟨keyView, valueView⟩ := ExpressionAt.receiving_views receipt form view
  obtain ⟨locals0, root, remaining, _roots, _contexts, accepted⟩ := factory.actual
  obtain ⟨ranges, positive, fixed, escaped⟩ := CompatiblePlaceMissingPreparationRanges.prepare_ranges accepted
  have limits : registry.limits.maxEntries =
      (SourceCoreCompatibleValues.Context.initial checked).registry.limits.maxEntries :=
    congrArg SourceCoreRawMetadata.Limits.maxEntries extension.limits
  have actualRanges : CompatiblePlaceMissingDiagnosticAssociation.Ranges registry.limits.maxEntries issued.missing :=
    limits.symm ▸ ranges
  have budget := CompatiblePlaceMissingDiagnosticRows.tableForRegistry_budget rebuilt
  have bounded := Nat.le_trans (CompatiblePlaceMissingDiagnosticRows.metadata_headerBound metadata) budget
  have reserved := actualRanges.reserved missing member
  obtain ⟨cover, coverMember, coverToken, _coverOrigin⟩ :=
    CompatiblePlaceMissingDiagnosticRows.tableForRegistry_contains rebuilt member metadata keyView valueView reserved
  have covered : (table.additional.find? (fun candidate => decide (candidate.1 = missing.base.add header))).isSome := by
    apply List.find?_isSome.mpr
    exact ⟨cover, coverMember, by simp only [coverToken, decide_true]⟩
  have sameEscape : table.escapedReason = issued.program.rootTable.escapedReason := by
    obtain ⟨extra, _produced, tableEq, _origins⟩ := issued.tableForRegistry_receipt rebuilt
    rw [tableEq]
  have number := SourceCoreCompatibleDataPlaceFaultSites.token_nonWrapping
    missing.base header registry.limits.maxEntries reserved bounded
  have headerPositive : 0 < header.val := by
    by_cases zero : header.val = 0
    · exact False.elim (metadata.nonzero (Fin.ext zero))
    · omega
  have nonzero : missing.base.add header ≠ Word.zero := by
    intro zero
    have numbers := congrArg Fin.val zero
    rw [number] at numbers
    change missing.base.val + header.val = 0 at numbers
    omega
  have ordinary : missing.base.add header ≠ table.escapedReason := by
    intro same
    have numbers := congrArg Fin.val same
    rw [number, sameEscape] at numbers
    have separated := escaped missing member
    rw [← limits] at separated
    rcases separated with before | after <;> omega
  cases found : table.additional.find? (fun candidate => decide (candidate.1 = missing.base.add header)) with
  | none => simp only [found, Option.isSome_none, Bool.false_eq_true] at covered
  | some selected =>
    have selectedMember := List.mem_of_find?_eq_some found
    have selectedToken : selected.1 = missing.base.add header :=
      of_decide_eq_true (List.find?_some
        (p := fun candidate : Word × Diagnostic => decide (candidate.1 = missing.base.add header)) found)
    have origin : CompatiblePlaceMissingDiagnosticRows.MissingRow registry issued.missing selected := by
      rcases CompatiblePlaceMissingDiagnosticRows.tableForRegistry_rows rebuilt selectedMember with old | missingRow
      · exact False.elim (CompatiblePlaceMissingDiagnosticAssociation.fixed_different metadata budget reserved
          (by simpa only [limits] using fixed missing member selected old) selectedToken)
      · exact missingRow
    have fields := CompatibleContextualDiagnosticMissingOrigins.FactoryAt.expanded_row_fields
      factory record unique contains member receipt limits budget metadata origin selectedToken
    have diagnosticEq : selected.2 = {
        error := .typeMismatch rawValue none,
        site := .occurrence node.id.occurrence, span := some node.span } := by
      cases actual : selected.2 with
      | mk error site span =>
        rw [actual] at fields
        obtain ⟨rfl, rfl, rfl⟩ := fields
        rfl
    refine ⟨missing, member, receipt, providerBase, ?_⟩
    simp only [SourceCoreFaultSites.Table.diagnostic?, nonzero, ordinary, found, if_false]
    exact congrArg some diagnosticEq

/-- Sealed compilation supplies actual contextual preparation and callable
allocation. The canonical row and its base are derived internally. -/
theorem receiver_index_missing_diagnostic (compiled : SourceCoreUnifiedCompilation.Compiled)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
      completion.result.extension completion.result.diagnostics)
    {issued : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked)}
    (present : compiled.indexed.base.diagnostics = some issued)
    {owner : Key} {function : SourceSpecialization.SpecializedFunction}
    (record : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan owner = .ok function)
    (unique : NodeOccurrencesUnique function.function.typedBody)
    {node : ExpressionNode} {base key : ExpressionId}
    (contains : ContainsExpression function.function.typedBody node.id node)
    (form : node.form = .index base key)
    {rawKey rawValue : TypeSystem.Ty} {header : Word}
    (view : CanonicalMappingView function.function.typedBody base rawKey rawValue)
    (metadata : MetadataRep completion.result.context.registry (.mapping rawKey rawValue) header) :
    completion.result.diagnostics.diagnostic? ((issued.program.reasonAt owner node.id).add header) = some {
      error := .typeMismatch rawValue none,
      site := .occurrence node.id.occurrence, span := some node.span } := by
  have factory := CallableIndexedOwnedContextualDiagnosticSources.of_compiled compiled present
  have allocation := CompatiblePublicCallableAllocationReceipts.of_compiled compiled present
  obtain ⟨actual, rebuilt, tableEq⟩ := receiver
  rw [present] at rebuilt
  obtain ⟨missing, member, _receipt, providerBase, decoded⟩ :=
    FactoryAt.table_expression_missing_diagnostic factory record unique contains form view rebuilt metadata
  obtain ⟨locals0, root, remaining, _roots, _contexts, accepted⟩ := factory.actual
  obtain ⟨baseProgram, extra, reserved⟩ := CompatiblePlaceMissingPreparationRanges.prepare_reserved_receipt accepted
  have below : BelowCallable compiled.indexed ((issued.program.reasonAt owner node.id).add header) := by
    simpa only [providerBase] using allocation.below
      (CompatiblePublicDiagnosticPriority.missing_token_below reserved rebuilt member metadata)
  rw [tableEq, appendCallable_diagnostic_of_below below]
  simpa only [providerBase] using decoded

end Solcore.SourceSemantics.CoreLowering.CompatiblePublicContextualMissingDiagnosticObservations
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicReadFaultObservation
/-! An ordinary read observation keeps the actual Source location and the
binder selected by the same read certificate. The receiver is the real indexed
completion table, rebuilt at its own registry. Issuer lookup, priority and range
receipts remain explicit until their genuine preparation producers supply them.
This packet is indexed by the reached heap; it defines no blanket FaultRep.
The whole Source failure and primitive read receipt are retained independently.
Their occurrence path through the whole fault must come from the existing
semantic fold; same-location equality alone does not identify that path. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicReadFaultObservation
open Core Frontend SourceInference GeneralHeap CompatibleExpressionReads CompatiblePayload
open CallableIndexedOwnedPublicFaultObservation CallableIndexedOwnedPublicFaultReceiverTables

variable {checked : SourceCoreCompatibleCatalog.Checked}
  {nativeProgram : SourceCoreUnifiedRuntime.Program checked}
  {prepared : SourceCoreUnifiedRuntime.Prepared nativeProgram}
  (execution : SourceCoreUnifiedRuntime.Execution prepared)
  {ambient : AmbientDefinitions checked.catalog.definitions}
  {functions : FunctionModel checked.catalog ambient}
  {program : SourceSemantics.Program} {entry : Dynamic.ProgramEntry}
  {before after : Dynamic.Heap} {mapping : LocationMap} {world : StoreTyping}
  {location : Dynamic.Location} {cell : Dynamic.Cell} {store : Store}
  {fuel : Nat} {values : ValuesContext} {source : TypedSource} {scope : Scope}
  {id : ExpressionId} {reason : Word} {code : Expr}
  (certificate : CompatibleExpressionReads.Certificate fuel values source scope id reason code)
  (context : SourceSemantics.Context) (environment : Dynamic.Environment)
  (site : SourceCoreFaultSites.ReadSite)

/-- The observation retains the exact read witness at the original fault's
reached heap. Its binder, occurrence and span are the issued diagnostic row. -/
structure Packet
    (functions : FunctionModel checked.catalog ambient)
    (program : SourceSemantics.Program) (entry : Dynamic.ProgramEntry)
    (before after : Dynamic.Heap) (mapping : LocationMap) (world : StoreTyping)
    (location : Dynamic.Location) (cell : Dynamic.Cell) (store : Store) : Prop where
  observation : CallableIndexedOwnedPublicFaultObservation.Packet execution
    (CompatibleHeap.payloadModel checked execution.completion.result.context.registry functions) program entry
    before after (.uninitializedLocation location) mapping world site.reason store {
      error := .uninitializedLocal site.binder
      site := .occurrence site.expression.occurrence
      span := some site.span}
  read : CompatibleExpressionReads.UninitializedWitness certificate context environment after location cell
  checkedExact : values.checked = checked
  ambientExact : ambient.definitions = nativeProgram.layouts.definitions
  expression : site.expression = id
  binder : site.binder = certificate.binder
  span : site.span = certificate.node.span
  token : site.reason = reason

/-- Actual base preparation and the actual completion's issued table derive
the decoder equation internally. The Source failure and read witness still
retain their same location and heap, and native failure retains its real store. -/
theorem packet_of_issued
    (sourceFault : Dynamic.ProgramFaults program entry before (.uninitializedLocation location) after)
    (reachedHeap : CompatibleHeap.HeapRepresents checked execution.completion.result.context.registry
      functions mapping world after store)
    (nativeFault : execution.completion.result.native.observation = .failed site.reason store)
    (read : CompatibleExpressionReads.UninitializedWitness certificate context environment after location cell)
    (checkedExact : values.checked = checked)
    (ambientExact : ambient.definitions = nativeProgram.layouts.definitions)
    (expression : site.expression = id) (binder : site.binder = certificate.binder)
    (span : site.span = certificate.node.span) (token : site.reason = reason)
    (receiver : IssuedAt nativeProgram execution.completion.entry
      execution.completion.result.context.registry execution.completion.result.extension
      execution.completion.result.diagnostics)
    {issued : SourceCoreCompatibleDataPlaceFaultSites.Program (SourceCoreCompatibleValues.Context.initial checked)}
    (present : nativeProgram.base.diagnostics = some issued)
    {base : SourceCoreFaultSites.Table}
    (rebuilt : issued.tableForRegistry execution.completion.result.context.registry
      execution.completion.result.extension = .ok base)
    (positive : site.reason ≠ Word.zero) (ordinary : site.reason ≠ base.escapedReason)
    (noBoundary : base.additional.find? (fun candidate => decide (candidate.1 = site.reason)) = none)
    (found : base.reads.find? (fun candidate => decide (candidate.reason = site.reason)) = some site)
    (below : BelowCallable nativeProgram site.reason) :
    Packet execution certificate context environment site functions program entry before after mapping world location cell store := by
  have decoded := read_diagnostic_of_issued receiver present rebuilt positive ordinary noBoundary found below
  exact ⟨⟨sourceFault, reachedHeap, nativeFault, decoded⟩,
    read, checkedExact, ambientExact, expression, binder, span, token⟩

/-- The real read packet survives public observation beside the exact exported
heap. Export acceptance is independent of Source/native heap representation;
no equality between the two heap formats is inferred here. -/
theorem Packet.observe
    (packet : Packet execution certificate context environment site functions program entry before after mapping world location cell store)
    {exportFuel : Option Nat}
    {exported : SourceCoreCallableIndexedHeapOutputs.Export prepared.output
      execution.completion execution.initial.heap}
    (heapExport : SourceCoreCallableIndexedHeapOutputs.exportHeap prepared.output
      execution.completion execution.initial.heap
      (exportFuel.getD execution.exportFuel) = .ok exported) :
    Packet execution certificate context environment site functions program entry before after mapping world location cell store ∧
      execution.observe exportFuel = .ok (.fault (.uninitializedLocal site.binder) ⟨exported.heap⟩) :=
  ⟨packet, CallableIndexedOwnedPublicFaultObservation.observe_failed execution heapExport
    packet.observation.nativeFault packet.observation.decoded⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicReadFaultObservation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatiblePlaceMissingPreparedDiagnostics
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleSessionContextualDiagnosticObservations
/-! The Session table receipt retains its actual raw registry and filtered
callable append. Static factory authority follows from the artifact's genuine
sealed compiler in a proof goal. Primitive paths and heap associations remain
independent receipts. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleSessionContextualDiagnosticObservations
open Core Frontend SourceInference
open CallableIndexedOwnedPublicFaultReceiverTables
open CallableIndexedOwnedContextualDiagnosticSources

abbrev Key := SourceSpecialization.SpecializationKey

/-- Static receipts for the actual prepared program. No recipe or code getter
is added to the public session interface. -/
def FactoryReceiptsFor {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCallableIndexedPrograms.Prepared checked) : Prop :=
  ∀ issued : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial checked),
    prepared.base.diagnostics = some issued → FactoryAt prepared.base issued ∧
      CompatiblePublicCallableAllocationReceipts.AllocationAt prepared.base issued

/-- Existing structure elimination is used only in this proof goal. Its actual
retained sealed compiler supplies the genuine Source and allocation factories. -/
theorem artifact_factory_receipts (artifact : SourceCoreIndexedSession.Artifact) :
    FactoryReceiptsFor artifact.program := by
  unfold FactoryReceiptsFor
  cases artifact
  rename_i authority recipe
  dsimp only [SourceCoreIndexedSession.Artifact.program, SourceCoreIndexedSession.Recipe.program]
  intro issued present
  exact ⟨CallableIndexedOwnedContextualDiagnosticSources.of_compiled recipe.compiled present,
    CompatiblePublicCallableAllocationReceipts.of_compiled recipe.compiled present⟩

/-- The actual optional issuer and selected own row are static inputs. -/
def ReadInputs {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCallableIndexedPrograms.Prepared checked) (owner : Key) : Prop :=
  ∃ issued : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial checked),
    ∃ own : SourceCoreProgramFaultSites.Function,
      prepared.base.diagnostics = some issued ∧ issued.program.base.find? owner = some own

/-- The receiving registry and actual metadata are kept with the missing row.
Neither its source owner nor its requested span follows from a raw type. -/
def MissingInputs {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCallableIndexedPrograms.Prepared checked)
    (owner : Key) (id : ExpressionId) (registry : SourceCoreRawMetadata.Registry)
    (rawKey rawValue : TypeSystem.Ty) (header : Word) : Prop :=
  ∃ issued : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial checked),
    ∃ missing : SourceCoreCompatibleDataPlaceFaultSites.MissingSite,
      prepared.base.diagnostics = some issued ∧ missing ∈ issued.missing ∧
      missing.base = issued.program.reasonAt owner id ∧
      CompatiblePayload.MetadataRep registry (.mapping rawKey rawValue) header ∧
      SourceCoreRawMetadata.runtimeType rawKey = SourceCoreRawMetadata.runtimeType missing.keyType ∧
      SourceCoreRawMetadata.runtimeType rawValue = SourceCoreRawMetadata.runtimeType missing.valueType

/-- The exact globally issued read and actual table observation stay together. -/
def ReadObservationAt {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCallableIndexedPrograms.Prepared checked)
    (owner : Key) (id : ExpressionId) (binder : Resolved.LocalId) (span : Syntax.SourceSpan)
    (table : SourceCoreFaultSites.Table) : Prop :=
  ∃ issued : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial checked),
    ∃ read : SourceCoreFaultSites.ReadSite,
      prepared.base.diagnostics = some issued ∧ read.expression = id ∧
      read.binder = binder ∧ read.span = span ∧
      issued.program.reasonAt owner id = read.reason ∧ read ∈ issued.program.rootTable.reads ∧
      table.diagnostic? read.reason = some {
        error := .uninitializedLocal binder, site := .occurrence id.occurrence, span := some span }

/-- The first actual index issuer is retained beside the missing row and decoded
raw error. The decoded diagnostic's span is deliberately not identified here. -/
def IndexObservationAt {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCallableIndexedPrograms.Prepared checked)
    (owner : Key) (node : ExpressionNode) (rawValue : TypeSystem.Ty) (header : Word)
    (table : SourceCoreFaultSites.Table) : Prop :=
  ∃ issued : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial checked),
    ∃ missing : SourceCoreCompatibleDataPlaceFaultSites.MissingSite,
    ∃ site : SourceCoreDataFaultSites.IndexSite,
      prepared.base.diagnostics = some issued ∧ missing ∈ issued.missing ∧
      missing.base = site.reason ∧
      issued.program.expressions.indices.find?
        (fun candidate => decide (candidate.owner = owner ∧ candidate.expression = node.id)) = some site ∧
      site.owner = owner ∧ site.expression = node.id ∧
      issued.program.reasonAt owner node.id = site.reason ∧
      (∃ actual issuer actualBase actualKey,
        (owner, actual) ∈ (prepared.base.plan.specializations.map
          (fun row => (row.key, row.function.typedBody)) ++
          prepared.base.contexts.map (fun item => (item.caller.key, item.source))) ∧
        actual.owner = owner.declaration ∧ ContainsExpression actual node.id issuer ∧
        issuer.form = .index actualBase actualKey ∧ node.form = .index actualBase actualKey ∧
        issuer.span = node.span ∧
        site.diagnostic = ⟨.typeMismatch issuer.type none, .occurrence node.id.occurrence, some node.span⟩) ∧
      ∃ diagnostic, table.diagnostic? (site.reason.add header) = some diagnostic ∧
        diagnostic.error = .typeMismatch rawValue none

/-- The genuine ordinary-root lookup table decodes a real canonical local read.
The nested primitive owner remains independent of that selected root key. -/
theorem session_read_observation {artifact : SourceCoreIndexedSession.Artifact}
    (session : SourceCoreIndexedSession.Session artifact) {rootKey : Key} {table : SourceCoreFaultSites.Table}
    (receiver : session.DiagnosticTableAt rootKey table) {owner : Key}
    (inputs : ReadInputs artifact.program owner) {row : SourceSpecialization.SpecializedFunction}
    (record : SourceCompilationPlan.exactSpecialization artifact.program.base.plan owner = .ok row)
    (unique : NodeOccurrencesUnique row.function.typedBody)
    {id : ExpressionId} {node : ExpressionNode} {name : String} {binder : Resolved.LocalId}
    (contains : ContainsExpression row.function.typedBody id node)
    (form : node.form = .reference name (.local binder)) :
    ∃ registry, session.RegistryAt registry ∧
      ReadObservationAt artifact.program owner id binder node.span table := by
  obtain ⟨issued, own, present, ownFound⟩ := inputs
  obtain ⟨factory, allocation⟩ := artifact_factory_receipts artifact issued present
  have noIndex := CompatibleContextualDiagnosticIndexOrigins.FactoryAt.no_index_at_read
    factory record unique contains form
  obtain ⟨locals0, root, remaining, _roots, _contexts, accepted⟩ := factory.actual
  obtain ⟨base, extra, reserved⟩ := CompatiblePlaceMissingPreparationRanges.prepare_reserved_receipt accepted
  have baseAccepted := CallableIndexedOwnedPublicDiagnosticReceipts.data_place_base accepted
  obtain ⟨read, _ownRead, expression, binderEq, spanEq, ownReason, rootMember,
    _positive, _ordinary, _noAdditional, _byReason, _baseDecoded⟩ :=
    SourceCoreProgramFaultSites.prepare_local_read baseAccepted record ownFound contains.1 form
  have expressionEq : read.expression = id := expression.trans contains.2
  have sameExpressionBase : issued.program.expressions.base = issued.program.base :=
    reserved.sameExpressionBase.trans reserved.sameBase.symm
  have token : issued.program.reasonAt owner id = read.reason := by
    unfold SourceCoreDataPlaceFaultSites.Program.reasonAt SourceCoreDataFaultSites.Program.reasonAt
    rw [noIndex, sameExpressionBase, ownFound]
    simpa only [contains.2] using ownReason
  have readsSame : issued.program.rootTable.reads = issued.program.base.rootTable.reads := by
    rw [reserved.sameRoot, reserved.sameBase]
  have member : read ∈ issued.program.rootTable.reads := by rw [readsSame]; exact rootMember
  have baseMember : read ∈ base.rootTable.reads := by simpa only [reserved.sameRoot] using member
  obtain ⟨registry, registryAt, extension, selectedRoot, actual, _found, _key, rebuilt, tableEq⟩ := receiver.rebuild
  rw [present] at rebuilt
  have append : table = appendCallable artifact.program actual := by
    rw [tableEq]
    unfold appendCallable
    cases artifact.program.base.callableDiagnostics <;> rfl
  have decoded : table.diagnostic? read.reason = some {
      error := .uninitializedLocal binder, site := .occurrence id.occurrence, span := some node.span } := by
    rw [append, appendCallable_diagnostic_of_below (allocation.below (reserved.readsBelow read baseMember))]
    simpa only [expressionEq, binderEq, spanEq] using
      CompatiblePublicDiagnosticPriority.read_diagnostic reserved rebuilt baseMember
  exact ⟨registry, registryAt, issued, read, present, expressionEq, binderEq, spanEq, token, member, decoded⟩

/-- The actual Session registry fixes receiving metadata. Its rebuilt table and
filtered callable append preserve the exact missing-default error. -/
theorem session_index_missing_observation {artifact : SourceCoreIndexedSession.Artifact}
    (session : SourceCoreIndexedSession.Session artifact) {rootKey : Key} {table : SourceCoreFaultSites.Table}
    (receiver : session.DiagnosticTableAt rootKey table)
    (registry : SourceCoreRawMetadata.Registry) (registryAt : session.RegistryAt registry)
    {owner : Key} {row : SourceSpecialization.SpecializedFunction}
    {node : ExpressionNode} {base key : ExpressionId} {rawKey rawValue : TypeSystem.Ty} {header : Word}
    (inputs : MissingInputs artifact.program owner node.id registry rawKey rawValue header)
    (record : SourceCompilationPlan.exactSpecialization artifact.program.base.plan owner = .ok row)
    (unique : NodeOccurrencesUnique row.function.typedBody)
    (contains : ContainsExpression row.function.typedBody node.id node)
    (form : node.form = .index base key) :
    IndexObservationAt artifact.program owner node rawValue header table := by
  obtain ⟨issued, missing, present, member, providerBase, metadata, keyView, valueView⟩ := inputs
  obtain ⟨factory, allocation⟩ := artifact_factory_receipts artifact issued present
  obtain ⟨site, found, ownerEq, expressionEq, origin⟩ :=
    CompatibleContextualDiagnosticIndexOrigins.FactoryAt.index_selected_origin
      factory record unique contains form
  have reason : issued.program.reasonAt owner node.id = site.reason := by
    unfold SourceCoreDataPlaceFaultSites.Program.reasonAt SourceCoreDataFaultSites.Program.reasonAt
    rw [found]
  have baseEq : missing.base = site.reason := providerBase.trans reason
  obtain ⟨locals0, root, remaining, _roots, _contexts, accepted⟩ := factory.actual
  obtain ⟨baseProgram, extra, reserved⟩ := CompatiblePlaceMissingPreparationRanges.prepare_reserved_receipt accepted
  obtain ⟨actualRegistry, actualAt, extension, selectedRoot, actual, _found, _key, rebuilt, tableEq⟩ := receiver.rebuild
  have sameRegistry : actualRegistry = registry := actualAt.symm.trans registryAt
  have actualMetadata : CompatiblePayload.MetadataRep actualRegistry (.mapping rawKey rawValue) header := by
    rw [sameRegistry]
    exact metadata
  rw [present] at rebuilt
  have append : table = appendCallable artifact.program actual := by
    rw [tableEq]
    unfold appendCallable
    cases artifact.program.base.callableDiagnostics <;> rfl
  obtain ⟨diagnostic, decoded, error⟩ :=
    CompatiblePlaceMissingPreparationRanges.table_diagnostic accepted rebuilt member actualMetadata keyView valueView
  have below : BelowCallable artifact.program (site.reason.add header) := by
    simpa only [baseEq] using
      allocation.below (CompatiblePublicDiagnosticPriority.missing_token_below reserved rebuilt member actualMetadata)
  have decodedAt : table.diagnostic? (site.reason.add header) = some diagnostic := by
    rw [append, appendCallable_diagnostic_of_below below]
    simpa only [baseEq] using decoded
  exact ⟨issued, missing, site, present, member, baseEq, found, ownerEq, expressionEq,
    reason, origin, diagnostic, decodedAt, error⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleSessionContextualDiagnosticObservations
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleSessionContextualMissingDiagnosticObservations
/-! The canonical expression row and actual receiving registry retain the
exact Session diagnostic. Factory authority comes from the sealed artifact
in a proof goal, and the original filtered callable append is unchanged. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleSessionContextualMissingDiagnosticObservations
open Core Frontend SourceInference CompatiblePayload
open CallableIndexedOwnedPublicFaultReceiverTables
open CallableIndexedOwnedContextualDiagnosticSources
open CompatibleSessionContextualDiagnosticObservations (artifact_factory_receipts)
open CompatiblePublicContextualMissingDiagnosticObservations

abbrev Key := SourceSpecialization.SpecializationKey

/-- The optional actual issuer identity stays with the exact decoded
occurrence and span. Primitive Source failure paths remain independent. -/
def CanonicalMissingObservationAt {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCallableIndexedPrograms.Prepared checked)
    (owner : Key) (node : ExpressionNode) (rawValue : TypeSystem.Ty) (header : Word)
    (table : SourceCoreFaultSites.Table) : Prop :=
  ∃ issued : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial checked),
    prepared.base.diagnostics = some issued ∧
    table.diagnostic? ((issued.program.reasonAt owner node.id).add header) = some {
      error := .typeMismatch rawValue none,
      site := .occurrence node.id.occurrence, span := some node.span }

/-- The real rebuilt Session table identifies the canonical missing row
internally; only receiving metadata and its actual Source base view remain. -/
theorem session_index_missing_observation {artifact : SourceCoreIndexedSession.Artifact}
    (session : SourceCoreIndexedSession.Session artifact)
    {rootKey : Key} {table : SourceCoreFaultSites.Table}
    (receiver : session.DiagnosticTableAt rootKey table)
    (registry : SourceCoreRawMetadata.Registry) (registryAt : session.RegistryAt registry)
    {issued : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial _)}
    (present : artifact.program.base.diagnostics = some issued)
    {owner : Key} {function : SourceSpecialization.SpecializedFunction}
    (record : SourceCompilationPlan.exactSpecialization artifact.program.base.plan owner = .ok function)
    (unique : NodeOccurrencesUnique function.function.typedBody)
    {node : ExpressionNode} {base key : ExpressionId}
    (contains : ContainsExpression function.function.typedBody node.id node)
    (form : node.form = .index base key)
    {rawKey rawValue : TypeSystem.Ty} {header : Word}
    (view : CanonicalMappingView function.function.typedBody base rawKey rawValue)
    (metadata : MetadataRep registry (.mapping rawKey rawValue) header) :
    CanonicalMissingObservationAt artifact.program owner node rawValue header table := by
  obtain ⟨factory, allocation⟩ := artifact_factory_receipts artifact issued present
  obtain ⟨actualRegistry, actualAt, extension, selectedRoot, actual,
    _found, _key, rebuilt, tableEq⟩ := receiver.rebuild
  have sameRegistry : actualRegistry = registry := actualAt.symm.trans registryAt
  have actualMetadata : MetadataRep actualRegistry (.mapping rawKey rawValue) header := by
    rw [sameRegistry]
    exact metadata
  rw [present] at rebuilt
  obtain ⟨missing, member, _receipt, providerBase, decoded⟩ :=
    CompatiblePublicContextualMissingDiagnosticObservations.FactoryAt.table_expression_missing_diagnostic
      factory record unique contains form view rebuilt actualMetadata
  obtain ⟨locals0, root, remaining, _roots, _contexts, accepted⟩ := factory.actual
  obtain ⟨baseProgram, extra, reserved⟩ := CompatiblePlaceMissingPreparationRanges.prepare_reserved_receipt accepted
  have below : BelowCallable artifact.program ((issued.program.reasonAt owner node.id).add header) := by
    simpa only [providerBase] using allocation.below
      (CompatiblePublicDiagnosticPriority.missing_token_below reserved rebuilt member actualMetadata)
  have append : table = appendCallable artifact.program actual := by
    rw [tableEq]
    unfold appendCallable
    cases artifact.program.base.callableDiagnostics <;> rfl
  refine ⟨issued, present, ?_⟩
  rw [append, appendCallable_diagnostic_of_below below]
  simpa only [providerBase] using decoded

end Solcore.SourceSemantics.CoreLowering.CompatibleSessionContextualMissingDiagnosticObservations
end
