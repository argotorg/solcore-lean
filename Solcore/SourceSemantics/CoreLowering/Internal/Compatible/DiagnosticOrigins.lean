import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.PlaceReflection
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.BodyReadyState
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.Paths
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.PlaceKeys
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.StatementAdmission
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionTyped
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.Statements
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.ScalarReflection

/-!
# Compatible profile: diagnostic origins

Registry completeness, origins of contextual diagnostics, and general index trees.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleRegistryDiagnosticCompleteness
/-! An authentic compatible diagnostic issuer rebuilds at every bounded
extension of its actual metadata registry. No execution receipt is required. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CompatibleRegistryDiagnosticCompleteness
open Core Frontend SourceInference
open SourceCoreCompatibleDataPlaceFaultSites

private theorem forIn_total {α β ε : Type} (items : List α)
    (step : α → β → Except ε (ForInStep β))
    (each : ∀ item, item ∈ items → ∀ state, ∃ next, step item state = .ok (.yield next)) :
    ∀ state, ∃ final, forIn items state step = .ok final := by
  induction items with
  | nil => intro state; exact ⟨state, rfl⟩
  | cons head tail ih =>
    intro state
    obtain ⟨next, advanced⟩ := each head (by simp) state
    obtain ⟨final, continued⟩ := ih (fun item member => each item (List.mem_cons_of_mem _ member)) next
    exact ⟨final, by simp only [List.forIn_cons, advanced, bind, Except.bind, continued]⟩

private theorem bind_total {α β ε : Type} {action : Except ε α} {next : α → Except ε β}
    (first : ∃ value, action = .ok value) (second : ∀ value, ∃ output, next value = .ok output) :
    ∃ output, (action >>= next) = .ok output := by
  obtain ⟨value, rfl⟩ := first
  exact second value

private theorem yield_bind_total {β ε : Type} {action : Except ε β}
    (first : ∃ value, action = .ok value) :
    ∃ output, (action >>= fun value => pure (ForInStep.yield value)) = .ok (ForInStep.yield output) := by
  obtain ⟨value, rfl⟩ := first
  exact ⟨value, rfl⟩

/-- Reserved nonwrapping ranges and the owning registry budget are sufficient
for the real pair of finite expansion loops to finish. -/
theorem missingDiagnostics_complete
    (registry : SourceCoreRawMetadata.Registry) (sites : List MissingSite)
    (bounded : registry.length ≤ registry.limits.maxEntries)
    (reserved : ∀ site, site ∈ sites → site.base.val + registry.limits.maxEntries < wordModulus) :
    ∃ rows, missingDiagnostics registry sites = .ok rows := by
  unfold missingDiagnostics
  split
  · apply bind_total
    · apply forIn_total
      intro site member rows
      apply yield_bind_total
      apply forIn_total
      rintro ⟨metadata, index⟩ stored state
      have indexBound : index < registry.entries.length := by
        exact (List.getElem?_eq_some_iff.mp (List.mk_mem_zipIdx_iff_getElem?.mp stored)).1
      cases metadata with
      | proxy | constructor => exact ⟨state, rfl⟩
      | mapping key value =>
        dsimp only
        split
        · have within : site.base.val + index + 1 < wordModulus := by
            have room := reserved site member
            change registry.entries.length ≤ registry.limits.maxEntries at bounded
            omega
          have wordAt : Word.ofNat? (site.base.val + index + 1) =
              some ⟨site.base.val + index + 1, within⟩ := by
            simp only [Word.ofNat?, within, ↓reduceDIte]
          change ∃ updated : List (Word × Diagnostic),
            ((match Word.ofNat? (site.base.val + index + 1) with
              | some value => Except.ok value
              | none => Except.error SourceCoreCompatibleDataPlaceFaultSites.Error.reasonSpaceExhausted) >>= fun reason =>
                if state.any (fun previous => decide (previous.1 = reason)) then Except.ok (ForInStep.yield state)
                else Except.ok (ForInStep.yield (state ++ [(reason, {
                  error := .typeMismatch value none, site := site.site, span := some site.span })]))) =
              Except.ok (ForInStep.yield updated)
          rw [wordAt]
          simp only [bind, Except.bind]
          split <;> exact ⟨_, rfl⟩
        · exact ⟨state, rfl⟩
    · intro rows; exact ⟨rows, rfl⟩
  · contradiction

/-- Successful source preparation reserves every dynamic metadata slot before
any public input can extend the registry. -/
theorem tableForRegistry_complete
    {context : SourceCoreCompatibleValues.Context} {plan : SourceSpecializationWorklist.Plan}
    {root : SourceSpecialization.SpecializationKey} {sources : List (SourceSpecialization.SpecializationKey × TypedSource)}
    {program : SourceCoreCompatibleDataPlaceFaultSites.Program context}
    (prepared : SourceCoreCompatibleDataPlaceFaultSites.prepare context plan root sources = .ok program)
    (registry : SourceCoreRawMetadata.Registry)
    (extension : SourceCoreRawMetadata.Extends context.registry registry) :
    ∃ table, program.tableForRegistry registry extension = .ok table := by
  have ranges := (CompatiblePlaceMissingPreparationRanges.prepare_ranges prepared).1
  obtain ⟨rows, expanded⟩ := missingDiagnostics_complete registry program.missing registry.length_le_limit (by
    intro site member
    rw [extension.limits]
    exact ranges.reserved site member)
  refine ⟨{program.program.rootTable with additional := program.fixed ++ rows}, ?_⟩
  simp only [Program.tableForRegistry, expanded, bind, Except.bind, pure, Except.pure]

/-- The sealed compilation supplies the authentic preparation equation. -/
theorem compiled_table_complete (compiled : SourceCoreUnifiedCompilation.Compiled)
    {program : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked)}
    (present : compiled.indexed.base.diagnostics = some program)
    (registry : SourceCoreRawMetadata.Registry)
    (extension : SourceCoreRawMetadata.Extends compiled.compatible.checked.staticRegistry registry) :
    ∃ table, program.tableForRegistry registry extension = .ok table := by
  obtain ⟨root, sources, prepared⟩ := CallableIndexedOwnedPublicDiagnosticReceipts.compiled_diagnostics compiled present
  exact tableForRegistry_complete prepared registry extension

end Solcore.SourceSemantics.CoreLowering.CompatibleRegistryDiagnosticCompleteness
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatiblePathMissingProvider
/-! A selected static suffix reads the provider and key view retained by the
same prepared path. This proof examines only static membership certificates. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMixedRoute
open Core Frontend SourceInference SourceCoreCompatibleDataPlaces CompatiblePlaceKeys

/-- Static suffix membership selects the original complete generated index. -/
theorem IndexInPath.index_member {checked : Checked} {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
    {terminalRoot keySource valueSource terminalLeaf : TypeSystem.Ty} {key : ExpressionId} {layout : OrderedMapping.Layout}
    {terminalProjections : List PlaceProjection} {terminalSteps : List PreparedStep} {terminalPosition : Nat}
    {terminalKeys : List (ExpressionId × Ty)} {comparison : Expr} {token : Word}
    {certificate : IndexSite checked source terminalRoot keySource valueSource key layout}
    {generated : CompatibleMapping.Index checked ⟨layout, key, terminalPosition, comparison, token⟩}
    {tail : PreparedPath checked source site valueSource terminalProjections (terminalPosition + 1)
      terminalSteps terminalKeys terminalLeaf}
    {root leaf : TypeSystem.Ty} {projections : List PlaceProjection} {position : Nat}
    {steps : List PreparedStep} {keys : List (ExpressionId × Ty)}
    {path : PreparedPath checked source site root projections position steps keys leaf}
    (selected : IndexInPath (.index certificate generated tail) path) :
    PreparedStep.index ⟨layout, key, terminalPosition, comparison, token⟩ ∈ steps := by
  induction selected with
  | here => exact List.mem_cons_self
  | member _ ih => exact List.mem_cons_of_mem _ ih
  | index _ ih => exact List.mem_cons_of_mem _ ih

private theorem index_views {checked : Checked} {source : TypedSource}
    {leftRoot leftKey leftValue rightRoot rightKey rightValue : TypeSystem.Ty}
    {key : ExpressionId} {layout : OrderedMapping.Layout}
    (left : IndexSite checked source leftRoot leftKey leftValue key layout)
    (right : IndexSite checked source rightRoot rightKey rightValue key layout) :
    leftKey = rightKey ∧ leftValue = rightValue := by
  obtain ⟨leftEntry, leftFound, leftSource⟩ := CompatibleEquality.identity_entry left.identity
  obtain ⟨rightEntry, rightFound, rightSource⟩ := CompatibleEquality.identity_entry right.identity
  have entries := Option.some.inj (leftFound.symm.trans rightFound)
  subst rightEntry
  have roots := leftSource.symm.trans rightSource
  rw [left.view, right.view] at roots
  exact TypeSystem.Ty.mapping.inj roots

/-- Select the exact original provider using the retained raw catalog row. -/
theorem IndexInPath.provider {checked : Checked} {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
    {terminalRoot keySource valueSource terminalLeaf : TypeSystem.Ty} {key : ExpressionId} {layout : OrderedMapping.Layout}
    {terminalProjections : List PlaceProjection} {terminalSteps : List PreparedStep} {terminalPosition : Nat}
    {terminalKeys : List (ExpressionId × Ty)} {comparison : Expr} {token : Word}
    {certificate : IndexSite checked source terminalRoot keySource valueSource key layout}
    {generated : CompatibleMapping.Index checked ⟨layout, key, terminalPosition, comparison, token⟩}
    {tail : PreparedPath checked source site valueSource terminalProjections (terminalPosition + 1)
      terminalSteps terminalKeys terminalLeaf}
    {root leaf : TypeSystem.Ty} {projections : List PlaceProjection} {position : Nat}
    {steps : List PreparedStep} {keys : List (ExpressionId × Ty)}
    {path : PreparedPath checked source site root projections position steps keys leaf}
    (selected : IndexInPath (.index certificate generated tail) path)
    {missing : TypeSystem.Ty → Word} (providers : Providers missing path) : token = missing valueSource := by
  obtain ⟨actualRoot, actualKey, actualValue, actual, _, provider⟩ := providers _ (selected.index_member (certificate := certificate) (generated := generated) (tail := tail))
  have values := (index_views actual certificate).2
  simpa only [values] using provider

private theorem key_views_node {checked : Checked} {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
    {root leaf : TypeSystem.Ty} {projections : List PlaceProjection} {position : Nat}
    {steps : List PreparedStep} {keys : List (ExpressionId × Ty)}
    {path : PreparedPath checked source site root projections position steps keys leaf}
    {types : List TypeSystem.Ty} (views : KeyViews path types)
    (nodes : DataPatternValues.ListRel (fun id type => ∃ node,
      source.lookupExpression? id = some node ∧ node.type = type) (DataPlaceKeyOrder.sourceKeys projections) types)
    {reference : PreparedIndex} (member : PreparedStep.index reference ∈ steps) :
    ∃ actualRoot actualKey actualValue node,
      IndexSite checked source actualRoot actualKey actualValue reference.key reference.layout ∧
      source.lookupExpression? reference.key = some node ∧
      SourceCoreRawMetadata.runtimeType actualKey = SourceCoreRawMetadata.runtimeType node.type := by
  induction views with
  | nil => cases member
  | member rest ih =>
    rcases List.mem_cons.mp member with impossible | member
    · cases impossible
    · exact ih nodes member
  | @index root keySource valueSource leaf key layout projections steps position keys comparison missing certificate generated tail type types view rest ih =>
    cases nodes with
    | cons head more =>
      rcases List.mem_cons.mp member with same | member
      · cases same
        obtain ⟨node, found, nodeType⟩ := head
        exact ⟨root, keySource, valueSource, node, certificate, found, by simpa only [nodeType] using view⟩
      · exact ih more member

/-- Select the retained key node and genuine raw runtime view at the suffix. -/
theorem IndexInPath.key_view {checked : Checked} {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
    {terminalRoot keySource valueSource terminalLeaf : TypeSystem.Ty} {key : ExpressionId} {layout : OrderedMapping.Layout}
    {terminalProjections : List PlaceProjection} {terminalSteps : List PreparedStep} {terminalPosition : Nat}
    {terminalKeys : List (ExpressionId × Ty)} {comparison : Expr} {token : Word}
    {certificate : IndexSite checked source terminalRoot keySource valueSource key layout}
    {generated : CompatibleMapping.Index checked ⟨layout, key, terminalPosition, comparison, token⟩}
    {tail : PreparedPath checked source site valueSource terminalProjections (terminalPosition + 1)
      terminalSteps terminalKeys terminalLeaf}
    {root leaf : TypeSystem.Ty} {projections : List PlaceProjection} {position : Nat}
    {steps : List PreparedStep} {keys : List (ExpressionId × Ty)}
    {path : PreparedPath checked source site root projections position steps keys leaf}
    (selected : IndexInPath (.index certificate generated tail) path)
    {types : List TypeSystem.Ty} (views : KeyViews path types)
    (nodes : DataPatternValues.ListRel (fun id type => ∃ node,
      source.lookupExpression? id = some node ∧ node.type = type) (DataPlaceKeyOrder.sourceKeys projections) types) :
    ∃ node, source.lookupExpression? key = some node ∧
      SourceCoreRawMetadata.runtimeType keySource = SourceCoreRawMetadata.runtimeType node.type := by
  obtain ⟨actualRoot, actualKey, actualValue, node, actual, found, view⟩ :=
    key_views_node views nodes (selected.index_member (certificate := certificate) (generated := generated) (tail := tail))
  have keys := (index_views certificate actual).1
  exact ⟨node, found, by simpa only [keys] using view⟩

private theorem typed_nodes {source : TypedSource} {context : SourceSemantics.Context}
    {ids : List ExpressionId} {types : List TypeSystem.Ty}
    (unique : NodeOccurrencesUnique source) (typed : ExpressionsHaveTypes source context ids types) :
    DataPatternValues.ListRel (fun id type => ∃ node,
      source.lookupExpression? id = some node ∧ node.type = type) ids types := by
  cases ids with
  | nil => cases typed; exact .nil
  | cons id more =>
    cases typed with
    | cons head rest =>
      obtain ⟨node, member, type⟩ := head.stored_type
      exact .cons ⟨node, lookupExpression?_complete unique member, type⟩ (typed_nodes unique rest)
termination_by ids.length

/-- Original projection typing supplies all selected key facts through the
existing KeyTyping proof. Native projected equality supplies no raw type. -/
theorem IndexInPath.key_view_of_typing {checked : Checked} {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
    {context : SourceSemantics.Context}
    {terminalRoot keySource valueSource terminalLeaf : TypeSystem.Ty} {key : ExpressionId} {layout : OrderedMapping.Layout}
    {terminalProjections : List PlaceProjection} {terminalSteps : List PreparedStep} {terminalPosition : Nat}
    {terminalKeys : List (ExpressionId × Ty)} {comparison : Expr} {token : Word}
    {certificate : IndexSite checked source terminalRoot keySource valueSource key layout}
    {generated : CompatibleMapping.Index checked ⟨layout, key, terminalPosition, comparison, token⟩}
    {tail : PreparedPath checked source site valueSource terminalProjections (terminalPosition + 1)
      terminalSteps terminalKeys terminalLeaf}
    {root leaf sourceRoot sourceLeaf : TypeSystem.Ty} {projections : List PlaceProjection} {position : Nat}
    {steps : List PreparedStep} {keys : List (ExpressionId × Ty)}
    {path : PreparedPath checked source site root projections position steps keys leaf}
    (selected : IndexInPath (.index certificate generated tail) path)
    (unique : NodeOccurrencesUnique source) (signatures : context.signatures = checked.signatures)
    (view : SourceCoreRawMetadata.runtimeType root = SourceCoreRawMetadata.runtimeType sourceRoot)
    (typed : SourceProjectionsHaveType source context sourceRoot projections sourceLeaf) :
    ∃ node, source.lookupExpression? key = some node ∧
      SourceCoreRawMetadata.runtimeType keySource = SourceCoreRawMetadata.runtimeType node.type := by
  obtain ⟨types, original⟩ := CallableIndexedOwnedPlaceAdmission.projections_keys_typed typed
  have nodes := typed_nodes unique original
  obtain ⟨views, _⟩ := CompatiblePlaceKeyTyping.of_nodes unique signatures path view typed nodes
  exact selected.key_view (certificate := certificate) (generated := generated) (tail := tail) views nodes

/-- The actual unavailable mapping selects its own owning metadata, Source
key node and original provider. The raw semantic value type stays independent. -/
theorem MissingTerminal.provider_view {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : CompatiblePayload.FunctionModel checked.catalog ambient}
    {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {source : TypedSource} {site : SourceCoreElaboration.ErrorSite} {context : SourceSemantics.Context}
    {root leaf sourceRoot sourceLeaf : TypeSystem.Ty} {projections : List PlaceProjection} {position : Nat}
    {steps : List PreparedStep} {keys : List (ExpressionId × Ty)}
    {path : PreparedPath checked source site root projections position steps keys leaf}
    {reason : Dynamic.SemanticFault} {token : Word}
    (terminal : MissingTerminal (registry := registry) functions mapping world path reason token)
    {missing : TypeSystem.Ty → Word} (providers : Providers missing path)
    (unique : NodeOccurrencesUnique source) (signatures : context.signatures = checked.signatures)
    (view : SourceCoreRawMetadata.runtimeType root = SourceCoreRawMetadata.runtimeType sourceRoot)
    (typed : SourceProjectionsHaveType source context sourceRoot projections sourceLeaf) :
    ∃ rawKey rawValue header key node,
      CompatiblePayload.MetadataRep registry (.mapping rawKey rawValue) header ∧
      source.lookupExpression? key = some node ∧
      SourceCoreRawMetadata.runtimeType rawKey = SourceCoreRawMetadata.runtimeType node.type ∧
      reason = .missingMappingDefault rawValue ∧
      token = (missing (SourceCoreRawMetadata.runtimeType rawValue)).add header := by
  obtain ⟨terminalRoot, keySource, valueSource, terminalLeaf, key, layout, terminalProjections,
    terminalSteps, terminalPosition, terminalKeys, comparison, base, certificate, generated, tail,
    selected, rawKey, rawValue, entries, header, nativeEntries, fallback, lookup, fields,
    keyView, valueView, _lookupTyped, _absent, _unavailable, fault, tokenEq⟩ := terminal
  have provider := selected.provider (certificate := certificate) (generated := generated) (tail := tail) providers
  obtain ⟨node, found, keyNodeView⟩ := selected.key_view_of_typing
    (certificate := certificate) (generated := generated) (tail := tail) unique signatures view typed
  refine ⟨rawKey, rawValue, header, key, node, fields.metadata, found, ?_, fault, ?_⟩
  · simpa only [keyView, SourceCoreRawMetadata.runtimeType_idempotent] using keyNodeView
  · simpa only [provider, valueView] using tokenEq

end Solcore.SourceSemantics.CoreLowering.CompatibleMixedRoute
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleContextualDiagnosticIndexOrigins
/-! The unconditional issuer receipt combines with actual contextual Source
views only at the queried key. Canonical uniqueness fixes the owning occurrence
and span; raw substituted types remain the issuer's original types. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleContextualDiagnosticIndexOrigins
open Core Frontend SourceInference
open CompatibleExpressionIndexSourceReceipts CallableIndexedOwnedContextualDiagnosticSources
abbrev Key := SourceSpecialization.SpecializationKey

/-- A genuine local read cannot have an index issuer at that same unique
canonical occurrence among the actual supplied Source views. -/
theorem Inventory.no_index_at_read {sources visited : List (Key × TypedSource)} {indices : List IndexSite}
    (inventory : Inventory sources visited indices) {owner : Key} {canonical : TypedSource}
    (views : QuerySourceViews owner canonical sources) (unique : SourceSemantics.NodeOccurrencesUnique canonical)
    {id : ExpressionId} {node : ExpressionNode} {name : String} {binder : Resolved.LocalId}
    (contains : SourceSemantics.ContainsExpression canonical id node)
    (form : node.form = .reference name (.local binder)) :
    indices.find? (fun site => decide (site.owner = owner ∧ site.expression = id)) = none := by
  apply List.find?_eq_none.mpr
  intro site member matched
  have hit : site.owner = owner ∧ site.expression = id := of_decide_eq_true matched
  obtain ⟨actual, issuer, base, key, actualMember, _owns, issuerContains, issuerForm, _diagnostic⟩ :=
    inventory.origins site member
  have view := views site.owner actual actualMember hit.1
  rw [hit.2] at issuerContains
  exact view.no_index_at_read unique contains form issuerContains issuerForm

/-- The selected row comes from a literal actual issuer, while the genuine
query views identify the canonical index form and the exact span. -/
theorem Inventory.selected_origin {sources visited : List (Key × TypedSource)} {indices : List IndexSite}
    (inventory : Inventory sources visited indices) {owner : Key} {canonical : TypedSource}
    (views : QuerySourceViews owner canonical sources) (unique : SourceSemantics.NodeOccurrencesUnique canonical)
    {id : ExpressionId} {node : ExpressionNode} (contains : SourceSemantics.ContainsExpression canonical id node)
    {site : IndexSite} (found : indices.find? (fun site => decide (site.owner = owner ∧ site.expression = id)) = some site) :
    site.owner = owner ∧ site.expression = id ∧
    ∃ actual issuer base key,
      (owner, actual) ∈ sources ∧ actual.owner = owner.declaration ∧
      SourceSemantics.ContainsExpression actual id issuer ∧ issuer.form = .index base key ∧
      node.form = .index base key ∧ issuer.span = node.span ∧
      site.diagnostic = ⟨.typeMismatch issuer.type none, .occurrence id.occurrence, some node.span⟩ := by
  have hit : site.owner = owner ∧ site.expression = id := of_decide_eq_true
    (List.find?_some (p := fun site : IndexSite => decide (site.owner = owner ∧ site.expression = id)) found)
  obtain ⟨actual, issuer, base, key, member, owns, retained, form, diagnostic⟩ :=
    inventory.origins site (List.mem_of_find?_eq_some found)
  have view := views site.owner actual member hit.1
  rw [hit.1] at member owns
  rw [hit.2] at retained
  obtain ⟨canonicalForm, span⟩ := view.index_span_at unique contains retained form
  refine ⟨hit.1, hit.2, actual, issuer, base, key, member, owns, retained, form, canonicalForm, span, ?_⟩
  rw [diagnostic, retained.2, span]

/-- Actual coverage selects an index row for a supplied canonical source;
this uses its literal member and form rather than a type or decoder guess. -/
theorem Inventory.index_selected {sources : List (Key × TypedSource)} {indices : List IndexSite}
    (inventory : Inventory sources sources indices) {owner : Key} {canonical : TypedSource}
    (member : (owner, canonical) ∈ sources) {node : ExpressionNode} {base key : ExpressionId}
    (contains : SourceSemantics.ContainsExpression canonical node.id node) (form : node.form = .index base key) :
    Selected indices owner node.id :=
  inventory.covered owner canonical member node contains.1 base key form

theorem FactoryAt.no_index_at_read {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : SourceCoreCompatibleFunctions.Prepared checked}
    {diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial checked)}
    (factory : FactoryAt prepared diagnostics) {owner : Key} {row : SourceSpecialization.SpecializedFunction}
    (record : SourceCompilationPlan.exactSpecialization prepared.plan owner = .ok row)
    (unique : SourceSemantics.NodeOccurrencesUnique row.function.typedBody)
    {id : ExpressionId} {node : ExpressionNode} {name : String} {binder : Resolved.LocalId}
    (contains : SourceSemantics.ContainsExpression row.function.typedBody id node)
    (form : node.form = .reference name (.local binder)) :
    diagnostics.program.expressions.indices.find? (fun site => decide (site.owner = owner ∧ site.expression = id)) = none := by
  obtain ⟨locals0, root, remaining, _roots, _contexts, accepted⟩ := factory.actual
  exact Inventory.no_index_at_read (CompatiblePlaceMissingPreparationRanges.prepare_index_origins accepted).2
    (factory.source_views record) unique contains form

theorem FactoryAt.index_selected_origin {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : SourceCoreCompatibleFunctions.Prepared checked}
    {diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial checked)}
    (factory : FactoryAt prepared diagnostics) {owner : Key} {row : SourceSpecialization.SpecializedFunction}
    (record : SourceCompilationPlan.exactSpecialization prepared.plan owner = .ok row)
    (unique : SourceSemantics.NodeOccurrencesUnique row.function.typedBody)
    {node : ExpressionNode} {base key : ExpressionId}
    (contains : SourceSemantics.ContainsExpression row.function.typedBody node.id node)
    (form : node.form = .index base key) :
    ∃ site, diagnostics.program.expressions.indices.find?
        (fun site => decide (site.owner = owner ∧ site.expression = node.id)) = some site ∧
      site.owner = owner ∧ site.expression = node.id ∧
      ∃ actual issuer actualBase actualKey,
        (owner, actual) ∈ (prepared.plan.specializations.map (fun row => (row.key, row.function.typedBody)) ++
          prepared.contexts.map (fun item => (item.caller.key, item.source))) ∧
        actual.owner = owner.declaration ∧ SourceSemantics.ContainsExpression actual node.id issuer ∧
        issuer.form = .index actualBase actualKey ∧ node.form = .index actualBase actualKey ∧
        issuer.span = node.span ∧
        site.diagnostic = ⟨.typeMismatch issuer.type none, .occurrence node.id.occurrence, some node.span⟩ := by
  obtain ⟨locals0, root, remaining, _roots, _contexts, accepted⟩ := factory.actual
  have inventory := (CompatiblePlaceMissingPreparationRanges.prepare_index_origins accepted).2
  have member : (owner, row.function.typedBody) ∈ (prepared.plan.specializations.map
      (fun row => (row.key, row.function.typedBody)) ++ prepared.contexts.map (fun item => (item.caller.key, item.source))) := by
    apply List.mem_append_left
    have filtered : row ∈ prepared.plan.specializations.filter (fun actual => decide (actual.key = owner)) := by
      rw [selected_filter record]
      exact List.mem_singleton_self _
    exact List.mem_map.mpr ⟨row, (List.mem_filter.mp filtered).1, by rw [selected_key record]⟩
  obtain ⟨site, found⟩ := Inventory.index_selected inventory member contains form
  exact ⟨site, found, Inventory.selected_origin inventory (factory.source_views record) unique contains found⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleContextualDiagnosticIndexOrigins
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleContextualDiagnosticMissingOrigins
/-! Missing-row ownership follows actual accepted suffixes. Query views and
canonical uniqueness identify the same occurrence and span only after genuine
reason ownership has selected the expression class and full specialization key. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleContextualDiagnosticMissingOrigins
open Core Frontend SourceInference CompatiblePayload
open SourceCoreCompatibleDataPlaceFaultSites CallableIndexedOwnedContextualDiagnosticSources
open CompatibleExpressionMissingSourceReceipts
abbrev Key := SourceSpecialization.SpecializationKey

/-- The literal supplied source receives its actual appended expression row. -/
theorem Inventory.expression_missing_at {sources : List (Key × TypedSource)} {indices : List IndexSite}
    {places : List PlaceSite} {missing : List MissingSite} (inventory : Inventory sources sources indices places missing)
    {owner : Key} {source : TypedSource} (member : (owner, source) ∈ sources)
    {node : ExpressionNode} {mapping key : ExpressionId}
    (contains : SourceSemantics.ContainsExpression source node.id node) (form : node.form = .index mapping key) :
    ∃ row, row ∈ missing ∧ ExpressionAt indices owner source node row :=
  inventory.covered owner source member node contains.1 mapping key form

/-- The appended row uses exactly the reason selected by the original lookup. -/
theorem ExpressionAt.reason_at {program : SourceCoreDataPlaceFaultSites.Program}
    {owner : Key} {source : TypedSource} {node : ExpressionNode} {row : MissingSite}
    (receipt : ExpressionAt program.expressions.indices owner source node row) :
    row.base = program.reasonAt owner node.id := by
  obtain ⟨mapping, key, base, keyType, valueType, selected, _form, _lookup, _mappingView, _valueView, found, rowEq⟩ := receipt
  rw [rowEq]
  simp only [SourceCoreDataPlaceFaultSites.Program.reasonAt, SourceCoreDataFaultSites.Program.reasonAt, found]

/-- A row at this genuine selected reason cannot belong to a place allocation
or to a different expression key. Its issuer raw type stays independent. -/
theorem Inventory.row_site_span {sources visited : List (Key × TypedSource)} {indices : List IndexSite}
    {places : List PlaceSite} {missing : List MissingSite} (inventory : Inventory sources visited indices places missing)
    {owner : Key} {canonical : TypedSource} (views : QuerySourceViews owner canonical sources)
    (unique : SourceSemantics.NodeOccurrencesUnique canonical) {node : ExpressionNode}
    (contains : SourceSemantics.ContainsExpression canonical node.id node)
    {selected : IndexSite}
    (found : indices.find? (fun site => decide (site.owner = owner ∧ site.expression = node.id)) = some selected)
    {row : MissingSite} (member : row ∈ missing) (sameReason : row.base = selected.reason) :
    row.owner = owner ∧ row.site = .occurrence node.id.occurrence ∧ row.binder = none ∧ row.span = node.span := by
  have selectedMember := List.mem_of_find?_eq_some found
  have hit : selected.owner = owner ∧ selected.expression = node.id :=
    of_decide_eq_true (List.find?_some (p := fun site : IndexSite => decide (site.owner = owner ∧ site.expression = node.id)) found)
  rcases inventory.origins row member with ⟨actualOwner, source, issuer, sourceMember, owns, issuerContains, receipt⟩ |
    ⟨actualOwner, source, issuer, assignment, _sourceMember, _owns, _issuerContains, receipt⟩
  · obtain ⟨mapping, key, base, keyType, valueType, actualIndex, issuerForm, _lookup, _mappingView, _valueView, actualFound, rowEq⟩ := receipt
    have actualHit : actualIndex.owner = actualOwner ∧ actualIndex.expression = issuer.id :=
      of_decide_eq_true (List.find?_some (p := fun site : IndexSite => decide (site.owner = actualOwner ∧ site.expression = issuer.id)) actualFound)
    have reasonEq : selected.reason = actualIndex.reason := by simpa only [rowEq] using sameReason.symm
    have sameKey := inventory.ownership.index selected selectedMember actualIndex
      (List.mem_of_find?_eq_some actualFound) reasonEq
    have ownerEq : actualOwner = owner := actualHit.1.symm.trans (sameKey.1.symm.trans hit.1)
    have idEq : issuer.id = node.id := actualHit.2.symm.trans (sameKey.2.symm.trans hit.2)
    have view := views actualOwner source sourceMember ownerEq
    rw [idEq] at issuerContains
    obtain ⟨_canonicalForm, span⟩ := view.index_span_at unique contains issuerContains issuerForm
    simp only [rowEq, ownerEq, idEq, span, and_self]
  · obtain ⟨place, key, keyNode, valueType, placeMember, _owner, _location, _binder, kind, _lookup, rowEq⟩ := receipt
    have reasonEq : selected.reason = place.reason := by simpa only [rowEq] using sameReason.symm
    exact False.elim (inventory.ownership.separate selected selectedMember place placeMember valueType kind reasonEq)

/-- Public source coverage retains the suffix from that literal canonical row;
no receiving metadata or runtime value supplies this static acceptance. -/
theorem FactoryAt.expression_missing_at {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : SourceCoreCompatibleFunctions.Prepared checked}
    {diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial checked)}
    (factory : FactoryAt prepared diagnostics) {owner : Key} {row : SourceSpecialization.SpecializedFunction}
    (record : SourceCompilationPlan.exactSpecialization prepared.plan owner = .ok row)
    {node : ExpressionNode} {mapping key : ExpressionId}
    (contains : SourceSemantics.ContainsExpression row.function.typedBody node.id node)
    (form : node.form = .index mapping key) :
    ∃ missing, missing ∈ diagnostics.missing ∧
      ExpressionAt diagnostics.program.expressions.indices owner row.function.typedBody node missing ∧
      missing.base = diagnostics.program.reasonAt owner node.id := by
  obtain ⟨locals0, root, remaining, _roots, _contexts, accepted⟩ := factory.actual
  have inventory := (CompatiblePlaceMissingPreparationRanges.prepare_missing_origins accepted).2
  have member : (owner, row.function.typedBody) ∈ (prepared.plan.specializations.map
      (fun row => (row.key, row.function.typedBody)) ++ prepared.contexts.map (fun item => (item.caller.key, item.source))) := by
    apply List.mem_append_left
    have filtered : row ∈ prepared.plan.specializations.filter (fun actual => decide (actual.key = owner)) := by
      rw [selected_filter record]
      exact List.mem_singleton_self _
    exact List.mem_map.mpr ⟨row, (List.mem_filter.mp filtered).1, by rw [selected_key record]⟩
  obtain ⟨missing, missingMember, receipt⟩ := Inventory.expression_missing_at inventory member contains form
  exact ⟨missing, missingMember, receipt, ExpressionAt.reason_at receipt⟩

/-- Same-token actual expanded rows have the same genuine base; ownership and
Source views then determine occurrence and span independently of raw types. -/
theorem FactoryAt.expanded_row_fields {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : SourceCoreCompatibleFunctions.Prepared checked}
    {diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial checked)}
    (factory : FactoryAt prepared diagnostics) {owner : Key} {function : SourceSpecialization.SpecializedFunction}
    (record : SourceCompilationPlan.exactSpecialization prepared.plan owner = .ok function)
    (unique : SourceSemantics.NodeOccurrencesUnique function.function.typedBody)
    {node : ExpressionNode} (contains : SourceSemantics.ContainsExpression function.function.typedBody node.id node)
    {site : MissingSite} (member : site ∈ diagnostics.missing)
    (receipt : ExpressionAt diagnostics.program.expressions.indices owner function.function.typedBody node site)
    {registry : SourceCoreRawMetadata.Registry}
    (limits : registry.limits.maxEntries = diagnostics.context.registry.limits.maxEntries)
    (budget : registry.length ≤ registry.limits.maxEntries)
    {rawKey rawValue : TypeSystem.Ty} {header : Word}
    (metadata : MetadataRep registry (.mapping rawKey rawValue) header)
    {row : Word × Diagnostic}
    (origin : CompatiblePlaceMissingDiagnosticRows.MissingRow registry diagnostics.missing row)
    (same : row.1 = site.base.add header) :
    row.2.error = .typeMismatch rawValue none ∧ row.2.site = .occurrence node.id.occurrence ∧ row.2.span = some node.span := by
  obtain ⟨locals0, root, remaining, _roots, _contexts, accepted⟩ := factory.actual
  have inventory := (CompatiblePlaceMissingPreparationRanges.prepare_missing_origins accepted).2
  have ranges := (CompatiblePlaceMissingPreparationRanges.prepare_ranges accepted).1
  have actualRanges : CompatiblePlaceMissingDiagnosticAssociation.Ranges registry.limits.maxEntries diagnostics.missing :=
    limits.symm ▸ ranges
  obtain ⟨actual, actualMember, actualKey, actualValue, actualHeader, actualMetadata, _keyView, _valueView,
    actualToken, _actualBound, actualDiagnostic⟩ := origin.metadata
  have leftBound := Nat.le_trans (CompatiblePlaceMissingDiagnosticRows.metadata_headerBound metadata) budget
  have rightBound := Nat.le_trans (CompatiblePlaceMissingDiagnosticRows.metadata_headerBound actualMetadata) budget
  have leftReserved := actualRanges.reserved site member
  have rightReserved := actualRanges.reserved actual actualMember
  have tokens : site.base.add header = actual.base.add actualHeader := same.symm.trans actualToken
  have baseEq : actual.base = site.base := by
    rcases actualRanges.separated site member actual actualMember with equal | before | after
    · exact equal.symm
    · exact False.elim (token_ranges_disjoint _ _ _ _ _ _ leftReserved rightReserved leftBound rightBound before tokens)
    · exact False.elim (token_ranges_disjoint _ _ _ _ _ _ rightReserved leftReserved rightBound leftBound after tokens.symm)
  obtain ⟨mapping, key, base, keyType, valueType, selected, _form, _lookup, _mappingView, _valueView, found, rowEq⟩ := receipt
  have reasonEq : actual.base = selected.reason := by simpa only [rowEq] using baseEq
  have fields := Inventory.row_site_span inventory (factory.source_views record) unique contains found actualMember reasonEq
  refine ⟨CompatiblePlaceMissingDiagnosticAssociation.row_error actualRanges budget member metadata origin same, ?_, ?_⟩
  · rw [actualDiagnostic]
    exact fields.2.1
  · rw [actualDiagnostic, fields.2.2.2]

end Solcore.SourceSemantics.CoreLowering.CompatibleContextualDiagnosticMissingOrigins
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleMissingDiagnosticExtension
/-! Rebuilding missing-value diagnostics preserves the exact first public row
for every already issued token, even though new rows interleave by site. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMissingDiagnosticExtension
open Core Frontend SourceInference CompatiblePayload
open SourceCoreCompatibleDataPlaceFaultSites CompatiblePlaceMissingDiagnosticRows
open CompatiblePlaceMissingDiagnosticAssociation

private abbrev Row := Word × Diagnostic

private def candidate (site : MissingSite) (token : Word)
    (entry : SourceCoreRawMetadata.Metadata × Nat) : Option Row :=
  match entry.1 with
  | .mapping key value =>
      if SourceCoreRawMetadata.runtimeType key = SourceCoreRawMetadata.runtimeType site.keyType ∧
          SourceCoreRawMetadata.runtimeType value = SourceCoreRawMetadata.runtimeType site.valueType ∧
          token.val = site.base.val + entry.2 + 1 then
        some (token, { error := .typeMismatch value none, site := site.site, span := some site.span })
      else none
  | _ => none

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {out : β}
    (accepted : (action >>= next) = .ok out) :
    ∃ value, action = .ok value ∧ next value = .ok out := by
  cases action with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem duplicate_find (rows : List Row) (row : Row) (token : Word) :
    (if rows.any (fun previous => decide (previous.1 = row.1)) then rows else rows ++ [row]).find?
        (fun found => decide (found.1 = token)) =
      (rows.find? (fun found => decide (found.1 = token))).or
        (if row.1 = token then some row else none) := by
  by_cases same : row.1 = token
  · subst token
    by_cases present : rows.any (fun previous => decide (previous.1 = row.1)) = true
    · obtain ⟨old, member, equal⟩ := List.any_eq_true.mp present
      have someFound : (rows.find? (fun found => decide (found.1 = row.1))).isSome :=
        List.find?_isSome.mpr ⟨old, member, equal⟩
      cases found : rows.find? (fun found => decide (found.1 = row.1)) with
      | none => simp [found] at someFound
      | some selected => simp [present, found]
    · simp [present, List.find?_append]
  · split <;> simp [same]

private theorem missing_find {registry : SourceCoreRawMetadata.Registry} {sites : List MissingSite}
    {rows : List Row} (accepted : missingDiagnostics registry sites = .ok rows) (token : Word) :
    rows.find? (fun row => decide (row.1 = token)) =
      sites.findSome? (fun site => registry.entries.zipIdx.findSome? (candidate site token)) := by
  unfold missingDiagnostics at accepted
  split at accepted
  · obtain ⟨updated, loop, finished⟩ := bind_ok accepted
    cases Except.ok.inj finished
    apply CompatibleMemberCertificates.forIn_preserves loop (fun seen output =>
      output.find? (fun row => decide (row.1 = token)) =
        seen.findSome? (fun site => registry.entries.zipIdx.findSome? (candidate site token)))
    · rfl
    · intro seen site remaining state outcome _ previous ran
      obtain ⟨updated, inner, finished⟩ := bind_ok ran
      refine ⟨updated, (Except.ok.inj finished).symm, ?_⟩
      have innerResult : updated.find? (fun row => decide (row.1 = token)) =
          (state.find? (fun row => decide (row.1 = token))).or
            (registry.entries.zipIdx.findSome? (candidate site token)) := by
        apply CompatibleMemberCertificates.forIn_preserves inner (fun seen output =>
          output.find? (fun row => decide (row.1 = token)) =
            (state.find? (fun row => decide (row.1 = token))).or
              (seen.findSome? (candidate site token)))
        · simp
        · intro seen entry remaining current result _ previous ran
          obtain ⟨metadata, index⟩ := entry
          dsimp only at ran
          cases metadata with
          | proxy inner | constructor inner =>
            refine ⟨current, (Except.ok.inj ran).symm, ?_⟩
            simpa [candidate] using previous
          | mapping key value =>
            dsimp only at ran
            split at ran
            · rename_i matched
              have views : SourceCoreRawMetadata.runtimeType key = SourceCoreRawMetadata.runtimeType site.keyType ∧
                  SourceCoreRawMetadata.runtimeType value = SourceCoreRawMetadata.runtimeType site.valueType := by
                simpa only [Bool.and_eq_true, decide_eq_true_eq] using matched
              obtain ⟨reason, generated, finished⟩ := bind_ok ran
              have converted : Word.ofNat? (site.base.val + index + 1) = some reason := by
                change (match Word.ofNat? (site.base.val + index + 1) with
                  | some value => Except.ok value | none => Except.error Error.reasonSpaceExhausted) = .ok reason at generated
                split at generated
                · cases generated; assumption
                · cases generated
              have number : reason.val = site.base.val + index + 1 := by
                unfold Word.ofNat? at converted
                split at converted
                · exact congrArg Fin.val (Option.some.inj converted).symm
                · cases converted
              let row : Row := (reason, {error := .typeMismatch value none, site := site.site, span := some site.span})
              have candidateEq : candidate site token (.mapping key value, index) =
                  (if reason = token then some row else none) := by
                have iffEq : token.val = site.base.val + index + 1 ↔ reason = token := by
                  constructor
                  · intro eq; apply Fin.ext; omega
                  · intro eq; simpa [eq] using number
                simp [candidate, views.1, views.2, iffEq, row]
                split
                · rename_i same; simp [same]
                · rfl
              have nextFind := duplicate_find current row token
              split at finished
              · rename_i present
                refine ⟨current, (Except.ok.inj finished).symm, ?_⟩
                have nextFind := nextFind
                simp only [row, present, ↓reduceIte] at nextFind
                rw [nextFind, previous]
                simp only [List.findSome?_append, List.findSome?_singleton,
                  candidateEq, Option.or_assoc]
                rfl
              · rename_i absent
                refine ⟨_, (Except.ok.inj finished).symm, ?_⟩
                have nextFind := nextFind
                simp only [row, absent, Bool.false_eq_true, ↓reduceIte] at nextFind
                rw [nextFind, previous]
                simp only [List.findSome?_append, List.findSome?_singleton,
                  candidateEq, Option.or_assoc]
                rfl
            · rename_i unmatched
              have notViews : ¬ (SourceCoreRawMetadata.runtimeType key = SourceCoreRawMetadata.runtimeType site.keyType ∧
                  SourceCoreRawMetadata.runtimeType value = SourceCoreRawMetadata.runtimeType site.valueType) := by
                simpa only [Bool.and_eq_true, decide_eq_true_eq] using unmatched
              refine ⟨current, (Except.ok.inj ran).symm, ?_⟩
              have noCandidate : candidate site token (.mapping key value, index) = none := by
                simp only [candidate]
                split
                · rename_i matched; exact False.elim (notViews ⟨matched.1, matched.2.1⟩)
                · rfl
              simpa [noCandidate] using previous
      simpa only [List.findSome?_append, List.findSome?_singleton, previous] using innerResult
  · cases accepted

private theorem findSome_congr {α β : Type} (items : List α) (left right : α → Option β)
    (same : ∀ item, item ∈ items → left item = right item) :
    items.findSome? left = items.findSome? right := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
    rw [List.findSome?_cons, List.findSome?_cons, same head (by simp)]
    cases right head with
    | some => rfl
    | none => exact ih (fun item member => same item (by simp [member]))

/-- Existing tokens select exactly the same first raw diagnostic after a genuine
metadata extension. Newly inserted site-major rows cannot shadow the old token. -/
theorem missingDiagnostics_find_preserved
    {before after : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends before after)
    {sites : List MissingSite} (ranges : Ranges before.limits.maxEntries sites)
    {oldRows newRows : List Row}
    (oldBuilt : missingDiagnostics before sites = .ok oldRows)
    (newBuilt : missingDiagnostics after sites = .ok newRows)
    {token : Word} {row : Row}
    (found : oldRows.find? (fun selected => decide (selected.1 = token)) = some row) :
    newRows.find? (fun selected => decide (selected.1 = token)) = some row := by
  have origin := missingDiagnostics_rows oldBuilt row (List.mem_of_find?_eq_some found)
  have same : row.1 = token := of_decide_eq_true (List.find?_some (p := fun selected : Row => decide (selected.1 = token)) found)
  obtain ⟨original, originalMember, originalIndex, originalKey, originalValue,
    originalStored, _, _, converted, _⟩ := origin
  have tokenNumber : token.val = original.base.val + originalIndex + 1 := by
    unfold Word.ofNat? at converted
    split at converted
    · have number := congrArg Fin.val (Option.some.inj converted).symm
      simpa only [same] using number
    · cases converted
  have originalBound : originalIndex < before.entries.length := by
    have bounded := List.snd_lt_of_mem_zipIdx originalStored
    simpa only [Nat.add_zero] using bounded
  have beforeBudget := missingDiagnostics_budget oldBuilt
  have afterBudget := missingDiagnostics_budget newBuilt
  rw [extension.limits] at afterBudget
  change before.entries.length ≤ before.limits.maxEntries at beforeBudget
  change after.entries.length ≤ before.limits.maxEntries at afterBudget
  obtain ⟨suffix, appended⟩ := extension.suffix
  have suffixNoMatch : ∀ site, site ∈ sites →
      (suffix.zipIdx before.entries.length).findSome? (candidate site token) = none := by
    intro site member
    apply List.findSome?_eq_none_iff.mpr
    intro entry stored
    have lower := List.le_snd_of_mem_zipIdx stored
    have upper := List.snd_lt_of_mem_zipIdx stored
    have afterLength : after.entries.length = before.entries.length + suffix.length := by simp [appended]
    have numeric : token.val ≠ site.base.val + entry.2 + 1 := by
      intro equal
      rcases ranges.separated original originalMember site member with bases | first | last
      · have bases := congrArg Fin.val bases
        omega
      · omega
      · omega
    obtain ⟨metadata, index⟩ := entry
    cases metadata with
    | proxy inner | constructor inner => rfl
    | mapping key value =>
      dsimp only [candidate]
      split
      · rename_i matched
        exact False.elim (numeric matched.2.2)
      · rfl
  have scans : sites.findSome? (fun site => after.entries.zipIdx.findSome? (candidate site token)) =
      sites.findSome? (fun site => before.entries.zipIdx.findSome? (candidate site token)) := by
    apply findSome_congr
    intro site member
    rw [appended, List.zipIdx_append, List.findSome?_append]
    simp only [Nat.zero_add, suffixNoMatch site member, Option.or_none]
  rw [missing_find newBuilt token, scans, ← missing_find oldBuilt token]
  exact found

end Solcore.SourceSemantics.CoreLowering.CompatibleMissingDiagnosticExtension
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleGeneralIndexTree
/-! General mapping index chains over the full existing typed expression
fragment. Static receipts retain raw mapping types and the actual comparator;
compound keys require no additional runtime operation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleGeneralIndex
open Core Frontend SourceInference
open CompatibleExpressionIndices (Header)
abbrev ValuesContext := SourceCoreCompatibleValues.Context
abbrev Scope := SourceCoreLocalCell.Scope

inductive Syntax (source : TypedSource) : ExpressionId → Prop where
  | fragment {id} (tree : CompatibleExpressionTyped.Syntax source id) : Syntax source id
  | index {id node base key keyNode} (found : source.lookupExpression? id = some node)
      (form : node.form = .index base key) (keyFound : source.lookupExpression? key = some keyNode)
      (first : Syntax source base) (second : Syntax source key) : Syntax source id

inductive Tree (fuel : Nat) (values : ValuesContext) (source : TypedSource)
    (context : SourceSemantics.Context) (solved : List SolvedRequirement)
    (reasonAt : ExpressionId → Word) (scope : Scope) :
    ExpressionId → SourceCoreBasic.LoweredExpr → Prop where
  | fragment {id lowered}
      (tree : CompatibleExpressionTyped.Tree fuel values source context solved reasonAt scope id lowered) :
      Tree fuel values source context solved reasonAt scope id lowered
  | index {id node base key baseNode keyNode layout comparison first second}
      (header : Header values source id base node baseNode layout comparison first second)
      (keyFound : source.lookupExpression? key = some keyNode)
      (form : node.form = .index base key)
      (sourceType : baseNode.type = .mapping keyNode.type node.type)
      (firstTree : Tree fuel values source context solved reasonAt scope base first)
      (secondTree : Tree fuel values source context solved reasonAt scope key second) :
      Tree fuel values source context solved reasonAt scope id
        ⟨layout.valueType, SourceCoreCompatibleDataExpressions.index layout comparison.expression first.expression second.expression (reasonAt id)⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleGeneralIndex
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleGeneralIndexMeaning
/-! Whole finite index trees evaluate base, then key, then the actual generated
comparator. Every child meaning is discharged by structural induction; actual
hidden slots are typed because comparator closures capture those slots. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleGeneralIndex
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CompatibleMapping
open GenericExpressionMeaning (agree_prefix rename_prefix)
open CompatibleExpressionIndices (index_inv index_intro index_rename)

variable {fuel : Nat} {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
  (unique : NodeOccurrencesUnique source) {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

include unique in
theorem preserves_with_post {post : ExpressionFailurePostContracts.ExpressionFaultPost}
    (fragment : ExpressionFailurePostContracts.TypedPreserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (CompatibleExpressionTyped.Tree fuel values source context solved reasonAt) faults post)
    (terminalProvider : IndexFaultPostContracts.TerminalProvider values source functions registry program context evidence
      reasonAt (fun _ => True) faults post)
    (joins : IndexFaultPostContracts.IndexJoins post values program context evidence source) :
    ExpressionFailurePostContracts.TypedPreserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Tree fuel values source context solved reasonAt) faults post := by
  intro scope id lowered tree
  induction tree with
  | fragment child =>
    exact fragment child
  | @index id node base key baseNode keyNode layout comparison first second header keyFound form sourceType firstTree secondTree firstIH secondIH =>
    intro root found mapping world administrative environment canonical actual actualContext before store ξ outcome after
      environments heaps locals agrees actualTyped trace
    have same := Option.some.inj (header.metadata.found.symm.trans found)
    subst root
    rcases (index_inv header.metadata form unique trace).split with ⟨reason, rfl, failed⟩ | ⟨baseSource, middle, baseTrace, tail⟩
    · obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, childPost⟩ :=
        firstIH header.baseMetadata.found environments heaps locals agrees actualTyped (.fault failed)
      cases represented with
      | fault matched =>
        refine ⟨_, finalStore, finalMap, finalWorld, ?_, .fault matched, finalHeaps, maps, worlds, frame, metadata,
          joins.base_outcome header keyFound form sourceType failed childPost⟩
        rw [index_rename comparison header.registered header.comparisonType]
        exact LanguageResult.bind_failure _ evaluated
    · obtain ⟨value, middleStore, middleMap, middleWorld, firstEval, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, _firstPost⟩ :=
        firstIH header.baseMetadata.found environments heaps locals agrees actualTyped (.value baseTrace)
      cases represented with
      | @value _ baseValue baseRep =>
        have keyEnvironment := RuntimeEnvironmentHasTypes.cons baseRep.runtime_hasType (actualTyped.weaken firstWorlds)
        rcases tail with ⟨reason, rfl, failed⟩ | ⟨keySource, keyTrace, terminal⟩
        · obtain ⟨value, finalStore, finalMap, finalWorld, secondEval, represented, finalHeaps, maps, worlds, frame, metadata, childPost⟩ :=
            secondIH keyFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (agree_prefix agrees _) keyEnvironment (.fault failed)
          cases represented with
          | fault matched =>
            refine ⟨_, finalStore, finalMap, finalWorld, ?_, .fault matched, finalHeaps,
              firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata,
              joins.key_outcome header keyFound form sourceType baseTrace failed childPost⟩
            rw [index_rename comparison header.registered header.comparisonType]
            rw [rename_prefix] at secondEval
            exact LanguageResult.bind_success _ firstEval (LanguageResult.bind_failure _ secondEval)
        · obtain ⟨value, keyStore, keyMap, keyWorld, secondEval, represented, keyHeaps, keyMaps, keyWorlds, keyFrame, keyMetadata, _keyPost⟩ :=
            secondIH keyFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (agree_prefix agrees _) keyEnvironment (.value keyTrace)
          cases represented with
          | @value _ keyValue keyRep =>
            obtain ⟨actualOutcome, result, finalStore, finalWorld, terminal', related, lookup, finalHeaps, worlds, frame, uniqueResult, _terminalTrace, terminalPost⟩ :=
              terminalProvider header sourceType True.intro (baseRep.extend (.refl _) keyMaps keyWorlds) keyRep
                (actualTyped.weaken (firstWorlds.trans keyWorlds)) keyHeaps keyFound form baseTrace keyTrace
            have same := uniqueResult outcome terminal
            subst actualOutcome
            refine ⟨result, finalStore, keyMap, finalWorld, ?_, related, finalHeaps,
              firstMaps.trans keyMaps, (firstWorlds.trans keyWorlds).trans worlds,
              (firstFrame.trans keyFrame).trans frame, firstMetadata.trans keyMetadata, terminalPost⟩
            rw [index_rename comparison header.registered header.comparisonType]
            rw [rename_prefix] at secondEval
            apply SourceCoreCompatibleDataExpressions.index_completed layout (reasonAt id) firstEval secondEval
            simpa only [Transport.expression_weaken] using lookup

theorem reflects_with_post {post : ExpressionFailurePostContracts.ExpressionFaultPost}
    (fragment : ExpressionFailurePostContracts.TypedReflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (CompatibleExpressionTyped.Tree fuel values source context solved reasonAt) faults post)
    (terminalProvider : IndexFaultPostContracts.TerminalProvider values source functions registry program context evidence
      reasonAt (fun _ => True) faults post)
    (joins : IndexFaultPostContracts.IndexJoins post values program context evidence source) :
    ExpressionFailurePostContracts.TypedReflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Tree fuel values source context solved reasonAt) faults post := by
  intro scope id lowered tree
  induction tree with
  | fragment child =>
    exact fragment child
  | @index id node base key baseNode keyNode layout comparison first second header keyFound form sourceType firstTree secondTree firstIH secondIH =>
    intro root found mapping world administrative environment canonical actual actualContext before store ξ value finalStore
      environments heaps locals agrees actualTyped evaluated
    have same := Option.some.inj (header.metadata.found.symm.trans found)
    subst root
    rw [index_rename comparison header.registered header.comparisonType] at evaluated
    have complete := evaluated
    cases evaluated with
    | caseLeft baseEvaluation branch =>
      obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, childPost⟩ :=
        firstIH header.baseMetadata.found environments heaps locals agrees actualTyped baseEvaluation
      cases represented with
      | fault matched =>
        have expected := LanguageResult.bind_failure layout.valueType baseEvaluation (body :=
          LanguageResult.bind layout.valueType ((second.expression.rename ξ).weakenAt 0)
            (SourceCoreMappingWithDefault.lookup layout (reasonAt id) (comparison.expression.weakenAt 0 |>.weakenAt 0) (.var 1) (.var 0)))
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete expected
        cases trace with
        | fault failed => exact ⟨_, after, finalMap, finalWorld, index_intro header.metadata form (.baseFailure failed),
            .fault matched, finalHeaps, maps, worlds, frame, metadata,
            joins.base_outcome header keyFound form sourceType failed childPost⟩
    | caseRight baseEvaluation branch =>
      obtain ⟨outcome, middle, middleMap, middleWorld, trace, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, _firstPost⟩ :=
        firstIH header.baseMetadata.found environments heaps locals agrees actualTyped baseEvaluation
      cases represented with
      | @value baseSource baseValue baseRep =>
        cases trace with
        | value baseTrace =>
          have keyEnvironment := RuntimeEnvironmentHasTypes.cons baseRep.runtime_hasType (actualTyped.weaken firstWorlds)
          cases branch with
          | caseLeft keyEvaluation ignored =>
            rw [← rename_prefix] at keyEvaluation
            obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, childPost⟩ :=
              secondIH keyFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                (agree_prefix agrees _) keyEnvironment keyEvaluation
            cases represented with
            | fault matched =>
              rw [rename_prefix] at keyEvaluation
              have expected := LanguageResult.bind_success layout.valueType baseEvaluation
                (LanguageResult.bind_failure layout.valueType keyEvaluation (body :=
                  SourceCoreMappingWithDefault.lookup layout (reasonAt id) (comparison.expression.weakenAt 0 |>.weakenAt 0) (.var 1) (.var 0)))
              obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete expected
              cases trace with
              | fault failed => exact ⟨_, after, finalMap, finalWorld, index_intro header.metadata form (.keyFailure baseTrace failed),
                  .fault matched, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata,
                  joins.key_outcome header keyFound form sourceType baseTrace failed childPost⟩
          | caseRight keyEvaluation lookupEvaluation =>
            rw [← rename_prefix] at keyEvaluation
            obtain ⟨outcome, after, keyMap, keyWorld, trace, represented, keyHeaps, keyMaps, keyWorlds, keyFrame, keyMetadata, _keyPost⟩ :=
              secondIH keyFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                (agree_prefix agrees _) keyEnvironment keyEvaluation
            cases represented with
            | @value keySource keyValue keyRep =>
              cases trace with
              | value keyTrace =>
                obtain ⟨outcome, result, endStore, finalWorld, terminal, related, lookup, finalHeaps, worlds, frame, uniqueResult, _terminalTrace, terminalPost⟩ :=
                  terminalProvider header sourceType True.intro (baseRep.extend (.refl _) keyMaps keyWorlds) keyRep
                    (actualTyped.weaken (firstWorlds.trans keyWorlds)) keyHeaps keyFound form baseTrace keyTrace
                rw [rename_prefix] at keyEvaluation
                have expected := SourceCoreCompatibleDataExpressions.index_completed (comparison := comparison.expression) layout (reasonAt id) baseEvaluation keyEvaluation
                  (by simpa only [Transport.expression_weaken] using lookup)
                obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete expected
                exact ⟨outcome, after, keyMap, finalWorld, index_intro header.metadata form (terminal.trace baseTrace keyTrace),
                    related, finalHeaps, firstMaps.trans keyMaps, (firstWorlds.trans keyWorlds).trans worlds,
                    (firstFrame.trans keyFrame).trans frame, firstMetadata.trans keyMetadata, terminalPost⟩

include extension faithful functionLeaves functionTypes valid unique uninitialized missing in
theorem preserves [FunctionCalls.FaultTokens faults] :
    TypedGenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Tree fuel values source context solved reasonAt) faults := by
  exact ExpressionFailurePostContracts.TypedPreserves.forget
    (preserves_with_post (functions := functions) (program := program) (evidence := evidence) (unique := unique)
      (ExpressionFailurePostContracts.TypedPreserves.of_trivial
        (CompatibleExpressionTyped.preserves functions extension program evidence valid unique uninitialized missing))
      (IndexFaultPostContracts.trivial_general_terminal functions registry program context evidence reasonAt faithful functionLeaves functionTypes missing)
      (IndexFaultPostContracts.trivial_index_joins values program context evidence source))

include extension faithful functionLeaves functionTypes valid uninitialized missing in
theorem reflects [FunctionCalls.FaultTokens faults] :
    TypedGenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Tree fuel values source context solved reasonAt) faults := by
  exact ExpressionFailurePostContracts.TypedReflects.forget
    (reflects_with_post (functions := functions) (program := program) (evidence := evidence)
      (ExpressionFailurePostContracts.TypedReflects.of_trivial
        (CompatibleExpressionTyped.reflects functions extension program evidence valid uninitialized missing))
      (IndexFaultPostContracts.trivial_general_terminal functions registry program context evidence reasonAt faithful functionLeaves functionTypes missing)
      (IndexFaultPostContracts.trivial_index_joins values program context evidence source))

end Solcore.SourceSemantics.CoreLowering.CompatibleGeneralIndex
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleGeneralIndexCertificates
/-! Accepted ordinary index lowering supplies the entire static tree. Raw
mapping/key types follow independent source typing, while the real compiler
supplies comparator preparation and registered layout receipts. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleGeneralIndex
open Core Frontend SourceInference
open CompatibleExpressionReads (ScopeDeclarations)
open CompatibleExpressionIndices (index_source_types index_of_functions)

structure PolicyFor (policy : SourceCoreFunctions.Policy) (context : SourceCoreFunctions.Context)
    (readFuel : Nat) (values : ValuesContext) (source : TypedSource) (scope : Scope)
    (reasonAt : ExpressionId → Word) : Prop where
  special : ∀ id, Syntax source id → ∀ child budget, (match policy.lowerSpecial? with
    | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
    | some lower => lower context child budget source scope id reasonAt) = .ok none
  read : ∀ id, Syntax source id → policy.readExpression source id =
    SourceCoreCompatibleDataExpressions.readExpression values.checked source id
  lower : policy.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values
  leaf : policy.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values

theorem tree_of_functions
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {readFuel : Nat} {context : SourceCoreFunctions.Context} {values : ValuesContext}
    {source : TypedSource} {scope : Scope} {reasonAt : ExpressionId → Word} {sourceContext : SourceSemantics.Context}
    (unique : NodeOccurrencesUnique source)
    (declarations : ScopeDeclarations source scope sourceContext)
    (signatures : sourceContext.signatures = values.checked.signatures)
    (closed : sourceContext.typeVariables = []) (residual : sourceContext.residualTypeVariables = false)
    (policyFor : PolicyFor policy context readFuel values source scope reasonAt)
    (coercions : ∀ id node, Syntax source id → source.lookupExpression? id = some node → node.coercions = [])
    {id : ExpressionId} (syntaxTree : Syntax source id) {node : ExpressionNode}
    (found : source.lookupExpression? id = some node) (typed : ExpressionHasType source sourceContext id node.type)
    {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope id reasonAt = .ok lowered) :
    Tree readFuel values source sourceContext context.solvedRequirements reasonAt scope id lowered := by
  induction syntaxTree generalizing node fuel lowered with
  | fragment syntaxTree =>
    refine .fragment (CompatibleExpressionTyped.tree_of_functions unique declarations signatures closed residual ?_ ?_ syntaxTree found typed accepted)
    · exact ⟨fun id child => policyFor.special id (.fragment child), fun id child => policyFor.read id (.fragment child), policyFor.lower, policyFor.leaf⟩
    · exact fun id node child => coercions id node (.fragment child)
  | @index id original base key keyNode originalFound form keyFound firstSyntax secondSyntax firstIH secondIH =>
    have same := Option.some.inj (originalFound.symm.trans found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      have syntaxTree : Syntax source id := .index originalFound form keyFound firstSyntax secondSyntax
      obtain ⟨keyType, baseTyped, keyTyped⟩ := index_source_types unique originalFound form
        (coercions _ _ syntaxTree originalFound) typed
      obtain ⟨baseNode, baseContains, baseType⟩ := baseTyped.stored_type
      obtain ⟨actualKeyNode, keyContains, actualKeyType⟩ := keyTyped.stored_type
      have keySame := Option.some.inj ((lookupExpression?_complete unique keyContains).symm.trans keyFound)
      subst actualKeyNode
      have baseFound := lookupExpression?_complete unique baseContains
      rw [← actualKeyType] at keyTyped baseType baseTyped
      rw [← baseType] at baseTyped
      obtain ⟨layout, comparison, first, second, rfl, header, firstGenerated, secondGenerated⟩ :=
        index_of_functions originalFound baseFound form
          (policyFor.special _ syntaxTree) (policyFor.read _ syntaxTree) policyFor.leaf accepted
      exact .index header keyFound form baseType (firstIH baseFound baseTyped firstGenerated)
        (secondIH keyFound keyTyped secondGenerated)

end Solcore.SourceSemantics.CoreLowering.CompatibleGeneralIndex
end
