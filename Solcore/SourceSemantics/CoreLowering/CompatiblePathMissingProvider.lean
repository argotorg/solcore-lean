import Solcore.SourceSemantics.CoreLowering.CompatiblePathMissingTerminal
import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceKeyTyping
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPlaceAdmission

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
