import Solcore.SourceSemantics.CoreLowering.CompatiblePathFaultToken

/-! The actual unavailable index is a suffix of the same certified path.
Its raw mapping fields, lookup, owning header and static type views remain
attached to that exact Source/site/position and generated native index. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMixedRoute
open Core Frontend SourceInference SourceCoreCompatibleDataPlaces CompatiblePayload
open CompatibleMapping CompatibleMapping.MixedPaths

/-- Membership retains the genuine prepared path receipt at every prefix. -/
inductive IndexInPath {checked : Checked} {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
    {terminalRoot terminalLeaf : TypeSystem.Ty} {terminalProjections : List PlaceProjection}
    {terminalPosition : Nat} {terminalSteps : List PreparedStep} {terminalKeys : List (ExpressionId × Ty)}
    (terminal : PreparedPath checked source site terminalRoot terminalProjections terminalPosition
      terminalSteps terminalKeys terminalLeaf) :
    {root : TypeSystem.Ty} → {projections : List PlaceProjection} → {position : Nat} →
    {steps : List PreparedStep} → {keys : List (ExpressionId × Ty)} → {leaf : TypeSystem.Ty} →
    PreparedPath checked source site root projections position steps keys leaf → Prop where
  | here : IndexInPath terminal terminal
  | member {root field leaf name index signature arguments identity branches fieldType projections steps position keys}
      {nominal : SourceCoreDataCatalog.nominalParts (SourceCoreRawMetadata.runtimeType root) = some (signature.id, arguments)}
      {selected : checked.signatures.dataTypes.filter (fun data => decide (data.id = signature.id)) = [signature]}
      {certificate : CompatibleMemberCertificates.Certificate checked site (SourceCoreRawMetadata.runtimeType root)
        field signature arguments index identity branches fieldType}
      {tail : PreparedPath checked source site field projections position steps keys leaf}
      (found : IndexInPath terminal tail) :
      IndexInPath terminal (.member (name := name) nominal selected certificate tail)
  | index {root keySource valueSource leaf key layout projections steps position keys comparison missing}
      {certificate : IndexSite checked source root keySource valueSource key layout}
      {generated : CompatibleMapping.Index checked ⟨layout, key, position, comparison, missing⟩}
      {tail : PreparedPath checked source site valueSource projections (position + 1) steps keys leaf}
      (found : IndexInPath terminal tail) : IndexInPath terminal (.index certificate generated tail)

/-- This existential retains the actual terminal mapping and lookup rather
than interpreting arbitrary raw metadata carrying the same numeric token. -/
def MissingTerminal {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) (mapping : GeneralHeap.LocationMap) (world : StoreTyping)
    {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
    {root leaf : TypeSystem.Ty} {projections : List PlaceProjection} {position : Nat}
    {steps : List PreparedStep} {keys : List (ExpressionId × Ty)}
    (path : PreparedPath checked source site root projections position steps keys leaf)
    (reason : Dynamic.SemanticFault) (token : Word) : Prop :=
  ∃ terminalRoot keySource valueSource terminalLeaf key layout terminalProjections terminalSteps terminalPosition
      terminalKeys comparison missing,
    ∃ (certificate : IndexSite checked source terminalRoot keySource valueSource key layout)
      (generated : CompatibleMapping.Index checked ⟨layout, key, terminalPosition, comparison, missing⟩)
      (tail : PreparedPath checked source site valueSource terminalProjections (terminalPosition + 1)
        terminalSteps terminalKeys terminalLeaf),
      IndexInPath (.index certificate generated tail) path ∧
      ∃ rawKey rawValue entries header nativeEntries fallback lookup,
        Fields checked registry functions mapping world rawKey rawValue entries header layout nativeEntries fallback ∧
        keySource = SourceCoreRawMetadata.runtimeType rawKey ∧
        valueSource = SourceCoreRawMetadata.runtimeType rawValue ∧
        Dynamic.ValueRuntimeTypeMatches lookup rawKey ∧ Dynamic.MappingAbsent lookup entries ∧
        ¬ Dynamic.Defaultable rawValue ∧ reason = .missingMappingDefault rawValue ∧ token = missing.add header

/-- A genuine member prefix forwards the same terminal witness. -/
theorem MissingTerminal.member {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
    {root field leaf name index signature arguments identity branches fieldType projections steps position keys}
    {nominal : SourceCoreDataCatalog.nominalParts (SourceCoreRawMetadata.runtimeType root) = some (signature.id, arguments)}
    {selected : checked.signatures.dataTypes.filter (fun data => decide (data.id = signature.id)) = [signature]}
    {certificate : CompatibleMemberCertificates.Certificate checked site (SourceCoreRawMetadata.runtimeType root)
      field signature arguments index identity branches fieldType}
    {tail : PreparedPath checked source site field projections position steps keys leaf}
    {reason : Dynamic.SemanticFault} {token : Word}
    (terminal : MissingTerminal (registry := registry) functions mapping world tail reason token) :
    MissingTerminal (registry := registry) functions mapping world (.member (name := name) nominal selected certificate tail) reason token := by
  obtain ⟨a, b, c, d, e, f, g, h, i, j, k, l, terminalCertificate, terminalGenerated, rest, found, raw⟩ := terminal
  exact ⟨a, b, c, d, e, f, g, h, i, j, k, l, terminalCertificate, terminalGenerated, rest,
    IndexInPath.member (nominal := nominal) (selected := selected) (certificate := certificate) found, raw⟩

/-- A genuine successful index prefix forwards the same terminal witness. -/
theorem MissingTerminal.index {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
    {root keySource valueSource leaf key layout projections steps position keys comparison missing}
    {certificate : IndexSite checked source root keySource valueSource key layout}
    {generated : CompatibleMapping.Index checked ⟨layout, key, position, comparison, missing⟩}
    {tail : PreparedPath checked source site valueSource projections (position + 1) steps keys leaf}
    {reason : Dynamic.SemanticFault} {token : Word}
    (terminal : MissingTerminal (registry := registry) functions mapping world tail reason token) :
    MissingTerminal (registry := registry) functions mapping world (.index certificate generated tail) reason token := by
  obtain ⟨a, b, c, d, e, f, g, h, i, j, k, l, terminalCertificate, terminalGenerated, rest, found, raw⟩ := terminal
  exact ⟨a, b, c, d, e, f, g, h, i, j, k, l, terminalCertificate, terminalGenerated, rest,
    IndexInPath.index (certificate := certificate) (generated := generated) found, raw⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleMixedRoute
