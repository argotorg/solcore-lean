import Solcore.SourceSemantics.CoreLowering.CompatibleMixedPreparation

/-! Actual compatible route compilation produces source-independent path
receipts. Member rows retain raw-field views; index rows retain actual key
occurrences, catalog layout and source/native projection checks. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMixedRoute
open Core Frontend SourceInference SourceCoreCompatibleDataPlaces

private theorem project_facts {checked : Checked} {site : SourceCoreElaboration.ErrorSite}
    {source : TypeSystem.Ty} {type : Ty} (accepted : project checked site source = .ok type) :
    checked.catalog.project source = .ok type ∧ type.WellFormed checked.catalog.definitions := by
  unfold project SourceCoreCompatibleDataExpressions.projectType SourceCoreCompatibleCatalog.Checked.project at accepted
  cases generated : checked.catalog.project source with
  | error error => simp [generated, bind, Except.bind, Except.map, Except.mapError] at accepted
  | ok native =>
    simp only [generated, bind, Except.bind] at accepted
    split at accepted
    · rename_i valid
      simp only [pure, Except.pure, Except.map, Except.mapError, Except.ok.injEq] at accepted
      subst type
      exact ⟨rfl, Ty.isWellFormed_sound valid⟩
    · cases accepted

structure IndexSite (checked : Checked) (source : TypedSource)
    (root keySource valueSource : TypeSystem.Ty) (key : ExpressionId) (layout : OrderedMapping.Layout) : Prop where
  view : SourceCoreRawMetadata.runtimeType root = .mapping keySource valueSource
  owner : key.occurrence.owner = source.owner
  node : ∃ node, source.lookupExpression? key = some node ∧ checked.catalog.project node.type = .ok layout.keyType
  keyProjection : checked.catalog.project keySource = .ok layout.keyType
  valueProjection : checked.catalog.project valueSource = .ok layout.valueType
  identity : checked.catalog.identity? root = some layout.dataType
  registered : layout.Registered checked.catalog.definitions

inductive Path (checked : Checked) (source : TypedSource) (site : SourceCoreElaboration.ErrorSite) :
    TypeSystem.Ty → List PlaceProjection → List Step → TypeSystem.Ty → Prop where
  | nil {type} : Path checked source site type [] [] type
  | member {root field leaf name index signature arguments identity branches fieldType projections steps}
      (nominal : SourceCoreDataCatalog.nominalParts (SourceCoreRawMetadata.runtimeType root) = some (signature.id, arguments))
      (selected : checked.signatures.dataTypes.filter (fun data => decide (data.id = signature.id)) = [signature])
      (certificate : CompatibleMemberCertificates.Certificate checked site (SourceCoreRawMetadata.runtimeType root)
        field signature arguments index identity branches fieldType)
      (tail : Path checked source site field projections steps leaf) :
      Path checked source site root (.member name index :: projections) (.member identity index branches fieldType :: steps) leaf
  | index {root keySource valueSource leaf key layout projections steps}
      (certificate : IndexSite checked source root keySource valueSource key layout)
      (tail : Path checked source site valueSource projections steps leaf) :
      Path checked source site root (.index key :: projections) (.index layout key valueSource :: steps) leaf

private theorem member_facts {checked : Checked} {site : SourceCoreElaboration.ErrorSite}
    {binder : Resolved.LocalId} {root field : TypeSystem.Ty} {index : Nat} {step : Step}
    (accepted : memberStep checked checked.signatures site binder root index = .ok (step, field)) :
    ∃ signature arguments identity branches fieldType,
      SourceCoreDataCatalog.nominalParts (SourceCoreRawMetadata.runtimeType root) = some (signature.id, arguments) ∧
      checked.signatures.dataTypes.filter (fun data => decide (data.id = signature.id)) = [signature] ∧
      step = .member identity index branches fieldType ∧
      CompatibleMemberCertificates.Certificate checked site (SourceCoreRawMetadata.runtimeType root)
        field signature arguments index identity branches fieldType := by
  have whole := accepted
  unfold memberStep at accepted
  cases nominal : SourceCoreDataCatalog.nominalParts (SourceCoreRawMetadata.runtimeType root) with
  | none => simp [nominal, throw, bind, Except.bind] at accepted
  | some parts =>
    obtain ⟨declaration, arguments⟩ := parts
    simp only [nominal, pure, Except.pure, bind, Except.bind] at accepted
    cases selected : checked.signatures.dataTypes.filter (fun data => decide (data.id = declaration)) with
    | nil => simp [selected, throw] at accepted
    | cons signature rest => cases rest with
      | cons other rest => simp [selected, throw] at accepted
      | nil =>
        have member : signature ∈ checked.signatures.dataTypes.filter (fun data => decide (data.id = declaration)) := by rw [selected]; simp
        have sourceId : signature.id = declaration := by simpa using (List.mem_filter.mp member).2
        have nominal : SourceCoreDataCatalog.nominalParts (SourceCoreRawMetadata.runtimeType root) = some (signature.id, arguments) := by simpa only [sourceId] using nominal
        have selected : checked.signatures.dataTypes.filter (fun data => decide (data.id = signature.id)) = [signature] := by simpa only [sourceId] using selected
        obtain ⟨identity, branches, fieldType, shape, certificate⟩ :=
          CompatibleMemberCertificates.certificate_of_memberStep nominal selected whole
        exact ⟨signature, arguments, identity, branches, fieldType, by simp only [sourceId], selected, shape, certificate⟩

private theorem ensureType_ok {site : SourceCoreElaboration.ErrorSite} {expected actual : Ty}
    (accepted : SourceCoreBasic.ensureType site expected actual = .ok ()) : expected = actual := by
  unfold SourceCoreBasic.ensureType at accepted
  split at accepted
  · assumption
  · cases accepted

/-- Extraction follows actual routeSteps; it neither evaluates keys nor
assumes a source-expression compiler or a helper evaluation. -/
theorem of_routeSteps {checked : Checked} {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
    {binder : Resolved.LocalId} {root leaf : TypeSystem.Ty} {projections : List PlaceProjection} {steps : List Step}
    (accepted : routeSteps checked checked.signatures source site binder root projections = .ok (steps, leaf)) :
    Path checked source site root projections steps leaf := by
  induction projections generalizing root steps leaf with
  | nil =>
    simp only [routeSteps, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at accepted
    obtain ⟨rfl, rfl⟩ := accepted
    exact .nil
  | cons projection projections ih =>
    cases projection with
    | member name index =>
      simp only [routeSteps] at accepted
      obtain ⟨⟨step, field⟩, generated, accepted⟩ := CompatibleEncoding.bind_ok accepted
      obtain ⟨signature, arguments, identity, branches, fieldType, nominal, selected, rfl, certificate⟩ := member_facts generated
      obtain ⟨⟨rest, selectedLeaf⟩, restGenerated, accepted⟩ := CompatibleEncoding.bind_ok accepted
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at accepted
      obtain ⟨rfl, rfl⟩ := accepted
      exact .member nominal selected certificate (ih restGenerated)
    | index key =>
      simp only [routeSteps] at accepted
      cases view : SourceCoreRawMetadata.runtimeType root <;> try (simp [view, throw, throwThe, bind, Except.bind] at accepted)
      case mapping keySource valueSource =>
        simp only [pure, Except.pure] at accepted
        by_cases owner : key.occurrence.owner = source.owner
        · simp only [owner, ↓reduceIte] at accepted
          cases nodeFound : source.lookupExpression? key with
          | none => simp [nodeFound] at accepted
          | some node =>
            simp only [nodeFound] at accepted
            obtain ⟨nodeType, nodeProjected, accepted⟩ := CompatibleEncoding.bind_ok accepted
            obtain ⟨keyType, keyProjected, accepted⟩ := CompatibleEncoding.bind_ok accepted
            obtain ⟨checkedUnit, typesEqual, remainder⟩ := CompatibleEncoding.bind_ok accepted
            have unitEq : checkedUnit = () := Subsingleton.elim _ _
            have same := ensureType_ok (unitEq ▸ typesEqual)
            rw [← same] at nodeProjected
            obtain ⟨valueType, valueProjected, accepted⟩ := CompatibleEncoding.bind_ok remainder
            cases identity : checked.catalog.identity? root with
            | none => simp [identity] at accepted
            | some dataType =>
              simp only [identity] at accepted
              split at accepted
              · rename_i registered
                obtain ⟨⟨rest, selectedLeaf⟩, restGenerated, accepted⟩ := CompatibleEncoding.bind_ok accepted
                simp only [Except.ok.injEq, Prod.mk.injEq] at accepted
                obtain ⟨rfl, rfl⟩ := accepted
                exact .index ⟨view, owner, ⟨node, nodeFound, (project_facts nodeProjected).1⟩,
                  (project_facts keyProjected).1, (project_facts valueProjected).1,
                  identity, ⟨(project_facts keyProjected).2, (project_facts valueProjected).2, registered⟩⟩ (ih restGenerated)
              · cases accepted
        · simp [owner] at accepted

end Solcore.SourceSemantics.CoreLowering.CompatibleMixedRoute
