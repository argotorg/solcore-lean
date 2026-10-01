import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionContextualConstructors
import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceKeyTyping

/-! Independent uniform-field typing fixes original field views. Compiler rows
may erase staging in their native types, but raw source types are aligned by
the retained source substitution and catalog membership instead. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionMembers
open Core Frontend SourceInference DataPatternValues CompatibleConstructorMetadata
abbrev ValuesContext := SourceCoreCompatibleValues.Context
abbrev Scope := SourceCoreLocalCell.Scope
abbrev Child := SourceCoreFunctions.ExpressionLowerer
abbrev Branch := SourceCoreCompatibleDataPlaces.MemberBranch

/-- A source-only property of the canonical metadata rows, with no evaluation
or native type equality premise. -/
def FieldViews (signature : ProgramDataSignature) (arguments : List TypeSystem.Ty)
    (index : Nat) (field : TypeSystem.Ty) : Prop :=
  ∀ constructor ∈ signature.constructors, ∃ actual,
    (constructor.payloadTypes.map (TypeSystem.ParameterSubstitution.apply (signature.parameters.zip arguments)))[index]? = some actual ∧
      SourceCoreRawMetadata.runtimeType actual = SourceCoreRawMetadata.runtimeType field

theorem field_views {checked : SourceCoreCompatibleCatalog.Checked} {context : SourceSemantics.Context}
    (signatures : context.signatures = checked.signatures)
    {base field : TypeSystem.Ty} {index : Nat} {signature : ProgramDataSignature} {arguments : List TypeSystem.Ty}
    (nominal : SourceCoreDataCatalog.nominalParts (SourceCoreRawMetadata.runtimeType base) = some (signature.id, arguments))
    (selected : checked.signatures.dataTypes.filter (fun data => decide (data.id = signature.id)) = [signature])
    (typed : UniformMemberProjection context base index field) : FieldViews signature arguments index field := by
  cases typed with
  | @intro _ _ dataType substitution member exact baseEq _ _ _ uniform _ =>
    rw [baseEq, runtimeType_nominal, DataPatternAuthenticity.nominalParts_nominal] at nominal
    obtain ⟨sameId, sameArguments⟩ := Prod.mk.inj (Option.some.inj nominal)
    have selectedMember : dataType ∈ checked.signatures.dataTypes.filter (fun data => decide (data.id = signature.id)) :=
      List.mem_filter.mpr ⟨signatures ▸ member, by simpa using sameId⟩
    rw [selected] at selectedMember
    have sameSignature : dataType = signature := List.mem_singleton.mp selectedMember
    subst dataType
    rw [← sameArguments]
    intro constructor member
    have found := uniform constructor member
    have lists :
        (constructor.payloadTypes.map
          (TypeSystem.ParameterSubstitution.apply (signature.parameters.zip ((SourceSemantics.ParameterSubstitution.orderedArguments substitution signature.parameters).map
            SourceCoreRawMetadata.runtimeType)))).map SourceCoreRawMetadata.runtimeType =
        (constructor.payloadTypes.map substitution.apply).map SourceCoreRawMetadata.runtimeType := by
      simp only [List.map_map]
      apply List.map_congr_left
      intro type _
      exact CompatiblePlaceKeyTyping.canonical_substitution_view exact type
    have same : ((constructor.payloadTypes.map
        (TypeSystem.ParameterSubstitution.apply (signature.parameters.zip ((SourceSemantics.ParameterSubstitution.orderedArguments substitution signature.parameters).map
          SourceCoreRawMetadata.runtimeType))))[index]?).map SourceCoreRawMetadata.runtimeType = some (SourceCoreRawMetadata.runtimeType field) := by
      rw [← List.getElem?_map, lists, List.getElem?_map, found]
      rfl
    cases actualAt : (constructor.payloadTypes.map
        (TypeSystem.ParameterSubstitution.apply (signature.parameters.zip ((SourceSemantics.ParameterSubstitution.orderedArguments substitution signature.parameters).map
          SourceCoreRawMetadata.runtimeType))))[index]? with
    | none => simp [actualAt] at same
    | some actual =>
      simp only [actualAt, Option.map_some, Option.some.injEq] at same
      exact ⟨actual, rfl, same⟩

def branchCode (index : Nat) (branch : Branch) : Expr :=
  LanguageResult.success (SourceCoreDataExpressions.projectPacked index branch.payloadTypes (.second (.var 0)))

/-- Exact expression-member row. Raw field equality is provided separately by
`FieldViews`; the compiler only checks its projected native type. -/
structure Row (checked : SourceCoreCompatibleCatalog.Checked) (site : SourceCoreElaboration.ErrorSite)
    (root : TypeSystem.Ty) (substitution : TypeSystem.ParameterSubstitution)
    (identity : DataTypeId) (index : Nat) (result : Ty)
    (input : ProgramDataConstructorSignature × Nat) (branch : Branch) : Prop where
  authenticated : checked.resolveConstructor
    ⟨input.1.id, substitution, input.1.payloadTypes.map substitution.apply, root⟩ = .ok branch.constructor
  position : branch.constructor = ⟨identity, input.2⟩
  field : ∃ actual, (input.1.payloadTypes.map substitution.apply)[index]? = some actual ∧
    SourceCoreCompatibleDataExpressions.projectType checked site actual = .ok result
  payloads : (input.1.payloadTypes.map substitution.apply).mapM
    (SourceCoreCompatibleDataExpressions.projectType checked site) = .ok branch.payloadTypes

theorem row_member {α β : Type} {relation : α → β → Prop} {inputs : List α} {outputs : List β}
    (rows : ListRel relation inputs outputs) {input : α} (member : input ∈ inputs) :
    ∃ output, relation input output := by
  induction rows with
  | nil => cases member
  | cons head tail ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨_, head⟩
    · exact ih member

theorem rows_certificate {checked : SourceCoreCompatibleCatalog.Checked} {site : SourceCoreElaboration.ErrorSite}
    {root field : TypeSystem.Ty} {signature : ProgramDataSignature} {arguments : List TypeSystem.Ty}
    {identity : DataTypeId} {index : Nat} {result : Ty} {branches : List Branch}
    (identityFound : checked.catalog.identity? root = some identity)
    (projected : SourceCoreCompatibleDataExpressions.projectType checked site field = .ok result)
    (views : FieldViews signature arguments index field)
    (rows : ListRel (Row checked site root (signature.parameters.zip arguments) identity index result)
      signature.constructors.zipIdx branches) :
    CompatibleMemberCertificates.Certificate checked site root field signature arguments index identity branches result := by
  refine ⟨identityFound, projected, ?_⟩
  have convert : ∀ inputs outputs,
      ListRel (Row checked site root (signature.parameters.zip arguments) identity index result) inputs outputs →
      (∀ input ∈ inputs, input.1 ∈ signature.constructors) →
      ListRel (CompatibleMemberCertificates.Row checked site root field (signature.parameters.zip arguments) identity index) inputs outputs := by
    intro inputs outputs related
    induction related with
    | nil => intro _; exact .nil
    | @cons input inputs branch branches row rest ih =>
      intro members
      obtain ⟨actual, found, view⟩ := views input.1 (members input (by simp))
      exact .cons ⟨row.authenticated, row.position, ⟨actual, found, view⟩, row.payloads⟩
        (ih (fun item member => members item (by simp [member])))
  apply convert _ _ rows
  intro input member
  obtain ⟨constructor, position⟩ := input
  exact List.mem_of_getElem? (List.mk_mem_zipIdx_iff_getElem?.mp member)

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionMembers
