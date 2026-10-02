import Solcore.SourceSemantics.CoreLowering.CompatibleCatalogNominalCoverage
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionConstructorNativeTyping
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionContextualMembers

/-! Factory nominal coverage and authenticated emitted rows type the complete
member match. Raw field views determine projection; no native branch typing or
child typing callback is assumed for the recursive member grammar. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionMemberNativeTyping
open Core Frontend SourceInference CompatibleExpressionReads
open CompatibleExpressionMembers CompatibleExpressionScalarNativeTyping
open CompatibleCatalogNominalCoverage
open DataPatternValues
open CompatibleEncoding (bind_ok)

theorem projectPacked_native {definitions : DataEnvironment} {context : Core.Context}
    {types : List Ty} {index : Nat} {type : Ty} {bundle : Expr}
    (found : types[index]? = some type)
    (typed : HasType context bundle (SourceCoreCompatibleCatalog.packTypes types) definitions) :
    HasType context (SourceCoreDataExpressions.projectPacked index types bundle) type definitions := by
  induction types generalizing index bundle with
  | nil => cases found
  | cons head rest ih =>
    cases rest with
    | nil =>
      cases index with
      | zero => cases found; exact typed
      | succ index => simp at found
    | cons next tail =>
      cases index with
      | zero => cases found; exact .first typed
      | succ index =>
        simpa [SourceCoreDataExpressions.projectPacked] using ih (by simpa using found) (HasType.second typed)

private theorem mapM_at {α β ε : Type} {inputs : List α} {outputs : List β}
    {action : α → Except ε β} (accepted : inputs.mapM action = .ok outputs)
    {index : Nat} {input : α} (found : inputs[index]? = some input) :
    ∃ output, outputs[index]? = some output ∧ action input = .ok output := by
  induction inputs generalizing outputs index with
  | nil => cases found
  | cons head rest ih =>
    rw [List.mapM_cons] at accepted
    obtain ⟨first, produced, accepted⟩ := bind_ok accepted
    obtain ⟨tail, remaining, accepted⟩ := bind_ok accepted
    cases accepted
    cases index with
    | zero => cases found; exact ⟨first, rfl, produced⟩
    | succ index => exact ih remaining found

private theorem projected_list {checked : SourceCoreCompatibleCatalog.Checked}
    {site : SourceCoreElaboration.ErrorSite} {inputs : List TypeSystem.Ty} {outputs : List Ty}
    (accepted : inputs.mapM (SourceCoreCompatibleDataExpressions.projectType checked site) = .ok outputs) :
    inputs.mapM checked.catalog.project = .ok outputs := by
  induction inputs generalizing outputs with
  | nil => simpa using accepted
  | cons head rest ih =>
    rw [List.mapM_cons] at accepted ⊢
    obtain ⟨first, produced, accepted⟩ := bind_ok accepted
    obtain ⟨tail, remaining, accepted⟩ := bind_ok accepted
    cases accepted
    simp [projectType_of_accepted produced, ih remaining, bind, Except.bind, pure, Except.pure]

private theorem relation_at {α β : Type} {relation : α → β → Prop} {inputs : List α} {outputs : List β}
    (related : ListRel relation inputs outputs) {index : Nat} {output : β}
    (found : outputs[index]? = some output) : ∃ input, inputs[index]? = some input ∧ relation input output := by
  induction related generalizing index with
  | nil => cases found
  | cons head tail ih =>
    cases index with
    | zero => cases found; exact ⟨_, rfl, head⟩
    | succ index => exact ih found

private theorem relation_length {α β : Type} {relation : α → β → Prop} {inputs : List α} {outputs : List β}
    (related : ListRel relation inputs outputs) : outputs.length = inputs.length := by
  induction related with
  | nil => rfl
  | cons head tail ih => simpa using ih

private theorem branches_native {definitions : DataEnvironment} {context : Core.Context}
    {payloads : List Ty} {branches : List Expr} {result : Ty}
    (count : branches.length = payloads.length)
    (typed : ∀ (index : Nat) payload branch, payloads[index]? = some payload → branches[index]? = some branch →
      HasType (payload :: context) branch result definitions) :
    BranchesHaveType context result payloads branches definitions := by
  induction payloads generalizing branches with
  | nil =>
    cases branches with
    | nil => exact .nil
    | cons => simp at count
  | cons payload rest ih =>
    cases branches with
    | nil => simp at count
    | cons branch tail =>
      exact .cons (typed 0 payload branch rfl rfl)
        (ih (by simpa using count) (fun index payload branch found generated => typed (index + 1) payload branch found generated))

theorem nominal_project {catalog : SourceCoreCompatibleCatalog.Catalog} {type : TypeSystem.Ty}
    {declaration : Resolved.DeclarationId} {arguments : List TypeSystem.Ty} {identity : DataTypeId}
    (nominal : SourceCoreDataCatalog.nominalParts type = some (declaration, arguments))
    (found : catalog.identity? type = some identity) : catalog.project type = .ok (.namedData identity) := by
  cases type <;> try simp [SourceCoreDataCatalog.nominalParts] at nominal
  · rename_i constructor
    cases constructor <;> simp_all [SourceCoreDataCatalog.nominalParts, SourceCoreCompatibleCatalog.Catalog.project]
  · simp [SourceCoreCompatibleCatalog.Catalog.project, found]

private theorem row_native {checked : SourceCoreCompatibleCatalog.Checked} {site : SourceCoreElaboration.ErrorSite}
    {root field : TypeSystem.Ty} {substitution : TypeSystem.ParameterSubstitution}
    {identity : DataTypeId} {index : Nat} {input : ProgramDataConstructorSignature × Nat} {branch : Branch} {result : Ty}
    (row : CompatibleMemberCertificates.Row checked site root field substitution identity index input branch)
    (fieldProjected : SourceCoreCompatibleDataExpressions.projectType checked site field = .ok result) :
    checked.catalog.definitions.lookupConstructorPayloadType? branch.constructor =
        some (.product .word (SourceCoreCompatibleCatalog.packTypes branch.payloadTypes)) ∧
      branch.payloadTypes[index]? = some result := by
  obtain ⟨_, actualTypes, projected, registered⟩ := CompatibleEncoding.resolveConstructor_facts row.authenticated
  have payloads := projected_list row.payloads
  have same := Except.ok.inj (projected.symm.trans payloads)
  subst actualTypes
  obtain ⟨actual, found, view⟩ := row.fieldLookup
  obtain ⟨native, nativeAt, actualProjected⟩ := mapM_at payloads found
  have compatible := CompatibleEncoding.project_compatible (catalog := checked.catalog) view
  have resultProjected := projectType_of_accepted fieldProjected
  rw [compatible, resultProjected] at actualProjected
  cases actualProjected
  exact ⟨registered, nativeAt⟩

theorem layout_native {checked : SourceCoreCompatibleCatalog.Checked} {site : SourceCoreElaboration.ErrorSite}
    {base field : TypeSystem.Ty} {index : Nat} {identity : DataTypeId} {branches : List Expr} {result : Ty}
    (layout : Layout checked site base field index identity branches result)
    (shaped : Shapes checked.signatures checked.catalog) (complete : Complete checked.catalog)
    {context : Core.Context} {child : Expr}
    (childTyped : HasType context child (LanguageResult.resultType (.namedData identity)) checked.catalog.definitions) :
    HasType context (SourceCoreDataExpressions.member identity result branches child)
      (LanguageResult.resultType result) checked.catalog.definitions := by
  cases layout with
  | @intro signature arguments infos nominal selected certificate generated =>
    obtain ⟨entry, entryAt, _⟩ := identity_entry certificate.identityLookup
    cases stored : entry.definition with
    | none =>
      have present := complete entry (List.mem_of_getElem? entryAt)
      simp [stored] at present
    | some definition =>
      have registered : checked.catalog.definitions.lookupDataType? identity = some definition := by
        simp [DataEnvironment.lookupDataType?, SourceCoreCompatibleCatalog.Catalog.definitions, List.getElem?_map, entryAt, stored]
      obtain ⟨_, _, _, count⟩ := shaped.nominal_coverage complete
        (by simpa [SourceCoreRawMetadata.runtimeType_idempotent] using nominal) selected certificate.identityLookup registered
      apply SourceCoreDataExpressions.member_hasType registered
        (projectType_wellFormed certificate.projectedField) childTyped
      apply branches_native
      · rw [generated, List.length_map, relation_length certificate.rows, List.length_zipIdx, count]
      · intro position payload code payloadAt codeAt
        rw [generated, List.getElem?_map] at codeAt
        cases branchAt : infos[position]? with
        | none => simp [branchAt] at codeAt
        | some branch =>
          simp only [branchAt, Option.map_some, Option.some.injEq] at codeAt
          subst code
          obtain ⟨input, inputAt, row⟩ := relation_at certificate.rows branchAt
          have positionEq : input.2 = position := by
            rw [List.getElem?_zipIdx] at inputAt
            cases constructorAt : signature.constructors[position]? with
            | none => simp [constructorAt] at inputAt
            | some constructor => simp only [constructorAt, Option.map_some, Option.some.injEq] at inputAt; cases inputAt; simp
          obtain ⟨payloadLookup, fieldAt⟩ := row_native row certificate.projectedField
          simp only [row.position, positionEq, DataEnvironment.lookupConstructorPayloadType?, registered,
            bind, Option.bind, payloadAt] at payloadLookup
          have payloadEq := Option.some.inj payloadLookup
          subst payload
          exact LanguageResult.success_hasType (projectPacked_native fieldAt (HasType.second (HasType.var rfl)))

theorem child_type {checked : SourceCoreCompatibleCatalog.Checked} {site : SourceCoreElaboration.ErrorSite}
    {base field : TypeSystem.Ty} {index : Nat} {identity : DataTypeId} {branches : List Expr} {result native : Ty}
    (layout : Layout checked site base field index identity branches result)
    (projected : checked.catalog.project base = .ok native) : native = .namedData identity := by
  cases layout with
  | intro nominal selected certificate generated =>
    have named := nominal_project nominal certificate.identityLookup
    rw [SourceCoreCompatibleCatalog.Catalog.project_runtimeType] at named
    exact Except.ok.inj (projected.symm.trans named)

theorem result_wellFormed {checked : SourceCoreCompatibleCatalog.Checked} {site : SourceCoreElaboration.ErrorSite}
    {base field : TypeSystem.Ty} {index : Nat} {identity : DataTypeId} {branches : List Expr} {result : Ty}
    (layout : Layout checked site base field index identity branches result) :
    result.WellFormed checked.catalog.definitions := by
  cases layout with
  | intro nominal selected certificate generated => exact projectType_wellFormed certificate.projectedField

variable {readFuel : Nat} {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  (shaped : Shapes values.checked.signatures values.checked.catalog) (complete : Complete values.checked.catalog)
  (visibleTypes : ScopeWellFormed values.checked.catalog.definitions scope) (administrative : Core.Context)

include shaped complete visibleTypes in
theorem members_native
    (tree : CompatibleExpressionMembers.Tree readFuel values source context solved reasonAt scope id lowered) :
    NativeTyping values.checked.catalog.definitions (SourceCoreLocalCell.coreContext scope ++ administrative) lowered := by
  induction tree with
  | fragment child => exact CompatibleExpressionConstructorNativeTyping.constructors_native visibleTypes administrative child
  | member metadata baseMetadata form layout childTree ih =>
    have childType := child_type layout baseMetadata.projected
    exact ⟨result_wellFormed layout, layout_native layout shaped complete (by rw [← childType]; exact ih.2)⟩

include shaped complete visibleTypes in
theorem members_native_at {definitions : DataEnvironment}
    (extension : values.checked.catalog.definitions.Extends definitions)
    (tree : CompatibleExpressionMembers.Tree readFuel values source context solved reasonAt scope id lowered) :
    NativeTyping definitions (SourceCoreLocalCell.coreContext scope ++ administrative) lowered := by
  obtain ⟨wellFormed, native⟩ := members_native shaped complete visibleTypes administrative tree
  exact ⟨wellFormed.extend_definitions extension, native.extend_definitions extension⟩

include visibleTypes in
theorem contextual_native
    {catalogSignatures : ProgramSignatures} {catalogFuel : Nat} {catalogTypes : List TypeSystem.Ty}
    {metadata : List SourceCoreCompatibleCatalog.Metadata} {limits : SourceCoreCompatibleCatalog.Limits} {contracts : Bool}
    (registered : SourceCoreCompatibleCatalog.prepare catalogSignatures catalogFuel catalogTypes metadata limits contracts = .ok values.checked)
    {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {signatures : ProgramSignatures} {locals : SourceCoreLocalPolymorphism.Catalog}
    {parents : List SourceCoreLocalEvidence.Prepared} {assignments : SourceCoreAssignmentFaultSites.Table}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {compilation : SourceCoreFunctions.Context}
    {native : Option SourceCoreGeneralFunctions.CallableContext} {parent : Option SourceCoreLocalEvidence.Prepared}
    {skipInitializer : Option ExpressionId} {compileFuel : Nat} {node : ExpressionNode}
    {definitions : DataEnvironment}
    (ordinary : CompatibleExpressionMembers.Ordinary source locals compilation.owner)
    (unique : NodeOccurrencesUnique source)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (syntaxTree : CompatibleExpressionMembers.Syntax source id)
    (found : source.lookupExpression? id = some node)
    (sourceTyped : ExpressionHasType source context id node.type)
    (readPolicy : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerPolicy : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression program representation signatures locals parents assignments
      diagnostics compilation native parent skipInitializer compileFuel source scope id reasonAt = .ok lowered)
    (extension : values.checked.catalog.definitions.Extends definitions) :
    NativeTyping definitions (SourceCoreLocalCell.coreContext scope ++ administrative) lowered := by
  have shaped := prepare_shapes registered
  rw [← SourceCoreCompatibleCatalog.prepare_signatures registered] at shaped
  exact members_native_at shaped (prepare_complete registered) visibleTypes administrative extension
    (CompatibleExpressionMembers.tree_of_contextual ordinary unique closed residual declarations sourceSignatures syntaxTree found sourceTyped
      readPolicy lowerPolicy leafPolicy accepted)

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionMemberNativeTyping
