import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionMemberMeaning

/-! Successful expression-member generation yields every native branch and
its catalog receipt. Independent source projection supplies raw field views;
no native representation equality is treated as source-type equality. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionMembers
open Core Frontend SourceInference DataPatternValues CompatibleExpressionReads
open CompatibleEncoding (bind_ok mapError_ok)

private theorem ensureType_ok {site : SourceCoreElaboration.ErrorSite} {expected actual : Core.Ty}
    (checked : SourceCoreBasic.ensureType site expected actual = .ok ()) : expected = actual := by
  by_cases same : expected = actual
  · exact same
  · simp [SourceCoreBasic.ensureType, same] at checked

private theorem read_projected {checked : SourceCoreCompatibleCatalog.Checked} {source : TypedSource} {id : ExpressionId}
    {node : ExpressionNode} {type : Ty}
    (accepted : SourceCoreCompatibleDataExpressions.readExpression checked source id = .ok (node, type)) :
    SourceCoreCompatibleDataExpressions.projectType checked (.occurrence id.occurrence) node.type = .ok type := by
  have metadata := metadata_of_read accepted
  simp only [SourceCoreCompatibleDataExpressions.readExpression, metadata.owner, ne_eq, not_true_eq_false,
    ↓reduceIte, metadata.found, metadata.requirements, metadata.coercions, List.isEmpty_nil, Bool.true_eq_false,
    bind, Except.bind, pure, Except.pure] at accepted
  cases projected : SourceCoreCompatibleDataExpressions.projectType checked (.occurrence id.occurrence) node.type with
  | error error => simp [projected] at accepted
  | ok native => simp only [projected, Except.ok.injEq, Prod.mk.injEq, true_and] at accepted; subst type; rfl

private theorem row_of_accepted {values : ValuesContext} {node : ExpressionNode} {root : TypeSystem.Ty}
    {substitution : TypeSystem.ParameterSubstitution} {identity : DataTypeId} {index : Nat} {result : Ty}
    {input : ProgramDataConstructorSignature × Nat} {code : Expr}
    (accepted : (do
      let payloadTypes := input.1.payloadTypes.map substitution.apply
      let instantiation : DataConstructorInstantiation := ⟨input.1.id, substitution, payloadTypes, root⟩
      let resolved ← (values.checked.resolveConstructor instantiation).mapError (fun _ => SourceCoreBasic.Error.unsupportedExpression node.id node.form)
      unless resolved.owner = identity && resolved.index = input.2 do throw (SourceCoreBasic.Error.unsupportedExpression node.id node.form)
      let selected ← match payloadTypes[index]? with
        | some selected => SourceCoreCompatibleDataExpressions.projectType values.checked (.occurrence node.id.occurrence) selected
        | none => throw (SourceCoreBasic.Error.unsupportedExpression node.id node.form)
      SourceCoreBasic.ensureType (.occurrence node.id.occurrence) result selected
      let payloads ← payloadTypes.mapM (SourceCoreCompatibleDataExpressions.projectType values.checked (.occurrence node.id.occurrence))
      pure (LanguageResult.success (SourceCoreDataExpressions.projectPacked index payloads (.second (.var 0))))) = Except.ok code) :
    ∃ info, code = branchCode index info ∧ Row values.checked (.occurrence node.id.occurrence) root substitution identity index result input info := by
  obtain ⟨tag, resolved, accepted⟩ := bind_ok accepted
  have resolved := mapError_ok resolved
  by_cases valid : tag.owner = identity ∧ tag.index = input.2
  · simp only [valid.1, valid.2, decide_true, Bool.and_self, ↓reduceIte, bind, Except.bind, pure, Except.pure] at accepted
    cases fieldAt : (input.1.payloadTypes.map substitution.apply)[index]? with
    | none => simp [fieldAt, throw] at accepted
    | some field =>
      simp only [fieldAt] at accepted
      obtain ⟨native, projected, accepted⟩ := bind_ok accepted
      obtain ⟨success, ensured, accepted⟩ := bind_ok accepted
      cases success
      have same := ensureType_ok ensured
      have projectedResult : SourceCoreCompatibleDataExpressions.projectType values.checked (.occurrence node.id.occurrence) field = .ok result := by
        rw [same]; exact projected
      cases payloads : (input.1.payloadTypes.map substitution.apply).mapM
          (SourceCoreCompatibleDataExpressions.projectType values.checked (.occurrence node.id.occurrence)) with
      | error error => simp only [payloads] at accepted; cases accepted
      | ok types =>
        simp only [payloads, pure, Except.pure, bind, Except.bind] at accepted
        cases accepted
        exact ⟨⟨tag, types⟩, rfl, resolved, by cases tag; simp_all, ⟨field, fieldAt, projectedResult⟩, payloads⟩
  · simp [valid, Bool.and_eq_true, throw, bind, Except.bind] at accepted

private theorem rows_of_mapM {values : ValuesContext} {node : ExpressionNode} {root : TypeSystem.Ty}
    {substitution : TypeSystem.ParameterSubstitution} {identity : DataTypeId} {index : Nat} {result : Ty}
    {inputs : List (ProgramDataConstructorSignature × Nat)} {codes : List Expr}
    {action : ProgramDataConstructorSignature × Nat → Except SourceCoreBasic.Error Expr}
    (accepted : inputs.mapM action = .ok codes)
    (row : ∀ input code, action input = .ok code → ∃ info, code = branchCode index info ∧
      Row values.checked (.occurrence node.id.occurrence) root substitution identity index result input info) :
    ∃ infos, codes = infos.map (branchCode index) ∧
      ListRel (Row values.checked (.occurrence node.id.occurrence) root substitution identity index result) inputs infos := by
  induction inputs generalizing codes with
  | nil => simp at accepted; subst codes; exact ⟨[], rfl, .nil⟩
  | cons input tail ih =>
    rw [List.mapM_cons] at accepted
    obtain ⟨first, produced, accepted⟩ := bind_ok accepted
    obtain ⟨rest, remaining, accepted⟩ := bind_ok accepted
    cases accepted
    obtain ⟨info, rfl, firstRow⟩ := row input first produced
    obtain ⟨infos, rfl, restRows⟩ := ih remaining
    exact ⟨info :: infos, rfl, .cons firstRow restRows⟩

theorem layout_of_accepted {values : ValuesContext} {node : ExpressionNode} {base : TypeSystem.Ty}
    {context : SourceSemantics.Context} {index : Nat} {result : Ty} {identity : DataTypeId} {branches : List Expr}
    (signatures : context.signatures = values.checked.signatures)
    (projection : UniformMemberProjection context base index node.type)
    (projected : SourceCoreCompatibleDataExpressions.projectType values.checked (.occurrence node.id.occurrence) node.type = .ok result)
    (accepted : SourceCoreCompatibleDataExpressions.memberBranches values node base result index = .ok (identity, branches)) :
    Layout values.checked (.occurrence node.id.occurrence) base node.type index identity branches result := by
  unfold SourceCoreCompatibleDataExpressions.memberBranches at accepted
  cases nominal : SourceCoreDataCatalog.nominalParts (SourceCoreRawMetadata.runtimeType base) with
  | none => simp [nominal, throw, bind, Except.bind] at accepted
  | some pair =>
    rcases pair with ⟨declaration, arguments⟩
    simp only [nominal, pure, Except.pure, bind, Except.bind] at accepted
    cases selected : values.checked.signatures.dataTypes.filter (fun data => decide (data.id = declaration)) with
    | nil => simp [selected, throw] at accepted
    | cons signature rest => cases rest with
      | cons => simp [selected, throw] at accepted
      | nil =>
        simp only [selected, bind, Except.bind] at accepted
        have member : signature ∈ values.checked.signatures.dataTypes.filter (fun data => decide (data.id = declaration)) := by rw [selected]; simp
        have signatureId : signature.id = declaration := by simpa using (List.mem_filter.mp member).2
        subst declaration
        by_cases valid : signature.parameters.length = arguments.length ∧ signature.constructors ≠ []
        · simp only [valid.1, decide_true, List.isEmpty_eq_false_iff.mpr valid.2, Bool.not_false, Bool.and_self, ↓reduceIte,
            pure, Except.pure, bind, Except.bind] at accepted
          cases identityFound : values.checked.catalog.identity? (SourceCoreRawMetadata.runtimeType base) with
          | none => simp [identityFound, throw] at accepted
          | some native =>
            simp only [identityFound, pure, Except.pure, bind, Except.bind] at accepted
            obtain ⟨codes, produced, accepted⟩ := bind_ok accepted
            cases accepted
            obtain ⟨infos, generated, rows⟩ := rows_of_mapM produced (fun _ _ generated => row_of_accepted generated)
            exact .intro nominal selected
              (rows_certificate identityFound projected (field_views signatures nominal selected projection) rows) generated
        · simp [valid, Bool.and_eq_true, throw] at accepted

/-- Actual child compilation equations, rather than semantic premises. -/
theorem member_of_lower
    {values : ValuesContext} {child : Child} {fuel : Nat} {source : TypedSource} {scope : Scope}
    {id base : ExpressionId} {node baseNode : ExpressionNode} {name : String} {index : Nat}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr} {context : SourceSemantics.Context}
    (signatures : context.signatures = values.checked.signatures)
    (found : source.lookupExpression? id = some node) (baseFound : source.lookupExpression? base = some baseNode)
    (form : node.form = .member base name index)
    (projection : UniformMemberProjection context baseNode.type index node.type)
    (accepted : SourceCoreCompatibleDataExpressions.lowerWithReasons (fuel + 1) values child source scope id reasonAt = .ok lowered) :
    ∃ identity branches result code,
      lowered = ⟨result, SourceCoreDataExpressions.member identity result branches code.expression⟩ ∧
      Metadata values.checked source id node result ∧ Metadata values.checked source base baseNode code.type ∧
      Layout values.checked (.occurrence id.occurrence) baseNode.type node.type index identity branches result ∧
      child fuel source scope base reasonAt = .ok code := by
  unfold SourceCoreCompatibleDataExpressions.lowerWithReasons at accepted
  obtain ⟨read, readAccepted, accepted⟩ := bind_ok accepted
  rcases read with ⟨actualNode, type⟩
  have metadata := metadata_of_read readAccepted
  have same := Option.some.inj (metadata.found.symm.trans found)
  subst actualNode
  simp only [form] at accepted
  obtain ⟨baseRead, baseAccepted, accepted⟩ := bind_ok accepted
  rcases baseRead with ⟨actualBase, baseType⟩
  have baseMetadata := metadata_of_read baseAccepted
  have same := Option.some.inj (baseMetadata.found.symm.trans baseFound)
  subst actualBase
  obtain ⟨layout, generated, accepted⟩ := bind_ok accepted
  rcases layout with ⟨identity, branches⟩
  obtain ⟨success, baseEnsured, accepted⟩ := bind_ok accepted
  cases success
  obtain ⟨code, compiled, accepted⟩ := bind_ok accepted
  obtain ⟨success, childEnsured, accepted⟩ := bind_ok accepted
  cases success
  cases accepted
  have same : baseType = code.type := ensureType_ok childEnsured
  subst baseType
  have layout := layout_of_accepted signatures projection (by
    simpa only [(lookupExpression?_sound found).2] using read_projected readAccepted) generated
  exact ⟨identity, branches, type, code, rfl, metadata, baseMetadata,
    (lookupExpression?_sound found).2 ▸ layout, compiled⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionMembers
