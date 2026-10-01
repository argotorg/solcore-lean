import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionConstructorCertificates

/-! Successful proxy lowering authenticates the exact raw inner type and its
registry header. The native nominal identity may share an erased runtime view;
it is not used to reconstruct or replace the original proxy metadata. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionProxies
open Core Frontend SourceInference CompatibleExpressionReads CompatiblePayload
open CompatibleEncoding (bind_ok)
abbrev ValuesContext := SourceCoreCompatibleValues.Context
abbrev Scope := SourceCoreLocalCell.Scope
abbrev Child := SourceCoreFunctions.ExpressionLowerer

private theorem ensureType_ok {site : SourceCoreElaboration.ErrorSite} {expected actual : Core.Ty}
    (checked : SourceCoreBasic.ensureType site expected actual = .ok ()) : expected = actual := by
  by_cases same : expected = actual
  · exact same
  · simp [SourceCoreBasic.ensureType, same] at checked

structure Header (values : ValuesContext) (source : TypedSource) (id : ExpressionId)
    (node : ExpressionNode) (inner : TypeSystem.Ty) (owner : DataTypeId) (header : Word) : Prop where
  metadata : Metadata values.checked source id node (.namedData owner)
  form : node.form = .proxy inner
  sourceType : node.type = .proxy inner
  identity : values.checked.catalog.identity? (.proxy inner) = some owner
  original : MetadataRep values.registry (.proxy inner) header
  registered : values.checked.catalog.definitions.lookupConstructorPayloadType? ⟨owner, 0⟩ = some .word

inductive Certificate (values : ValuesContext) (source : TypedSource) (_scope : Scope) :
    ExpressionId → SourceCoreBasic.LoweredExpr → Prop where
  | proxy {id node inner owner header} (receipt : Header values source id node inner owner header) :
      Certificate values source _scope id
        ⟨.namedData owner, LanguageResult.success (.construct ⟨owner, 0⟩ (.word header))⟩

/-- The actual leaf branch checks raw source type equality, registered payload
layout and the existing metadata ID; it never calls its child callback. -/
theorem proxy_of_lower
    {values : ValuesContext} {child : Child} {fuel : Nat} {source : TypedSource} {scope : Scope}
    {id : ExpressionId} {node : ExpressionNode} {inner : TypeSystem.Ty}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (found : source.lookupExpression? id = some node) (form : node.form = .proxy inner)
    (accepted : SourceCoreCompatibleDataExpressions.lowerWithReasons (fuel + 1) values child source scope id reasonAt = .ok lowered) :
    ∃ owner header, lowered = ⟨.namedData owner, LanguageResult.success (.construct ⟨owner, 0⟩ (.word header))⟩ ∧
      Header values source id node inner owner header := by
  unfold SourceCoreCompatibleDataExpressions.lowerWithReasons at accepted
  obtain ⟨read, readAccepted, accepted⟩ := bind_ok accepted
  rcases read with ⟨actualNode, type⟩
  have metadata := metadata_of_read readAccepted
  have same := Option.some.inj (metadata.found.symm.trans found)
  subst actualNode
  simp only [form] at accepted
  by_cases sourceType : node.type = .proxy inner
  · simp only [sourceType, ↓reduceIte, pure, Except.pure, bind, Except.bind] at accepted
    cases identity : values.checked.catalog.identity? (.proxy inner) with
    | none => simp [identity] at accepted
    | some owner =>
      simp only [identity] at accepted
      obtain ⟨header, metadataId, accepted⟩ := bind_ok accepted
      obtain ⟨success, checked, accepted⟩ := bind_ok accepted
      cases success
      have typeEq := ensureType_ok checked
      subst type
      by_cases registered : values.checked.catalog.definitions.lookupConstructorPayloadType? ⟨owner, 0⟩ = some .word
      · simp only [registered, ↓reduceIte, pure, Except.pure, bind, Except.bind, Except.ok.injEq] at accepted
        subst lowered
        have original : MetadataRep values.registry (.proxy inner) header := by
          change (match values.registry.id? (.proxy inner) with
            | some header => Except.ok header | none => Except.error _) = .ok header at metadataId
          cases selected : values.registry.id? (.proxy inner) with
          | none => simp [selected] at metadataId
          | some actual =>
            simp only [selected, Except.ok.injEq] at metadataId
            subst actual
            exact ⟨SourceCoreRawMetadata.Registry.id?_reconstruct selected⟩
        exact ⟨owner, header, rfl, metadata, form, sourceType, identity, original, registered⟩
      · simp [registered, throw, bind, Except.bind] at accepted
  · simp [sourceType, throw, bind, Except.bind] at accepted

/-- An ordinary Functions leaf receipt contains no child lowering, evaluation
or function-body semantics premise. Overrides are explicitly excluded. -/
theorem certificate_of_functions
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
    {context : SourceCoreFunctions.Context} {values : ValuesContext} {source : TypedSource} {scope : Scope}
    {id : ExpressionId} {node : ExpressionNode} {inner : TypeSystem.Ty}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (found : source.lookupExpression? id = some node) (form : node.form = .proxy inner)
    (special : ∀ child budget, (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower context child budget source scope id reasonAt) = .ok none)
    (readPolicy : policy.readExpression source id = SourceCoreCompatibleDataExpressions.readExpression values.checked source id)
    (leafPolicy : policy.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope id reasonAt = .ok lowered) :
    Certificate values source scope id lowered := by
  cases fuel with
  | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
  | succ fuel =>
    rw [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    by_cases owner : id.occurrence.owner = source.owner
    · simp only [owner, ne_eq, not_true_eq_false, ↓reduceIte, found, bind, Except.bind, pure, Except.pure] at accepted
      have bypass := special (fun budget childSource childScope childId childReasonAt =>
        SourceCoreFunctions.lowerExpressionWithPolicy policy body (min budget fuel) context childSource childScope childId childReasonAt) (fuel + 1)
      cases hook : policy.lowerSpecial? <;> simp only [hook] at accepted bypass
      all_goals try rw [bypass] at accepted
      all_goals
        simp only [form, readPolicy, bind, Except.bind, pure, Except.pure] at accepted
        cases read : SourceCoreCompatibleDataExpressions.readExpression values.checked source id with
        | error error => simp [read] at accepted
        | ok pair =>
          rcases pair with ⟨other, type⟩
          have metadata := metadata_of_read read
          have same := Option.some.inj (metadata.found.symm.trans found)
          subst other
          simp only [read, form, leafPolicy] at accepted
          unfold SourceCoreCompatibleDataExpressions.leafLowerer at accepted
          simp only [read, bind, Except.bind, form] at accepted
          obtain ⟨identity, header, rfl, receipt⟩ := proxy_of_lower found form accepted
          exact .proxy receipt
    · simp [owner, bind, Except.bind] at accepted

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionProxies
