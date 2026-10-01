import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionConstructorSource
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionContextualConditionals

/-! Receipts for the real constructor compiler preserve its raw metadata ID,
registered native layout, and ordered child compilation results. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionConstructors
open Core Frontend SourceInference CompatibleExpressionPrimitives CompatiblePayload DataPatternValues
abbrev ValuesContext := SourceCoreCompatibleValues.Context
abbrev Scope := SourceCoreLocalCell.Scope
abbrev Child := SourceCoreFunctions.ExpressionLowerer
open CompatibleEncoding (bind_ok mapError_ok)

private theorem ensureType_ok {site : SourceCoreElaboration.ErrorSite} {expected actual : Core.Ty}
    (checked : SourceCoreBasic.ensureType site expected actual = .ok ()) : expected = actual := by
  by_cases same : expected = actual
  · exact same
  · simp [SourceCoreBasic.ensureType, same] at checked

/-- The existing callback sequence, named only to state its static receipt. -/
def argument (values : ValuesContext) (child : Child) (fuel : Nat) (source : TypedSource)
    (scope : Scope) (site : SourceCoreElaboration.ErrorSite) (reasonAt : ExpressionId → Word)
    (input : ExpressionId × TypeSystem.Ty) : Except SourceCoreBasic.Error SourceCoreBasic.LoweredExpr := do
  let expected ← SourceCoreCompatibleDataExpressions.projectType values.checked site input.2
  let lowered ← child fuel source scope input.1 reasonAt
  SourceCoreBasic.ensureType site expected lowered.type
  pure lowered

structure Argument (values : ValuesContext) (child : Child) (fuel : Nat) (source : TypedSource)
    (scope : Scope) (reasonAt : ExpressionId → Word)
    (input : ExpressionId × TypeSystem.Ty) (code : SourceCoreBasic.LoweredExpr) : Prop where
  projected : values.checked.catalog.project input.2 = .ok code.type
  generated : child fuel source scope input.1 reasonAt = .ok code

theorem argument_of_accepted {values : ValuesContext} {child : Child} {fuel : Nat} {source : TypedSource}
    {scope : Scope} {site : SourceCoreElaboration.ErrorSite} {reasonAt : ExpressionId → Word}
    {input : ExpressionId × TypeSystem.Ty} {code : SourceCoreBasic.LoweredExpr}
    (accepted : argument values child fuel source scope site reasonAt input = .ok code) :
    Argument values child fuel source scope reasonAt input code := by
  unfold argument at accepted
  obtain ⟨expected, projected, accepted⟩ := bind_ok accepted
  obtain ⟨actual, generated, accepted⟩ := bind_ok accepted
  obtain ⟨success, checked, accepted⟩ := bind_ok accepted
  cases success
  cases accepted
  have typeEq := ensureType_ok checked
  exact ⟨typeEq ▸ CompatibleExpressionReads.projectType_of_accepted projected, generated⟩

theorem arguments_of_mapM {values : ValuesContext} {child : Child} {fuel : Nat} {source : TypedSource}
    {scope : Scope} {site : SourceCoreElaboration.ErrorSite} {reasonAt : ExpressionId → Word}
    {inputs : List (ExpressionId × TypeSystem.Ty)} {codes : List SourceCoreBasic.LoweredExpr}
    (accepted : inputs.mapM (argument values child fuel source scope site reasonAt) = .ok codes) :
    ListRel (Argument values child fuel source scope reasonAt) inputs codes := by
  induction inputs generalizing codes with
  | nil => simp at accepted; subst codes; exact .nil
  | cons input tail ih =>
    rw [List.mapM_cons] at accepted
    obtain ⟨head, generated, accepted⟩ := bind_ok accepted
    obtain ⟨rest, compiled, accepted⟩ := bind_ok accepted
    cases accepted
    exact .cons (argument_of_accepted generated) (ih compiled)

theorem arguments_projected {values : ValuesContext} {child : Child} {fuel : Nat} {source : TypedSource}
    {scope : Scope} {reasonAt : ExpressionId → Word} {ids : List ExpressionId} {types : List TypeSystem.Ty}
    {codes : List SourceCoreBasic.LoweredExpr} (count : ids.length = types.length)
    (arguments : ListRel (Argument values child fuel source scope reasonAt) (ids.zip types) codes) :
    types.mapM values.checked.catalog.project = .ok (codes.map (·.type)) := by
  induction ids generalizing types codes with
  | nil => cases types with
    | nil => cases arguments; rfl
    | cons => cases count
  | cons id ids ih => cases types with
    | nil => cases count
    | cons type types =>
      cases arguments with
      | cons head tail =>
        have rest := ih (Nat.succ.inj count) tail
        simp only [List.mapM_cons, head.projected, rest, bind, Except.bind, pure, Except.pure, List.map_cons]

structure Header (values : ValuesContext) (source : TypedSource) (id : ExpressionId)
    (node : ExpressionNode) (instantiation : DataConstructorInstantiation) (tag : ConstructorId)
    (header : Word) (codes : List SourceCoreBasic.LoweredExpr) : Prop where
  metadata : Metadata values.checked source id node (.namedData tag.owner)
  sourceType : node.type = instantiation.resultType
  selected : values.checked.catalog.constructor? instantiation = some tag
  original : MetadataRep values.registry (.constructor instantiation) header
  registered : values.checked.catalog.definitions.lookupConstructorPayloadType? tag =
    some (.product .word (SourceCoreCompatibleCatalog.packTypes (codes.map (·.type))))

/-- No type/evaluation property of the callback is assumed here. Successful
calls are exposed as equations to be consumed by the structural induction. -/
theorem constructor_of_lower
    {values : ValuesContext} {child : Child} {fuel : Nat} {source : TypedSource} {scope : Scope}
    {id : ExpressionId} {node : ExpressionNode} {instantiation : DataConstructorInstantiation}
    {ids : List ExpressionId} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (found : source.lookupExpression? id = some node) (form : node.form = .constructor instantiation ids)
    (accepted : SourceCoreCompatibleDataExpressions.lowerWithReasons (fuel + 1) values child source scope id reasonAt = .ok lowered) :
    ∃ tag header codes, lowered = ⟨.namedData tag.owner,
        SourceCoreCompatibleDataExpressions.construct tag header (SourceCoreCalls.packArguments codes).expression⟩ ∧
      Header values source id node instantiation tag header codes ∧ ids.length = instantiation.payloadTypes.length ∧
      ListRel (Argument values child fuel source scope reasonAt) (ids.zip instantiation.payloadTypes) codes := by
  unfold SourceCoreCompatibleDataExpressions.lowerWithReasons at accepted
  obtain ⟨read, readAccepted, accepted⟩ := bind_ok accepted
  rcases read with ⟨actualNode, type⟩
  have metadata := CompatibleExpressionReads.metadata_of_read readAccepted
  have same := Option.some.inj (metadata.found.symm.trans found)
  subst actualNode
  simp only [form] at accepted
  by_cases sourceType : node.type = instantiation.resultType
  · simp only [sourceType, ↓reduceIte, pure, Except.pure, bind, Except.bind] at accepted
    by_cases count : ids.length = instantiation.payloadTypes.length
    · simp only [count, ↓reduceIte, pure, Except.pure, bind, Except.bind] at accepted
      obtain ⟨tag, resolved, accepted⟩ := bind_ok accepted
      have resolved := mapError_ok resolved
      obtain ⟨header, metadataId, accepted⟩ := bind_ok accepted
      obtain ⟨success, checked, accepted⟩ := bind_ok accepted
      cases success
      have typeEq := ensureType_ok checked
      subst type
      obtain ⟨codes, generated, accepted⟩ := bind_ok accepted
      cases accepted
      have arguments : ListRel (Argument values child fuel source scope reasonAt) (ids.zip instantiation.payloadTypes) codes :=
        arguments_of_mapM generated
      obtain ⟨selected, types, projected, registered⟩ := CompatibleEncoding.resolveConstructor_facts resolved
      have actualProjected := arguments_projected count arguments
      have typeListEq := Except.ok.inj (projected.symm.trans actualProjected)
      subst types
      have original : MetadataRep values.registry (.constructor instantiation) header := by
        change (match values.registry.id? (.constructor instantiation) with
          | some header => Except.ok header | none => Except.error _) = .ok header at metadataId
        cases selectedId : values.registry.id? (.constructor instantiation) with
        | none => simp [selectedId] at metadataId
        | some actual =>
          simp only [selectedId, Except.ok.injEq] at metadataId
          subst actual
          exact ⟨SourceCoreRawMetadata.Registry.id?_reconstruct selectedId⟩
      exact ⟨tag, header, codes, rfl, ⟨metadata, sourceType, selected, original, registered⟩, count, arguments⟩
    · simp [count, throw, bind, Except.bind] at accepted
  · simp [sourceType, throw, bind, Except.bind] at accepted

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionConstructors
