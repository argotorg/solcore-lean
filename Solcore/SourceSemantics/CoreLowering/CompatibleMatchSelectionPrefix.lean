import Solcore.SourceSemantics.CoreLowering.CompatibleMatchBranchesPrefix
import Solcore.SourceSemantics.CoreLowering.CompatibleMatchHiddenPrefix

/-! The actual compatible match compiler reaches exactly its independently
selected source body. Hidden and successful arm allocations, raw scrutinee
heap type, source binder order and both continuation directions are composed.
The enclosing statement tree owns scrutinee and selected body semantics. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMatchSelectionPrefix
open Core Frontend SourceInference GeneralHeap CoreProof ReadOnly CompatiblePayload
open SourceCoreCompatibleDataMatches CompatibleMatchCertificates CompatibleMatchDecision
open DataMatchBranchPrefix CallableIndexedHistory

/-- Static binder IDs follow the same ordered flat instruction stream. -/
theorem tree_binding_ids {compilation : CompatiblePatternCertificates.Compilation}
    {source : TypedSource} {site : StatementId} {span : Syntax.SourceSpan} {scope : Scope}
    {expected : TypeSystem.Ty} {instructions rest : List MatchPatternInstruction} {pattern : Pattern}
    (tree : CompatiblePatternCertificates.Tree compilation source site span scope expected instructions pattern rest) :
    pattern.bindings.map (fun binding => binding.1.id) ++ MatchPatternInstruction.binderIds rest =
      MatchPatternInstruction.binderIds instructions := by
  induction tree using CompatiblePatternCertificates.Tree.rec
    (motive_2 := fun _ instructions patterns rest _ =>
      (patterns.flatMap (·.bindings)).map (fun binding => binding.1.id) ++ MatchPatternInstruction.binderIds rest =
        MatchPatternInstruction.binderIds instructions) with
  | wildcard => rfl
  | binder => rfl
  | literal => rfl
  | tuple projection unpacked children projectedChildren ih => exact ih
  | constructor projection result count resolved coreType raw children projectedChildren registered ih => exact ih
  | nil => rfl
  | cons head tail headIH tailIH =>
    simp only [List.flatMap_cons, List.map_append]
    rw [List.append_assoc, tailIH, headIH]

theorem certificate_binding_ids {compilation : CompatiblePatternCertificates.Compilation}
    {source : TypedSource} {site : StatementId} {span : Syntax.SourceSpan} {scope : Scope}
    {expected : TypeSystem.Ty} {pattern : TypedMatchPattern} {compiled : Pattern}
    (certificate : CompatiblePatternCertificates.Certificate compilation source scope site span expected pattern compiled) :
    compiled.bindings.map (fun binding => binding.1.id) = pattern.binderIds := by
  obtain ⟨instructions, root, tree⟩ := certificate.tree
  obtain ⟨arity, same, _⟩ := CompatiblePatternCertificates.rootInstructions_sound compilation
    (.ofSignatures compilation.signatures) rfl _ _ _ root
  have ids := tree_binding_ids tree
  rw [same] at ids
  cases resolutionEq : pattern.resolution <;>
    simpa [resolutionEq, MatchPatternInstruction.binderIds,
      matchPatternResolutionInstructions, TypedMatchPattern.binderIds] using ids

/-- A static allocation classification for this exact compiled tree. These
sites are ordinary lexical allocations, rather than named input allocations. -/
def Ordinary {compilation : SourceCoreCompatibleDataMatches.Context} {source : TypedSource} {scope : Scope}
    {id : StatementId} {resolution : MatchResolution} {resultType : Ty} {internalReason : Word}
    {expressionCertificate : ExpressionCertificate} {bodyCertificate : BodyCertificate} {code : Expr}
    (_certificate : Certificate compilation source scope id resolution resultType internalReason
      expressionCertificate bodyCertificate code) : Prop :=
  source.inputs.any (fun input => decide (input.id = resolution.hiddenScrutinee)) = false ∧
  ∀ payload expected arms, Arms compilation source id ((resolution.hiddenScrutinee, payload) :: scope)
      expected bodyCertificate resolution.cases arms →
    ∀ item ∈ arms, ∀ binding ∈ item.1.bindings,
      source.inputs.any (fun input => decide (input.id = binding.1.id)) = false

private theorem arms_ordinary {compilation : SourceCoreCompatibleDataMatches.Context}
    {source : TypedSource} {scope : Scope} {id : StatementId} {expected : TypeSystem.Ty}
    {bodyCertificate : BodyCertificate} {cases : List TypedMatchCase} {arms : List (Pattern × Expr)}
    (certified : Arms compilation source id scope expected bodyCertificate cases arms)
    (binders : ∀ arm ∈ cases, ∀ binder ∈ arm.pattern.binderIds,
      source.inputs.any (fun input => decide (input.id = binder)) = false) :
    ∀ item ∈ arms, ∀ binding ∈ item.1.bindings,
      source.inputs.any (fun input => decide (input.id = binding.1.id)) = false := by
  revert binders
  induction certified with
  | nil => intro binders item member; cases member
  | @cons arm rest pattern body arms patternCertified matcherTyped bodyCertified tail ih =>
    intro binders item member binding bindingMember
    rcases List.mem_cons.mp member with rfl | remaining
    · have ids := certificate_binding_ids patternCertified
      have selected : binding.1.id ∈ arm.pattern.binderIds := by
        rw [← ids]
        exact List.mem_map.mpr ⟨binding, bindingMember, rfl⟩
      exact binders arm (by simp) binding.1.id selected
    · exact ih (fun arm member => binders arm (List.mem_cons_of_mem _ member)) item remaining binding bindingMember

/-- Only source binder IDs are inspected to classify the actual arm sites.
This condition is independent of runtime matching and body execution. -/
theorem ordinary_of_source_ids {compilation : SourceCoreCompatibleDataMatches.Context}
    {source : TypedSource} {scope : Scope} {id : StatementId} {resolution : MatchResolution}
    {resultType : Ty} {internalReason : Word} {expressionCertificate : ExpressionCertificate}
    {bodyCertificate : BodyCertificate} {code : Expr}
    (certificate : Certificate compilation source scope id resolution resultType internalReason
      expressionCertificate bodyCertificate code)
    (hidden : source.inputs.any (fun input => decide (input.id = resolution.hiddenScrutinee)) = false)
    (binders : ∀ arm ∈ resolution.cases, ∀ binder ∈ arm.pattern.binderIds,
      source.inputs.any (fun input => decide (input.id = binder)) = false) : Ordinary certificate := by
  exact ⟨hidden, fun _ _ _ certified => arms_ordinary certified binders⟩

/-- Scrutinee completion constructs independent source selection and the
entire real prefix. Body execution is absent from the hypotheses. Source
heap and Core store extensions account for every actual allocation. -/
theorem Certificate.success_prefix
    {compilation : SourceCoreCompatibleDataMatches.Context} {source : TypedSource} {scope : Scope}
    {id : StatementId} {resolution : MatchResolution} {resultType : Ty} {internalReason : Word}
    {expressionCertificate : ExpressionCertificate} {bodyCertificate : BodyCertificate} {code : Expr}
    (certificate : Certificate compilation source scope id resolution resultType internalReason
      expressionCertificate bodyCertificate code) (ordinary : Ordinary certificate)
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    {context : SourceSemantics.Context} (valid : CompatiblePatternLeaves.ContextValid compilation context)
    (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)
    {node : ExpressionNode} (found : source.lookupExpression? resolution.scrutinee = some node)
    {lowered : SourceCoreBasic.LoweredExpr}
    (uniqueExpression : ∀ lowered', expressionCertificate scope resolution.scrutinee lowered' → lowered' = lowered)
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {heap : Dynamic.Heap} {before store : Store} {sourceValue : Dynamic.Value} {value : Value} {payload : Ty}
    (represented : CompatiblePayload.ValueRep compilation.checked registry functions mapping world node.type sourceValue value payload)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions mapping world heap store)
    (agrees : EnvironmentsAgree ξ canonical actual)
    {contextLocation : Location} {native : NativeFrame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual before (lowered.expression.rename ξ) (.inRight .word value) store) :
    ∃ hiddenHeap location selection finalScope finalEnvironment finalHeap finalCanonical finalActual finalStore
        finalMap finalWorld finalEmbedding body,
      Dynamic.Heap.Allocates heap node.type (some sourceValue) location hiddenHeap ∧
      Dynamic.MatchCasesSelect context sourceValue resolution.cases resolution.defaultBody selection ∧
      SelectedBody bodyCertificate ((resolution.hiddenScrutinee, payload) :: scope) environment hiddenHeap
        resultType selection finalScope finalEnvironment finalHeap body ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog) finalMap finalWorld administrative
        finalScope finalEnvironment finalCanonical ambient.definitions ∧
      CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      EnvironmentsAgree finalEmbedding finalCanonical finalActual ∧
      ContinuationAgreement actual before (code.rename ξ) finalActual finalStore (body.rename finalEmbedding) := by
  cases certificate with
  | @matchWith statementNode statementType scrutineeNode type scrutinee arms fallback branches _
      readStatement allowed form requirements hiddenOwned hiddenFresh scrutineeOwned scrutineeFound projection
      expressionCertified sameType armCertificates fallbackCertificate branchesCertified hiddenCompiled =>
    have nodeEq := Option.some.inj (found.symm.trans scrutineeFound)
    subst scrutineeNode
    have expressionEq := uniqueExpression scrutinee expressionCertified
    subst scrutinee
    have payloadEq : payload = type := Except.ok.inj
      (represented.projection.symm.trans (CompatibleExpressionReads.projectType_of_accepted projection))
    subst payload
    obtain ⟨hiddenOrdinary, ordinaryArms⟩ := ordinary
    have kinds := ordinaryArms type node.type arms armCertificates
    rw [allocator] at hiddenCompiled
    obtain ⟨hiddenHeap, location, hiddenStore, hiddenWorld, hiddenMap, hiddenRef, allocated, hiddenEnvironments,
      hiddenHeaps, hiddenMaps, hiddenWorlds, hiddenFrame, hiddenLayout, hiddenAgreement⟩ :=
      CompatibleMatchHiddenPrefix.success_prefix onError hiddenOrdinary hiddenFresh hiddenCompiled definitions registered
        (model := CompatibleAmbientHeap.payloadModel compilation.checked registry functions)
        represented environments heaps agrees reference read evaluated
    have bound : contextLocation < store.length := (List.getElem?_eq_some_iff.mp read).1
    obtain ⟨stillUnmapped, stillRead⟩ := hiddenFrame contextLocation unmapped bound
    have nextRead := stillRead.trans read
    have nextReference : (hiddenRef :: canonical)[((resolution.hiddenScrutinee, type) :: scope).length + 1 + globals]? =
        some (.cellRef frame.type contextLocation) := by
      have indexEq : ((resolution.hiddenScrutinee, type) :: scope).length + 1 + globals =
          (scope.length + 1 + globals) + 1 := by simp only [List.length_cons]; omega
      rw [indexEq]
      exact reference
    have nextRepresented := represented.extend (.refl _) hiddenMaps hiddenWorlds
    obtain ⟨selection, decision⟩ := CompatibleMatchDecision.Arms.decides armCertificates fallbackCertificate valid
      catalogValid extended nextRepresented
    obtain ⟨finalScope, finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore, finalMap, finalWorld,
      finalEmbedding, body, selected, finalEnvironments, finalHeaps, maps, worlds, preserved, finalLayout, agreement⟩ :=
      CompatibleMatchBranchesPrefix.Decision.prefix definitions registered allocator decision armCertificates
        branchesCertified kinds nextReference nextRead stillUnmapped hiddenEnvironments hiddenHeaps hiddenLayout
    exact ⟨hiddenHeap, location, selection, finalScope, finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore,
      finalMap, finalWorld, finalEmbedding, body, allocated, decision.source, selected, finalEnvironments, finalHeaps,
      hiddenMaps.trans maps, hiddenWorlds.trans worlds, hiddenFrame.trans preserved, finalLayout, hiddenAgreement.trans agreement⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleMatchSelectionPrefix
