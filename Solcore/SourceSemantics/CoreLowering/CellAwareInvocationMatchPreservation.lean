import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationMatchHeads

/-! Forward execution of the actual match compiler head uses the reached
scrutinee state, real marked allocation prefix and selected staged body. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationMatchPreservation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open SourceCoreCompatibleDataMatches CompatibleMatchCertificates CompatibleMatchMeaning
open DataMatchBranchPrefix GenericLexicalContext CallableIndexedHistory
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)
open CallableIndexedOwnedAdmittedStagedMatchHeads (restore_rep restore_arm restore_parent)
open CellAwareInvocationMatchHeads
open CellAwareInvocationExpressionBounds
universe u
private theorem default_selected {context : SourceSemantics.Context} {value : Dynamic.Value}
    {cases : List TypedMatchCase} {fallback : Option (List StatementId)} {statements : List StatementId}
    (selected : Dynamic.MatchCasesSelect context value cases fallback (.default statements)) :
    fallback = some statements := by
  cases selected with
  | default => rfl
  | tail _ next => exact default_selected next
termination_by cases.length
decreasing_by simp_all

private theorem allocations_same {before left right : Dynamic.Heap} {type : TypeSystem.Ty} {value : Option Dynamic.Value}
    {a b : Dynamic.Location} (first : Dynamic.Heap.Allocates before type value a left)
    (second : Dynamic.Heap.Allocates before type value b right) : left = right := by
  cases first; cases second; rfl

private theorem binders_same {environment a b : Dynamic.Environment} {before left right : Dynamic.Heap}
    {binders : List TypedBinder} {values : List Dynamic.Value}
    (first : Dynamic.BindersAllocate environment before binders values a left)
    (second : Dynamic.BindersAllocate environment before binders values b right) : a = b ∧ left = right := by
  induction first generalizing b right with
  | nil => cases second; exact ⟨rfl, rfl⟩
  | cons allocation rest ih =>
    cases second with
    | cons allocation' rest' =>
      cases allocation
      cases allocation'
      exact ih rest'

private theorem extensions_same {owner : Resolved.DeclarationId} {context a b : SourceSemantics.Context}
    {binders : List TypedBinder} (first : BindersExtend owner context binders a)
    (second : BindersExtend owner context binders b) : a = b := by
  induction first generalizing b with
  | nil => cases second; rfl
  | cons head tail ih =>
    cases second with
    | cons head' tail' =>
      cases head
      cases head'
      exact ih tail'


variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry} {administrative : Core.Context}
  {bodyRelation : ActualBodyInvocation.BodyRelation}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  (index : ActualBodyInvocation.Index compiled bodyRelation)
  {allocationSource : TypedSource}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}
  {solved : List SolvedRequirement} {sourceCells : Option SourceCoreSourceCells.Allocator}
  {ambientDefinitions : Option Core.DataEnvironment}
local notation "compilation" => (SourceCoreCompatibleDataMatches.Context.mk (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) solved sourceCells ambientDefinitions)
local notation "ambient" => CallableIndexedAmbient.ambientDefinitions compiled.indexed
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions
local notation "instances" => GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment
local notation "cells" => GeneralizedLocalDescriptorHeap.cellModel model instances
local notation "frame" => compiled.indexed.ancestry.layout.frame
local notation "globals" => compiled.indexed.base.globals.length
local notation "layouts" => compiled.indexed.layouts

include bridge functions index in
theorem preserves
    (sourceEq : invocation.source = index.source)
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (allocator : (compilation).sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      ((layouts).allocatorAt index.owner index.active onError)))
    (definitions : (layouts).definitions = (ambient).definitions) (registered : (frame).Registered (ambient).definitions)
    (extended : SourceCoreRawMetadata.Extends (compilation).values.registry receiving)
    {context : SourceSemantics.Context} {control : ControlContext} {scope : Scope}
    {id : StatementId} {resolution : MatchResolution} {expected : TypeSystem.Ty} {type : Ty} {reason : Word}
    {expressionCertificate : ExpressionCertificate} {bodyCertificate : BodyCertificate} {code : Expr}
    (certificate : CompatibleMatchCertificates.Certificate compilation allocationSource scope id resolution type reason
      expressionCertificate bodyCertificate code)
    (ordinary : CompatibleMatchSelectionPrefix.Ordinary certificate)
    (unique : NodeOccurrencesUnique invocation.source)
    (literals : IntegerLiteralResolution → Prop)
    (signatures : context.signatures = (compilation).signatures)
    (numericRequirements : ∀ numeric, literals numeric → RequirementProves context numeric.requirement numeric.predicate)
    (sites : CompatibleMatchDecision.Certificate.LiteralSites literals certificate)
    (catalogValid : SignatureCatalogWellFormed (compilation).checked.signatures)
    {node : ExpressionNode} (found : invocation.source.lookupExpression? resolution.scrutinee = some node)
    (typed : ExpressionHasType invocation.source context resolution.scrutinee node.type)
    {compilerNode : ExpressionNode}
    (compilerFound : allocationSource.lookupExpression? resolution.scrutinee = some compilerNode)
    (sameType : compilerNode.type = node.type)
    {statement : StatementNode}
    (statementFound : index.source.lookupStatement? id = some statement)
    (statementForm : statement.form = .matchWith resolution)
    {lowered : SourceCoreBasic.LoweredExpr}
    (uniqueExpression : ∀ other, expressionCertificate scope resolution.scrutinee other → other = lowered)
    {caseFacts : List BodyFacts}
    (casesTyped : MatchCasesHaveType invocation.source control context node.type resolution.cases caseFacts)
    (defaultTyped : ∀ {statements}, resolution.defaultBody = some statements →
      ∃ finalContext facts, StatementsHaveType invocation.source control context statements finalContext facts)
    (budget : Nat)
    (producer : ProtectedStateTransition.CellAllocation.Producer
      (catalog := CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      callerProtocol layouts frame cells)
    (stateBindings : ProtectedStateTransition.Bindings callerProtocol)
    (children : ∀ child, child < budget → PreservesAt (attachment := attachment) bridge context model index stages invocation expressionCertificate faults child)
    (armMeaning : ArmPreservesBelow (administrative := administrative) (receiving := receiving)
      (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions index producer context control resolution bodyCertificate expected type budget scope)
    (defaultMeaning : DefaultPreservesBelow (administrative := administrative) (receiving := receiving)
      (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions index producer context control resolution bodyCertificate expected type budget scope)
    {size : Nat} (within : size ≤ budget)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming}
    {outcome : Staging.Recursive.BodyOutcome}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical (ambient).definitions)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext (ambient).definitions)
    (runtime : Dynamic.SourceRuntimeValid program context index.source)
    (covers : invocation.evidence.Covers context)
    (sameLedger : context.solvedRequirements = index.compilation.solvedRequirements)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (authority : CellAwareScopeAuthority.At instances index.owner index.active mapping world before store environment)
    (physical : CellAwareInvocationPhysical.Physical (attachment := attachment) compiled index context scope canonical mapping world before store environment)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (sameLocation : owner.key.frameLocation = physical.location)
    (ready : ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native)
    (trace : Staging.Recursive.Size.Match program stages size invocation context environment before resolution outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      Represents model finalMap finalWorld false expected type faults outcome value ∧
      GenericHeap.CellHeapRepresents cells finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect instances mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ Post bridge context expected outcome reached := by
  have expression : expressionCertificate scope resolution.scrutinee lowered := by
    cases certificate with
    | matchWith _ _ _ _ _ _ _ _ _ certified =>
      exact (uniqueExpression _ certified) ▸ certified
  have hiddenFresh := CallableIndexedOwnedLocalIdentityFreshness.match_hidden_fresh physical.ownership statementFound statementForm
  cases trace with
  | @scrutineeFault exprSize _ _ _ _ _ _ failure fault =>
    have smaller : exprSize < budget := Nat.lt_of_lt_of_le
      (Staging.Recursive.Size.child_lt_stepSize (by simp)) within
    obtain ⟨value, finalStore, finalMap, finalWorld, coreEval, related, heapRep, maps, worlds, preserved, metadata, effect,
      reached, relatedState, post⟩ :=
      children _ smaller expression found typed environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation fault
    cases related with
    | fault represented =>
      exact ⟨_, finalStore, finalMap, finalWorld,
        CompatibleMatchScrutineeReflection.Certificate.failure_preserves certificate uniqueExpression coreEval,
        .fault represented, heapRep, maps, worlds, preserved, metadata, effect, reached, relatedState, post.at_fault_type⟩
  | patternFault contains evaluated allocated fault =>
    exact False.elim (CompatibleMatchSourceSelection.Certificate.not_pattern_fault_with_signatures certificate signatures _ fault)
  | @arm exprSize bodySize _ _ armContext innerFinal _ armEnvironment _ middle hidden bound _ _ sourceNode sourceValue
      location statements bindings innerOutcome contains sourceEval sourceHidden selected sourceExtended sourceAllocated sourceBody =>
    have exprSmaller : exprSize < budget := Nat.lt_of_lt_of_le
      (Staging.Recursive.Size.child_lt_stepSize (by simp)) within
    have bodyWithin : bodySize ≤ budget := Nat.le_trans
      (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) within
    have nodeEq : sourceNode = node := Option.some.inj
      ((lookupExpression?_complete unique contains).symm.trans found)
    subst sourceNode
    obtain ⟨value, middleStore, middleMap, middleWorld, coreEval, represented, middleRelated,
      firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect, middleState, firstRelated, firstPost⟩ :=
      children _ exprSmaller expression found typed environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation sourceEval
    cases represented with
    | value represented =>
      obtain ⟨valueFacts, middleReady⟩ := firstPost.at_value
      let middlePhysical := physical.transport firstEffect firstFrame
      have reference := physical.reference
      have read := middlePhysical.read
      have unmapped := middlePhysical.unmapped
      obtain ⟨hiddenHeap, hiddenLocation, finalScope, selectedEnvironment, selectedHeap, selectedCanonical,
        selectedActual, selectedStore, selectedMap, selectedWorld, selectedEmbedding, selectedContext, body,
        hiddenAllocated, selectedAgain, selectedBody, selectedEnv, selectedRelated, secondMaps, secondWorlds,
        secondFrame, selectedLayout, selectedTyped, selectedReference, selectedRead, selectedUnmapped, spine, agreement, selectedState, selectionRelated, ⟨returnTo⟩, secondEffect⟩ :=
        CellAwareMatchSelectedPrefix.selected_with_effect certificate ordinary onError allocator literals signatures numericRequirements sites
          catalogValid instances GeneralizedLocalDescriptorHeap.ordinary_cells callerProtocol producer stateBindings definitions registered extended compilerFound uniqueExpression (sameType.symm ▸ represented) (environments.extend firstMaps firstWorlds)
          middleRelated agrees (actualTyped.weaken firstWorlds) reference read unmapped coreEval middleState ready selected
      rw [sameType] at hiddenAllocated
      have hiddenEq := allocations_same hiddenAllocated sourceHidden
      subst hiddenHeap
      cases selectedBody with
      | arm binders allocated bodyCertified =>
        obtain ⟨sameEnvironment, sameHeap⟩ := binders_same allocated sourceAllocated
        subst selectedEnvironment
        subst selectedHeap
        obtain ⟨staticContext, staticFinal, facts, extended, typed, _⟩ :=
          DataMatchSourceScopes.MatchCasesSelect.arm_scope casesTyped selected
        have sameContext := extensions_same extended sourceExtended
        subst staticContext
        have selectedReady := (CallableIndexedOwnedMatchPrefixAdmission.after_arm_prefix bridge middleState selectedState middleReady valueFacts sourceHidden
          casesTyped selected sourceExtended sourceAllocated secondFrame).1
        have selectedMembers := selected_members statementFound statementForm (sourceEq ▸ casesTyped) selected
        let selectedPhysical := CellAwareInvocationMatchPhysical.arm middlePhysical hiddenFresh
          (by simpa only [binders] using selectedMembers) (by simpa only [binders, sourceEq] using sourceExtended)
          (by simpa only [binders] using allocated) secondEffect selectedReference selectedRead selectedUnmapped
        have selectedAuthority : CellAwareScopeAuthority.At instances index.owner index.active selectedMap selectedWorld bound selectedStore armEnvironment :=
          CellAwareInvocationMatchPhysical.allocated_authority (index := index) allocated
            (authority.transport (firstEffect.trans secondEffect))
        have fields := Dynamic.BindersExtend.runtimeContextFields sourceExtended
        obtain ⟨result, finalStore, finalMap, finalWorld, bodyEval, related, finalHeapRep,
          thirdMaps, thirdWorlds, thirdFrame, thirdMetadata, thirdEffect, bodyState, bodyRelated, bodyReady⟩ :=
          armMeaning rfl selected (.arm binders allocated bodyCertified) sourceExtended typed _ bodyWithin selectedEnv selectedRelated
            (binders_agree sourceExtended (arm_monomorphic casesTyped selected)
              (locals.mono (firstMetadata.trans (.of_allocation sourceHidden))) sourceAllocated)
            selectedLayout selectedTyped (runtime.transport fields) (fields.covers covers) (fields.solvedRequirements.trans sameLedger)
            (by simpa only [sourceEq] using (show ProtectedStateImperativeTypedSourceSites.Statements invocation.source armContext statements from ⟨control, staticFinal, facts, typed⟩))
            selectedState selectedReady selectedAuthority selectedPhysical owner sameLocation ready sourceBody
        exact ⟨result, finalStore, finalMap, finalWorld, agreement.wrap bodyEval, restore_rep related environment,
          finalHeapRep, firstMaps.trans (secondMaps.trans thirdMaps), firstWorlds.trans (secondWorlds.trans thirdWorlds),
          firstFrame.trans (secondFrame.trans thirdFrame),
          firstMetadata.trans ((Dynamic.HeapMetadataExtend.of_allocation sourceHidden).trans
            ((binders_metadata sourceAllocated).trans thirdMetadata)),
          firstEffect.trans (secondEffect.trans thirdEffect),
          ⟨returnTo.restore bodyState, callerProtocol.trans firstRelated
            (callerProtocol.trans selectionRelated (callerProtocol.trans bodyRelated (returnTo.related bodyState))),
            restore_arm bridge returnTo sourceExtended bodyState environment bodyReady⟩⟩
  | @default exprSize bodySize _ _ innerFinal _ _ middle hidden _ _ sourceNode sourceValue location statements innerOutcome
      contains sourceEval sourceHidden selected sourceBody =>
    have exprSmaller : exprSize < budget := Nat.lt_of_lt_of_le
      (Staging.Recursive.Size.child_lt_stepSize (by simp)) within
    have bodyWithin : bodySize ≤ budget := Nat.le_trans
      (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) within
    have nodeEq : sourceNode = node := Option.some.inj
      ((lookupExpression?_complete unique contains).symm.trans found)
    subst sourceNode
    obtain ⟨value, middleStore, middleMap, middleWorld, coreEval, represented, middleRelated,
      firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect, middleState, firstRelated, firstPost⟩ :=
      children _ exprSmaller expression found typed environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation sourceEval
    cases represented with
    | value represented =>
      obtain ⟨valueFacts, middleReady⟩ := firstPost.at_value
      let middlePhysical := physical.transport firstEffect firstFrame
      have reference := physical.reference
      have read := middlePhysical.read
      have unmapped := middlePhysical.unmapped
      obtain ⟨hiddenHeap, hiddenLocation, finalScope, selectedEnvironment, selectedHeap, selectedCanonical,
        selectedActual, selectedStore, selectedMap, selectedWorld, selectedEmbedding, selectedContext, body,
        hiddenAllocated, selectedAgain, selectedBody, selectedEnv, selectedRelated, secondMaps, secondWorlds,
        secondFrame, selectedLayout, selectedTyped, selectedReference, selectedRead, selectedUnmapped, spine, agreement, selectedState, selectionRelated, ⟨returnTo⟩, secondEffect⟩ :=
        CellAwareMatchSelectedPrefix.selected_with_effect certificate ordinary onError allocator literals signatures numericRequirements sites
          catalogValid instances GeneralizedLocalDescriptorHeap.ordinary_cells callerProtocol producer stateBindings definitions registered extended compilerFound uniqueExpression (sameType.symm ▸ represented) (environments.extend firstMaps firstWorlds)
          middleRelated agrees (actualTyped.weaken firstWorlds) reference read unmapped coreEval middleState ready selected
      rw [sameType] at hiddenAllocated
      have hiddenEq := allocations_same hiddenAllocated sourceHidden
      subst hiddenHeap
      cases selectedBody with
      | default bodyCertified =>
        have selectedReady := CallableIndexedOwnedMatchAdmission.after_hidden bridge middleState selectedState middleReady valueFacts sourceHidden secondFrame
        obtain ⟨staticFinal, facts, typed⟩ := defaultTyped (default_selected selected)
        let selectedPhysical := CellAwareInvocationMatchPhysical.parent middlePhysical hiddenFresh secondEffect selectedReference selectedRead selectedUnmapped
        have selectedAuthority : CellAwareScopeAuthority.At instances index.owner index.active selectedMap selectedWorld hidden selectedStore environment :=
          authority.transport (firstEffect.trans secondEffect)
        obtain ⟨result, finalStore, finalMap, finalWorld, bodyEval, related, finalHeapRep,
          thirdMaps, thirdWorlds, thirdFrame, thirdMetadata, thirdEffect, bodyState, bodyRelated, bodyReady⟩ :=
          defaultMeaning (environment := environment) (heap := hidden) rfl selected (.default bodyCertified) typed _ bodyWithin selectedEnv selectedRelated
            (locals.mono (firstMetadata.trans (.of_allocation sourceHidden))) selectedLayout selectedTyped runtime covers sameLedger
            (by simpa only [sourceEq] using (show ProtectedStateImperativeTypedSourceSites.Statements invocation.source context statements from ⟨control, staticFinal, facts, typed⟩))
            selectedState selectedReady selectedAuthority selectedPhysical owner sameLocation ready sourceBody
        exact ⟨result, finalStore, finalMap, finalWorld, agreement.wrap bodyEval, restore_rep related environment,
          finalHeapRep, firstMaps.trans (secondMaps.trans thirdMaps), firstWorlds.trans (secondWorlds.trans thirdWorlds),
          firstFrame.trans (secondFrame.trans thirdFrame),
          firstMetadata.trans ((Dynamic.HeapMetadataExtend.of_allocation sourceHidden).trans thirdMetadata),
          firstEffect.trans (secondEffect.trans thirdEffect),
          ⟨returnTo.restore bodyState, callerProtocol.trans firstRelated
            (callerProtocol.trans selectionRelated (callerProtocol.trans bodyRelated (returnTo.related bodyState))),
            restore_parent bridge returnTo bodyState environment bodyReady⟩⟩
  | @noBranch exprSize _ _ _ _ middle hidden _ sourceNode sourceValue location contains sourceEval sourceHidden selected =>
    have exprSmaller : exprSize < budget := Nat.lt_of_lt_of_le
      (Staging.Recursive.Size.child_lt_stepSize (by simp)) within
    have nodeEq : sourceNode = node := Option.some.inj
      ((lookupExpression?_complete unique contains).symm.trans found)
    subst sourceNode
    obtain ⟨value, middleStore, middleMap, middleWorld, coreEval, represented, middleRelated,
      firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect, middleState, firstRelated, firstPost⟩ :=
      children _ exprSmaller expression found typed environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation sourceEval
    cases represented with
    | value represented =>
      obtain ⟨valueFacts, middleReady⟩ := firstPost.at_value
      let middlePhysical := physical.transport firstEffect firstFrame
      have reference := physical.reference
      have read := middlePhysical.read
      have unmapped := middlePhysical.unmapped
      obtain ⟨hiddenHeap, hiddenLocation, finalScope, selectedEnvironment, selectedHeap, selectedCanonical,
        selectedActual, selectedStore, selectedMap, selectedWorld, selectedEmbedding, selectedContext, body,
        hiddenAllocated, selectedAgain, selectedBody, selectedEnv, selectedRelated, secondMaps, secondWorlds,
        secondFrame, selectedLayout, selectedTyped, selectedReference, selectedRead, selectedUnmapped, spine, agreement, selectedState, selectionRelated, ⟨returnTo⟩, secondEffect⟩ :=
        CellAwareMatchSelectedPrefix.selected_with_effect certificate ordinary onError allocator literals signatures numericRequirements sites
          catalogValid instances GeneralizedLocalDescriptorHeap.ordinary_cells callerProtocol producer stateBindings definitions registered extended compilerFound uniqueExpression (sameType.symm ▸ represented) (environments.extend firstMaps firstWorlds)
          middleRelated agrees (actualTyped.weaken firstWorlds) reference read unmapped coreEval middleState ready selected
      rw [sameType] at hiddenAllocated
      have hiddenEq := allocations_same hiddenAllocated sourceHidden
      subst hiddenHeap
      cases selectedBody
      have selectedReady := CallableIndexedOwnedMatchAdmission.after_hidden bridge middleState selectedState middleReady valueFacts sourceHidden secondFrame
      exact ⟨_, selectedStore, selectedMap, selectedWorld, agreement.wrap (.inRight (.inLeft (.inLeft .unit))),
        .fallthrough environment (.inl rfl), selectedRelated, firstMaps.trans secondMaps, firstWorlds.trans secondWorlds,
        firstFrame.trans secondFrame, firstMetadata.trans (.of_allocation sourceHidden), firstEffect.trans secondEffect,
        ⟨returnTo.restore selectedState, callerProtocol.trans firstRelated
          (callerProtocol.trans selectionRelated (returnTo.related selectedState)),
          restore_parent bridge returnTo selectedState environment (outcome := .fallthrough environment) selectedReady⟩⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationMatchPreservation
