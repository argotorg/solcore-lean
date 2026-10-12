import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedMatchHeads

/-! Forward execution of the actual match compiler head uses the reached
scrutinee state, real marked allocation prefix and selected staged body. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedMatchPreservation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open SourceCoreCompatibleDataMatches CompatibleMatchCertificates CompatibleMatchMeaning
open DataMatchBranchPrefix GenericLexicalContext CallableIndexedHistory
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)
open CallableIndexedOwnedAdmittedStagedMatchHeads
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
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}
  {solved : List SolvedRequirement} {sourceCells : Option SourceCoreSourceCells.Allocator}
  {ambientDefinitions : Option Core.DataEnvironment}
local notation "compilation" => (SourceCoreCompatibleDataMatches.Context.mk (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) solved sourceCells ambientDefinitions)
local notation "ambient" => CallableIndexedAmbient.ambientDefinitions compiled.indexed
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions

include bridge functions in
theorem preserves
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (allocator : (compilation).sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (definitions : layouts.definitions = (ambient).definitions) (registered : frame.Registered (ambient).definitions)
    (extended : SourceCoreRawMetadata.Extends (compilation).values.registry receiving)
    {context : SourceSemantics.Context} {control : ControlContext} {scope : Scope}
    {id : StatementId} {resolution : MatchResolution} {expected : TypeSystem.Ty} {type : Ty} {reason : Word}
    {expressionCertificate : ExpressionCertificate} {bodyCertificate : BodyCertificate} {code : Expr}
    (certificate : CompatibleMatchCertificates.Certificate compilation invocation.source scope id resolution type reason
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
    {lowered : SourceCoreBasic.LoweredExpr}
    (uniqueExpression : ∀ other, expressionCertificate scope resolution.scrutinee other → other = lowered)
    {caseFacts : List BodyFacts}
    (casesTyped : MatchCasesHaveType invocation.source control context node.type resolution.cases caseFacts)
    (defaultTyped : ∀ {statements}, resolution.defaultBody = some statements →
      ∃ finalContext facts, StatementsHaveType invocation.source control context statements finalContext facts)
    (budget : Nat)
    (condition : Location → NativeFrame → Prop)
    (producer : ProtectedStateTransition.MarkedAllocation.Producer callerProtocol layouts frame model)
    (stateBindings : ProtectedStateTransition.Bindings callerProtocol)
    (acquire : ∀ location native, condition location native →
      ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary location native)
    (children : ∀ child, child < budget → PreservesAt bridge context model stages invocation expressionCertificate faults child)
    (armMeaning : ArmPreservesBelow (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions condition context control resolution bodyCertificate expected type budget scope)
    (defaultMeaning : DefaultPreservesBelow (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions condition context control resolution bodyCertificate expected type budget scope)
    {size : Nat} (within : size ≤ budget)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    {outcome : Staging.Recursive.BodyOutcome}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical (ambient).definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext (ambient).definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (conditioned : condition contextLocation native)
    (admitted : Admission bridge context initial)
    (trace : Staging.Recursive.Size.Match program stages size invocation context environment before resolution outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      Represents model finalMap finalWorld false expected type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ Post bridge context expected outcome reached := by
  have expression : expressionCertificate scope resolution.scrutinee lowered := by
    cases certificate with
    | matchWith _ _ _ _ _ _ _ _ _ certified =>
      exact (uniqueExpression _ certified) ▸ certified
  cases trace with
  | @scrutineeFault exprSize _ _ _ _ _ _ failure fault =>
    have smaller : exprSize < budget := Nat.lt_of_lt_of_le
      (Staging.Recursive.Size.child_lt_stepSize (by simp)) within
    obtain ⟨value, finalStore, finalMap, finalWorld, coreEval, related, heapRep, maps, worlds, preserved, metadata,
      reached, relatedState, post⟩ :=
      children _ smaller expression found typed environments heaps locals agrees actualTyped initial admitted fault
    cases related with
    | fault represented =>
      exact ⟨_, finalStore, finalMap, finalWorld,
        CompatibleMatchScrutineeReflection.Certificate.failure_preserves certificate uniqueExpression coreEval,
        .fault represented, heapRep, maps, worlds, preserved, metadata, reached, relatedState, post.at_fault_type⟩
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
      firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, firstRelated, firstPost⟩ :=
      children _ exprSmaller expression found typed environments heaps locals agrees actualTyped initial admitted sourceEval
    cases represented with
    | value represented =>
      obtain ⟨valueFacts, middleReady⟩ := firstPost.at_value
      obtain ⟨stillUnmapped, stillRead⟩ := firstFrame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1
      obtain ⟨hiddenHeap, hiddenLocation, finalScope, selectedEnvironment, selectedHeap, selectedCanonical,
        selectedActual, selectedStore, selectedMap, selectedWorld, selectedEmbedding, selectedContext, body,
        hiddenAllocated, selectedAgain, selectedBody, selectedEnv, selectedRelated, secondMaps, secondWorlds,
        secondFrame, selectedLayout, selectedTyped, selectedReference, selectedRead, selectedUnmapped, spine, agreement, selectedState, selectionRelated, ⟨returnTo⟩⟩ :=
        CompatibleMatchTypedSelectionPrefix.Stateful.Certificate.selected_prefix_sized_with_literals certificate ordinary onError allocator literals signatures numericRequirements sites
          catalogValid callerProtocol producer stateBindings definitions registered extended found uniqueExpression represented (environments.extend firstMaps firstWorlds)
          middleRelated agrees (actualTyped.weaken firstWorlds) reference (stillRead.trans read) stillUnmapped coreEval middleState (acquire contextLocation native conditioned) selected
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
        obtain ⟨result, finalStore, finalMap, finalWorld, bodyEval, related, finalHeapRep,
          thirdMaps, thirdWorlds, thirdFrame, thirdMetadata, bodyState, bodyRelated, bodyReady⟩ :=
          armMeaning rfl selected (.arm binders allocated bodyCertified) sourceExtended typed bodyWithin selectedEnv selectedRelated
            (binders_agree sourceExtended (arm_monomorphic casesTyped selected)
              (locals.mono (firstMetadata.trans (.of_allocation sourceHidden))) sourceAllocated)
            selectedLayout selectedTyped selectedReference selectedRead selectedUnmapped selectedState conditioned selectedReady sourceBody
        exact ⟨result, finalStore, finalMap, finalWorld, agreement.wrap bodyEval, restore_rep related environment,
          finalHeapRep, firstMaps.trans (secondMaps.trans thirdMaps), firstWorlds.trans (secondWorlds.trans thirdWorlds),
          firstFrame.trans (secondFrame.trans thirdFrame),
          firstMetadata.trans ((Dynamic.HeapMetadataExtend.of_allocation sourceHidden).trans
            ((binders_metadata sourceAllocated).trans thirdMetadata)),
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
      firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, firstRelated, firstPost⟩ :=
      children _ exprSmaller expression found typed environments heaps locals agrees actualTyped initial admitted sourceEval
    cases represented with
    | value represented =>
      obtain ⟨valueFacts, middleReady⟩ := firstPost.at_value
      obtain ⟨stillUnmapped, stillRead⟩ := firstFrame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1
      obtain ⟨hiddenHeap, hiddenLocation, finalScope, selectedEnvironment, selectedHeap, selectedCanonical,
        selectedActual, selectedStore, selectedMap, selectedWorld, selectedEmbedding, selectedContext, body,
        hiddenAllocated, selectedAgain, selectedBody, selectedEnv, selectedRelated, secondMaps, secondWorlds,
        secondFrame, selectedLayout, selectedTyped, selectedReference, selectedRead, selectedUnmapped, spine, agreement, selectedState, selectionRelated, ⟨returnTo⟩⟩ :=
        CompatibleMatchTypedSelectionPrefix.Stateful.Certificate.selected_prefix_sized_with_literals certificate ordinary onError allocator literals signatures numericRequirements sites
          catalogValid callerProtocol producer stateBindings definitions registered extended found uniqueExpression represented (environments.extend firstMaps firstWorlds)
          middleRelated agrees (actualTyped.weaken firstWorlds) reference (stillRead.trans read) stillUnmapped coreEval middleState (acquire contextLocation native conditioned) selected
      have hiddenEq := allocations_same hiddenAllocated sourceHidden
      subst hiddenHeap
      cases selectedBody with
      | default bodyCertified =>
        have selectedReady := CallableIndexedOwnedMatchAdmission.after_hidden bridge middleState selectedState middleReady valueFacts sourceHidden secondFrame
        obtain ⟨staticFinal, facts, typed⟩ := defaultTyped (default_selected selected)
        obtain ⟨result, finalStore, finalMap, finalWorld, bodyEval, related, finalHeapRep,
          thirdMaps, thirdWorlds, thirdFrame, thirdMetadata, bodyState, bodyRelated, bodyReady⟩ :=
          defaultMeaning (environment := environment) (heap := hidden) rfl selected (.default bodyCertified) typed bodyWithin selectedEnv selectedRelated
            (locals.mono (firstMetadata.trans (.of_allocation sourceHidden))) selectedLayout selectedTyped selectedReference selectedRead selectedUnmapped selectedState conditioned selectedReady sourceBody
        exact ⟨result, finalStore, finalMap, finalWorld, agreement.wrap bodyEval, restore_rep related environment,
          finalHeapRep, firstMaps.trans (secondMaps.trans thirdMaps), firstWorlds.trans (secondWorlds.trans thirdWorlds),
          firstFrame.trans (secondFrame.trans thirdFrame),
          firstMetadata.trans ((Dynamic.HeapMetadataExtend.of_allocation sourceHidden).trans thirdMetadata),
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
      firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, firstRelated, firstPost⟩ :=
      children _ exprSmaller expression found typed environments heaps locals agrees actualTyped initial admitted sourceEval
    cases represented with
    | value represented =>
      obtain ⟨valueFacts, middleReady⟩ := firstPost.at_value
      obtain ⟨stillUnmapped, stillRead⟩ := firstFrame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1
      obtain ⟨hiddenHeap, hiddenLocation, finalScope, selectedEnvironment, selectedHeap, selectedCanonical,
        selectedActual, selectedStore, selectedMap, selectedWorld, selectedEmbedding, selectedContext, body,
        hiddenAllocated, selectedAgain, selectedBody, selectedEnv, selectedRelated, secondMaps, secondWorlds,
        secondFrame, selectedLayout, selectedTyped, selectedReference, selectedRead, selectedUnmapped, spine, agreement, selectedState, selectionRelated, ⟨returnTo⟩⟩ :=
        CompatibleMatchTypedSelectionPrefix.Stateful.Certificate.selected_prefix_sized_with_literals certificate ordinary onError allocator literals signatures numericRequirements sites
          catalogValid callerProtocol producer stateBindings definitions registered extended found uniqueExpression represented (environments.extend firstMaps firstWorlds)
          middleRelated agrees (actualTyped.weaken firstWorlds) reference (stillRead.trans read) stillUnmapped coreEval middleState (acquire contextLocation native conditioned) selected
      have hiddenEq := allocations_same hiddenAllocated sourceHidden
      subst hiddenHeap
      cases selectedBody
      have selectedReady := CallableIndexedOwnedMatchAdmission.after_hidden bridge middleState selectedState middleReady valueFacts sourceHidden secondFrame
      exact ⟨_, selectedStore, selectedMap, selectedWorld, agreement.wrap (.inRight (.inLeft (.inLeft .unit))),
        .fallthrough environment (.inl rfl), selectedRelated, firstMaps.trans secondMaps, firstWorlds.trans secondWorlds,
        firstFrame.trans secondFrame, firstMetadata.trans (.of_allocation sourceHidden),
        ⟨returnTo.restore selectedState, callerProtocol.trans firstRelated
          (callerProtocol.trans selectionRelated (returnTo.related selectedState)),
          restore_parent bridge returnTo selectedState environment (outcome := .fallthrough environment) selectedReady⟩⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedMatchPreservation
