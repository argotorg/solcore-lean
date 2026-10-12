import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedMatchHeads

/-! Completed native match execution recovers the actual staged scrutinee and
selected branch, preserving allocation effects and the restored caller state. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedMatchReflection
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open SourceCoreCompatibleDataMatches CompatibleMatchCertificates CompatibleMatchMeaning
open DataMatchBranchPrefix GenericLexicalContext CallableIndexedHistory
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)
open CallableIndexedOwnedAdmittedStagedMatchHeads
universe u
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
theorem reflects
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
    (children : ∀ child, child < budget → ReflectsAt bridge context model stages invocation expressionCertificate faults child)
    (armMeaning : ArmReflectsBelow (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions condition context control resolution bodyCertificate expected type budget scope)
    (defaultMeaning : DefaultReflectsBelow (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions condition context control resolution bodyCertificate expected type budget scope)
    {size : Nat} (within : size ≤ budget)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    {value : Core.Value}
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
    (completed : EvaluationSize size actual store (code.rename ξ) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Match program stages sourceSize invocation context environment before resolution outcome after ∧
      Represents model finalMap finalWorld false expected type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ Post bridge context expected outcome reached := by
  have fullCertificate := certificate
  cases certificate with
  | matchWith readStatement allowed form requirements hiddenOwned hiddenFresh scrutineeOwned scrutineeFound projection
      expression sameType arms fallback branches hiddenCompiled =>
    obtain ⟨childNode, child, childSize, input, middleStore, childFound, childCertificate, childSmaller, childCompleted⟩ :=
      RecursiveNamedMatchSourceBounds.Certificate.initial_evaluation_sized fullCertificate completed
    have childEq := uniqueExpression _ childCertificate
    subst child
    have nodeEq := Option.some.inj (found.symm.trans childFound)
    subst childNode
    obtain ⟨sourceSize, sourceOutcome, middleHeap, middleMap, middleWorld, sourceEval, represented,
      middleRelated, firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, firstRelated, firstPost⟩ :=
      children childSize (Nat.lt_of_lt_of_le childSmaller within) childCertificate found typed
        environments heaps locals agrees actualTyped initial admitted childCompleted
    cases represented with
    | fault matched =>
      have failed := CompatibleMatchScrutineeReflection.Certificate.failure_preserves fullCertificate uniqueExpression childCompleted.sound
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound failed
      exact ⟨_, _, middleHeap, middleMap, middleWorld, .scrutineeFault sourceEval, .fault matched,
        middleRelated, firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, firstRelated, firstPost.at_fault_type⟩
    | value payload =>
      obtain ⟨valueTyped, middleReady⟩ := firstPost.at_value
      obtain ⟨stillUnmapped, stillRead⟩ := firstFrame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1
      obtain ⟨hiddenHeap, location, selection, finalScope, selectedEnvironment, selectedHeap, selectedCanonical,
        selectedActual, selectedStore, selectedMap, selectedWorld, selectedEmbedding, selectedContext, body,
        hiddenAllocated, selected, selectedBody, selectedEnv, selectedRelated, secondMaps, secondWorlds, secondFrame,
        selectedLayout, selectedTyped, selectedReference, selectedRead, selectedUnmapped, spine, agreement, selectedState, selectionRelated, ⟨returnTo⟩⟩ :=
        CompatibleMatchTypedSelectionPrefix.Stateful.Certificate.success_prefix_sized_with_literals fullCertificate ordinary onError allocator literals signatures numericRequirements sites
          catalogValid callerProtocol producer stateBindings definitions registered extended found uniqueExpression payload (environments.extend firstMaps firstWorlds)
          middleRelated agrees (actualTyped.weaken firstWorlds) reference (stillRead.trans read) stillUnmapped childCompleted.sound middleState (acquire contextLocation native conditioned)
      obtain ⟨bodySize, bodySmaller, bodyEval⟩ := agreement.remaining completed
      cases selectedBody with
      | @arm statements bindings compiledBindings finalEnvironment finalHeap body binders allocated certified =>
        obtain ⟨armContext, staticFinal, facts, extendedContext, bodyTyped, _⟩ :=
          DataMatchSourceScopes.MatchCasesSelect.arm_scope casesTyped selected
        have selectedReady := (CallableIndexedOwnedMatchPrefixAdmission.after_arm_prefix bridge
          middleState selectedState middleReady valueTyped hiddenAllocated casesTyped selected extendedContext allocated secondFrame).1
        obtain ⟨bodySourceSize, finalContext, outcome, after, finalMap, finalWorld, sourceBody, related,
          finalHeaps, thirdMaps, thirdWorlds, thirdFrame, thirdMetadata, bodyState, bodyRelated, bodyPost⟩ :=
          armMeaning rfl selected (.arm binders allocated certified) extendedContext bodyTyped
            (Nat.le_of_lt (Nat.lt_of_lt_of_le bodySmaller within)) selectedEnv selectedRelated
            (binders_agree extendedContext (arm_monomorphic casesTyped selected)
              (locals.mono (firstMetadata.trans (.of_allocation hiddenAllocated))) allocated)
            selectedLayout selectedTyped selectedReference selectedRead selectedUnmapped selectedState conditioned selectedReady bodyEval
        exact ⟨_, _, after, finalMap, finalWorld,
          .arm (lookupExpression?_sound found) sourceEval hiddenAllocated selected extendedContext allocated sourceBody,
          restore_rep related environment, finalHeaps,
          firstMaps.trans (secondMaps.trans thirdMaps), firstWorlds.trans (secondWorlds.trans thirdWorlds),
          firstFrame.trans (secondFrame.trans thirdFrame), firstMetadata.trans
            ((Dynamic.HeapMetadataExtend.of_allocation hiddenAllocated).trans ((binders_metadata allocated).trans thirdMetadata)),
          returnTo.restore bodyState, callerProtocol.trans firstRelated
            (callerProtocol.trans selectionRelated (callerProtocol.trans bodyRelated (returnTo.related bodyState))),
          restore_arm bridge returnTo extendedContext bodyState environment bodyPost⟩
      | @default statements body certified =>
        have selectedReady := CallableIndexedOwnedMatchAdmission.after_hidden bridge
          middleState selectedState middleReady valueTyped hiddenAllocated secondFrame
        obtain ⟨staticFinal, facts, bodyTyped⟩ := defaultTyped selected.defaultBody_eq
        obtain ⟨bodySourceSize, finalContext, outcome, after, finalMap, finalWorld, sourceBody, related,
          finalHeaps, thirdMaps, thirdWorlds, thirdFrame, thirdMetadata, bodyState, bodyRelated, bodyPost⟩ :=
          defaultMeaning (environment := environment) (heap := hiddenHeap) rfl selected (.default certified) bodyTyped
            (Nat.le_of_lt (Nat.lt_of_lt_of_le bodySmaller within)) selectedEnv selectedRelated
            (locals.mono (firstMetadata.trans (.of_allocation hiddenAllocated))) selectedLayout selectedTyped
            selectedReference selectedRead selectedUnmapped selectedState conditioned selectedReady bodyEval
        exact ⟨_, _, after, finalMap, finalWorld,
          .default (lookupExpression?_sound found) sourceEval hiddenAllocated selected sourceBody,
          restore_rep related environment, finalHeaps,
          firstMaps.trans (secondMaps.trans thirdMaps), firstWorlds.trans (secondWorlds.trans thirdWorlds),
          firstFrame.trans (secondFrame.trans thirdFrame), firstMetadata.trans
            ((Dynamic.HeapMetadataExtend.of_allocation hiddenAllocated).trans thirdMetadata),
          returnTo.restore bodyState, callerProtocol.trans firstRelated
            (callerProtocol.trans selectionRelated (callerProtocol.trans bodyRelated (returnTo.related bodyState))),
          restore_parent bridge returnTo bodyState environment bodyPost⟩
      | noBranch =>
        have selectedReady := CallableIndexedOwnedMatchAdmission.after_hidden bridge
          middleState selectedState middleReady valueTyped hiddenAllocated secondFrame
        have finished : Evaluates selectedActual selectedStore ((LocalLoop.fallthrough type).rename selectedEmbedding)
            (LocalLoop.fallthroughValue type) selectedStore := .inRight (.inLeft (.inLeft .unit))
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic bodyEval.sound finished
        exact ⟨_, .fallthrough environment, hiddenHeap, selectedMap, selectedWorld,
          .noBranch (lookupExpression?_sound found) sourceEval hiddenAllocated selected,
          .fallthrough environment (Or.inl rfl), selectedRelated,
          firstMaps.trans secondMaps, firstWorlds.trans secondWorlds, firstFrame.trans secondFrame,
          firstMetadata.trans (.of_allocation hiddenAllocated), returnTo.restore selectedState,
          callerProtocol.trans firstRelated (callerProtocol.trans selectionRelated (returnTo.related selectedState)),
          restore_parent bridge returnTo selectedState environment (outcome := .fallthrough environment) selectedReady⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedMatchReflection
