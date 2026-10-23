import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationMatchHeads

/-! Forward execution of the actual match compiler head uses the reached
scrutinee state, real marked allocation prefix and selected staged body. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationMatchReflection
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open SourceCoreCompatibleDataMatches CompatibleMatchCertificates CompatibleMatchMeaning
open DataMatchBranchPrefix GenericLexicalContext CallableIndexedHistory
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)
open CallableIndexedOwnedAdmittedStagedMatchHeads (restore_rep restore_arm restore_parent)
open CellAwareInvocationMatchHeads
open CellAwareInvocationExpressionBounds
universe u
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
theorem reflects
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
    (children : ∀ child, child < budget → ReflectsAt (attachment := attachment) bridge context model index stages invocation expressionCertificate faults child)
    (armMeaning : ArmReflectsBelow (administrative := administrative) (receiving := receiving)
      (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions index producer context control resolution bodyCertificate expected type budget scope)
    (defaultMeaning : DefaultReflectsBelow (administrative := administrative) (receiving := receiving)
      (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions index producer context control resolution bodyCertificate expected type budget scope)
    {size : Nat} (within : size ≤ budget)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming}
    {value : Core.Value}
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
    (completed : EvaluationSize size actual store (code.rename ξ) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Match program stages sourceSize invocation context environment before resolution outcome after ∧
      Represents model finalMap finalWorld false expected type faults outcome value ∧
      GenericHeap.CellHeapRepresents cells finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect instances mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ Post bridge context expected outcome reached := by
  have fullCertificate := certificate
  have hiddenAbsence := CallableIndexedOwnedLocalIdentityFreshness.match_hidden_fresh physical.ownership statementFound statementForm
  cases certificate with
  | matchWith readStatement allowed form requirements hiddenOwned hiddenFresh scrutineeOwned scrutineeFound projection
      expression loweredSameType arms fallback branches hiddenCompiled =>
    obtain ⟨childNode, child, childSize, input, middleStore, childFound, childCertificate, childSmaller, childCompleted⟩ :=
      RecursiveNamedMatchSourceBounds.Certificate.initial_evaluation_sized fullCertificate completed
    have childEq := uniqueExpression _ childCertificate
    subst child
    have nodeEq := Option.some.inj (compilerFound.symm.trans childFound)
    subst childNode
    obtain ⟨sourceSize, sourceOutcome, middleHeap, middleMap, middleWorld, sourceEval, represented,
      middleRelated, firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect, middleState, firstRelated, firstPost⟩ :=
      children childSize (Nat.lt_of_lt_of_le childSmaller within) childCertificate found typed
        environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation childCompleted
    cases represented with
    | fault matched =>
      have failed := CompatibleMatchScrutineeReflection.Certificate.failure_preserves fullCertificate uniqueExpression childCompleted.sound
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound failed
      exact ⟨_, _, middleHeap, middleMap, middleWorld, .scrutineeFault sourceEval, .fault matched,
        middleRelated, firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect, middleState, firstRelated, firstPost.at_fault_type⟩
    | value payload =>
      obtain ⟨valueTyped, middleReady⟩ := firstPost.at_value
      let middlePhysical := physical.transport firstEffect firstFrame
      have reference := physical.reference
      have read := middlePhysical.read
      have unmapped := middlePhysical.unmapped
      obtain ⟨hiddenHeap, location, selection, finalScope, selectedEnvironment, selectedHeap, selectedCanonical,
        selectedActual, selectedStore, selectedMap, selectedWorld, selectedEmbedding, selectedContext, body,
        hiddenAllocated, selected, selectedBody, selectedEnv, selectedRelated, secondMaps, secondWorlds, secondFrame,
        selectedLayout, selectedTyped, selectedReference, selectedRead, selectedUnmapped, spine, agreement, selectedState, selectionRelated, ⟨returnTo⟩, secondEffect⟩ :=
        CellAwareMatchSelectedPrefix.success_with_effect fullCertificate ordinary onError allocator literals signatures numericRequirements sites
          catalogValid instances GeneralizedLocalDescriptorHeap.ordinary_cells callerProtocol producer stateBindings definitions registered extended compilerFound uniqueExpression (sameType.symm ▸ payload) (environments.extend firstMaps firstWorlds)
          middleRelated agrees (actualTyped.weaken firstWorlds) reference read unmapped childCompleted.sound middleState ready
      rw [sameType] at hiddenAllocated
      obtain ⟨bodySize, bodySmaller, bodyEval⟩ := agreement.remaining completed
      cases selectedBody with
      | @arm statements bindings compiledBindings finalEnvironment finalHeap body binders allocated certified =>
        obtain ⟨armContext, staticFinal, facts, extendedContext, bodyTyped, _⟩ :=
          DataMatchSourceScopes.MatchCasesSelect.arm_scope casesTyped selected
        have selectedReady := (CallableIndexedOwnedMatchPrefixAdmission.after_arm_prefix bridge
          middleState selectedState middleReady valueTyped hiddenAllocated casesTyped selected extendedContext allocated secondFrame).1
        have selectedMembers := selected_members statementFound statementForm (sourceEq ▸ casesTyped) selected
        let selectedPhysical := CellAwareInvocationMatchPhysical.arm middlePhysical hiddenAbsence
          (by simpa only [binders] using selectedMembers) (by simpa only [binders, sourceEq] using extendedContext)
          (by simpa only [binders] using allocated) secondEffect selectedReference selectedRead selectedUnmapped
        have selectedAuthority : CellAwareScopeAuthority.At instances index.owner index.active selectedMap selectedWorld selectedHeap selectedStore selectedEnvironment :=
          CellAwareInvocationMatchPhysical.allocated_authority (index := index) allocated
            (authority.transport (firstEffect.trans secondEffect))
        have fields := Dynamic.BindersExtend.runtimeContextFields extendedContext
        obtain ⟨bodySourceSize, finalContext, outcome, after, finalMap, finalWorld, sourceBody, related,
          finalHeaps, thirdMaps, thirdWorlds, thirdFrame, thirdMetadata, thirdEffect, bodyState, bodyRelated, bodyPost⟩ :=
          armMeaning rfl selected (.arm binders allocated certified) extendedContext bodyTyped _
            (Nat.le_of_lt (Nat.lt_of_lt_of_le bodySmaller within)) selectedEnv selectedRelated
            (binders_agree extendedContext (arm_monomorphic casesTyped selected)
              (locals.mono (firstMetadata.trans (.of_allocation hiddenAllocated))) allocated)
            selectedLayout selectedTyped (runtime.transport fields) (fields.covers covers) (fields.solvedRequirements.trans sameLedger)
            (by simpa only [sourceEq] using (show ProtectedStateImperativeTypedSourceSites.Statements invocation.source armContext statements from ⟨control, staticFinal, facts, bodyTyped⟩))
            selectedState selectedReady selectedAuthority selectedPhysical owner sameLocation ready bodyEval
        exact ⟨_, _, after, finalMap, finalWorld,
          .arm (lookupExpression?_sound found) sourceEval hiddenAllocated selected extendedContext allocated sourceBody,
          restore_rep related environment, finalHeaps,
          firstMaps.trans (secondMaps.trans thirdMaps), firstWorlds.trans (secondWorlds.trans thirdWorlds),
          firstFrame.trans (secondFrame.trans thirdFrame), firstMetadata.trans
            ((Dynamic.HeapMetadataExtend.of_allocation hiddenAllocated).trans ((binders_metadata allocated).trans thirdMetadata)),
          firstEffect.trans (secondEffect.trans thirdEffect),
          returnTo.restore bodyState, callerProtocol.trans firstRelated
            (callerProtocol.trans selectionRelated (callerProtocol.trans bodyRelated (returnTo.related bodyState))),
          restore_arm bridge returnTo extendedContext bodyState environment bodyPost⟩
      | @default statements body certified =>
        have selectedReady := CallableIndexedOwnedMatchAdmission.after_hidden bridge
          middleState selectedState middleReady valueTyped hiddenAllocated secondFrame
        obtain ⟨staticFinal, facts, bodyTyped⟩ := defaultTyped selected.defaultBody_eq
        let selectedPhysical := CellAwareInvocationMatchPhysical.parent middlePhysical hiddenAbsence secondEffect selectedReference selectedRead selectedUnmapped
        have selectedAuthority : CellAwareScopeAuthority.At instances index.owner index.active selectedMap selectedWorld hiddenHeap selectedStore environment :=
          authority.transport (firstEffect.trans secondEffect)
        obtain ⟨bodySourceSize, finalContext, outcome, after, finalMap, finalWorld, sourceBody, related,
          finalHeaps, thirdMaps, thirdWorlds, thirdFrame, thirdMetadata, thirdEffect, bodyState, bodyRelated, bodyPost⟩ :=
          defaultMeaning (environment := environment) (heap := hiddenHeap) rfl selected (.default certified) bodyTyped _
            (Nat.le_of_lt (Nat.lt_of_lt_of_le bodySmaller within)) selectedEnv selectedRelated
            (locals.mono (firstMetadata.trans (.of_allocation hiddenAllocated))) selectedLayout selectedTyped
            runtime covers sameLedger
            (by simpa only [sourceEq] using (show ProtectedStateImperativeTypedSourceSites.Statements invocation.source context statements from ⟨control, staticFinal, facts, bodyTyped⟩))
            selectedState selectedReady selectedAuthority selectedPhysical owner sameLocation ready bodyEval
        exact ⟨_, _, after, finalMap, finalWorld,
          .default (lookupExpression?_sound found) sourceEval hiddenAllocated selected sourceBody,
          restore_rep related environment, finalHeaps,
          firstMaps.trans (secondMaps.trans thirdMaps), firstWorlds.trans (secondWorlds.trans thirdWorlds),
          firstFrame.trans (secondFrame.trans thirdFrame), firstMetadata.trans
            ((Dynamic.HeapMetadataExtend.of_allocation hiddenAllocated).trans thirdMetadata),
          firstEffect.trans (secondEffect.trans thirdEffect),
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
          firstMetadata.trans (.of_allocation hiddenAllocated), firstEffect.trans secondEffect, returnTo.restore selectedState,
          callerProtocol.trans firstRelated (callerProtocol.trans selectionRelated (returnTo.related selectedState)),
          restore_parent bridge returnTo selectedState environment (outcome := .fallthrough environment) selectedReady⟩


end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationMatchReflection
