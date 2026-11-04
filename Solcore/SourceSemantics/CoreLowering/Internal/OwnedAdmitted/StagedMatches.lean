import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.StagedFlows
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.StatementAdmission
import Solcore.SourceSemantics.CoreLowering.ProtectedStateMatchBodyContracts
import Solcore.SourceSemantics.CoreLowering.ReachableMatchContinuationMeaning
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.ScopedSourceInversion
import Solcore.SourceSemantics.CoreLowering.CompatibleMatchTypedLiteralSites
import Solcore.SourceSemantics.CoreLowering.GenericImperativeMatchHeadBounds

/-!
# Admitted staged profile: matches

Match heads in both directions, sequences and tree heads.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedMatchHeads
/-! Selected match children retain their actual Source grades and reached
caller states. Restoring lexical bindings preserves captured heap cells and
both semantic and staging failures. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedMatchHeads
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState
open CallableIndexedOwnedSourceAdmission (Admission)
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)
open CallableIndexedOwnedAdmittedStagedConditionalHeads (BranchPreserves BranchReflects)
open SourceCoreCompatibleDataMatches CompatibleMatchCertificates CompatibleMatchSelectionPrefix DataMatchBranchPrefix
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry} {administrative : Core.Context}
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  (condition : Location → NativeFrame → Prop)
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}
  (parent : SourceSemantics.Context) (control : ControlContext) (resolution : MatchResolution)
  (bodyCertificate : BodyCertificate) (expected : TypeSystem.Ty) (type : Ty) (budget : Nat)

def ArmPreservesBelow (outerScope : Scope) : Prop :=
  ∀ {sourceValue scope environment heap statements bindings finalScope finalEnvironment finalHeap body},
    scope.map Prod.fst = resolution.hiddenScrutinee :: outerScope.map Prod.fst →
    Dynamic.MatchCasesSelect parent sourceValue resolution.cases resolution.defaultBody (.arm statements bindings) →
    SelectedBody bodyCertificate scope environment heap type (.arm statements bindings)
      finalScope finalEnvironment finalHeap body →
    ∀ {armContext staticFinal facts},
    BindersExtend invocation.source.owner parent (bindings.map Prod.fst) armContext →
    StatementsHaveType invocation.source control armContext statements staticFinal facts →
    BranchPreserves (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions condition armContext finalScope statements expected type body budget

def ArmReflectsBelow (outerScope : Scope) : Prop :=
  ∀ {sourceValue scope environment heap statements bindings finalScope finalEnvironment finalHeap body},
    scope.map Prod.fst = resolution.hiddenScrutinee :: outerScope.map Prod.fst →
    Dynamic.MatchCasesSelect parent sourceValue resolution.cases resolution.defaultBody (.arm statements bindings) →
    SelectedBody bodyCertificate scope environment heap type (.arm statements bindings)
      finalScope finalEnvironment finalHeap body →
    ∀ {armContext staticFinal facts},
    BindersExtend invocation.source.owner parent (bindings.map Prod.fst) armContext →
    StatementsHaveType invocation.source control armContext statements staticFinal facts →
    BranchReflects (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions condition armContext finalScope statements expected type body budget

def DefaultPreservesBelow (outerScope : Scope) : Prop :=
  ∀ {sourceValue scope environment heap statements finalScope finalEnvironment finalHeap body},
    scope.map Prod.fst = resolution.hiddenScrutinee :: outerScope.map Prod.fst →
    Dynamic.MatchCasesSelect parent sourceValue resolution.cases resolution.defaultBody (.default statements) →
    SelectedBody bodyCertificate scope environment heap type (.default statements)
      finalScope finalEnvironment finalHeap body →
    ∀ {staticFinal facts}, StatementsHaveType invocation.source control parent statements staticFinal facts →
    BranchPreserves (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions condition parent finalScope statements expected type body budget

def DefaultReflectsBelow (outerScope : Scope) : Prop :=
  ∀ {sourceValue scope environment heap statements finalScope finalEnvironment finalHeap body},
    scope.map Prod.fst = resolution.hiddenScrutinee :: outerScope.map Prod.fst →
    Dynamic.MatchCasesSelect parent sourceValue resolution.cases resolution.defaultBody (.default statements) →
    SelectedBody bodyCertificate scope environment heap type (.default statements)
      finalScope finalEnvironment finalHeap body →
    ∀ {staticFinal facts}, StatementsHaveType invocation.source control parent statements staticFinal facts →
    BranchReflects (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions condition parent finalScope statements expected type body budget

theorem restore_rep {catalog projects definitions}
    {model : GenericHeap.PayloadModel catalog projects definitions}
    {mapping world mode raw type faults outcome value}
    (represented : Represents model mapping world mode raw type faults outcome value)
    (environment : Dynamic.Environment) :
    Represents model mapping world mode raw type faults (outcome.restore environment) value := by
  cases represented with
  | returned payload => exact .returned payload
  | breaking _ => exact .breaking environment
  | continuing _ => exact .continuing environment
  | fault matched => exact .fault matched
  | fallthrough _ allowed => exact .fallthrough environment allowed

private theorem value_backward {owner context target binders heap value raw}
    (extended : BindersExtend owner context binders target)
    (typed : Dynamic.ValueHasType target heap value raw) :
    Dynamic.ValueHasType context heap value raw := by
  induction extended with
  | nil => exact typed
  | cons head tail ih => exact (Dynamic.ValueHasType.iff_of_binderExtends head).mpr (ih typed)

/-- Restore only the lexical view of a selected arm. All facts concern the
same returned heap, store, mapping and authenticated function rows. -/
theorem restore_arm {source : TypedSource}
    {scope selectedScope : SourceCoreLocalCell.Scope} {canonical selectedCanonical : Environment}
    (returnTo : ProtectedStateTransition.ReturnTo callerProtocol scope canonical selectedScope selectedCanonical)
    {context armContext : SourceSemantics.Context} {binders : List TypedBinder}
    (extended : BindersExtend source.owner context binders armContext)
    {mapping world heap store expected outcome}
    (state : callerProtocol.State ⟨selectedScope, mapping, world, heap, store, selectedCanonical⟩)
    (environment : Dynamic.Environment)
    (post : Post bridge armContext expected outcome state) :
    Post bridge context expected (outcome.restore environment) (returnTo.restore state) := by
  have rows := CallableIndexedOwnedIndirectExpressionHeads.StableRows.after_administrative
    (bridge.pool state) (bridge.pool (returnTo.restore state)) post.rows (.refl _ _)
  cases outcome with
  | returned value =>
    obtain ⟨typed, admitted⟩ := CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission.at_value post
    exact ⟨rows, by intro result same; cases same; exact ⟨value_backward extended typed,
      Dynamic.BindersExtend.control_heap_backward extended admitted.heap⟩⟩
  | fault failure =>
    cases failure with
    | semantic reason => exact ⟨rows, by intro result same; cases same⟩
    | stage origin call reason => exact rows
  | fallthrough _ | breaking _ | continuing _ => exact CallableIndexedOwnedMatchPrefixAdmission.restore_arm bridge returnTo extended state post

/-- Default and empty selections restore the native frame at the original
Source context and retain the actual selected body's postcondition. -/
theorem restore_parent
    {scope selectedScope : SourceCoreLocalCell.Scope} {canonical selectedCanonical : Environment}
    (returnTo : ProtectedStateTransition.ReturnTo callerProtocol scope canonical selectedScope selectedCanonical)
    {context : SourceSemantics.Context} {mapping world heap store expected outcome}
    (state : callerProtocol.State ⟨selectedScope, mapping, world, heap, store, selectedCanonical⟩)
    (environment : Dynamic.Environment)
    (post : Post bridge context expected outcome state) :
    Post bridge context expected (outcome.restore environment) (returnTo.restore state) := by
  have rows := CallableIndexedOwnedIndirectExpressionHeads.StableRows.after_administrative
    (bridge.pool state) (bridge.pool (returnTo.restore state)) post.rows (.refl _ _)
  cases outcome with
  | returned value =>
    obtain ⟨typed, admitted⟩ := CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission.at_value post
    exact ⟨rows, by intro result same; cases same; exact ⟨typed, admitted.heap⟩⟩
  | fault failure =>
    cases failure with
    | semantic reason => exact ⟨rows, by intro result same; cases same⟩
    | stage origin call reason => exact rows
  | fallthrough _ | breaking _ | continuing _ => exact CallableIndexedOwnedMatchPrefixAdmission.restore_parent bridge returnTo state post

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedMatchHeads
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedMatchReflection
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedMatchPreservation
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedMatchSequences
/-! Match heads restore the selected lexical scope before the actual suffix.
Returning and failing bypass that suffix; a genuine default-stopping receipt
justifies the compiler's unreachable continuation. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedMatchSequences
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedAllocationCompletion
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)
universe u

open CallableIndexedOwnedAdmittedStagedConditionalHeads

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry}
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {administrative : Core.Context}
  (condition : Location → NativeFrame → Prop)
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions

/-- A selected scoped arm's numeric reflection port, closed by the surrounding
compiler-tree induction. Its postcondition is at the original outer context. -/
def MatchReflects (context : SourceSemantics.Context) (scope : SourceCoreLocalCell.Scope)
    (resolution : MatchResolution) (expected : TypeSystem.Ty) (type : Ty) (code : Expr) (budget : Nat) : Prop :=
  ∀ {size : Nat}, size ≤ budget →
  ∀ {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame} {value : Value}
    (_environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (_heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions mapping world before store)
    (_locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (_agrees : EnvironmentsAgree ξ canonical actual)
    (_actualTyped : RuntimeEnvironmentHasTypes world actual actualContext (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (_reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (_read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (_unmapped : contextLocation ∉ mapping)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (_conditioned : condition contextLocation native)
    (_admitted : Admission bridge context initial),
    EvaluationSize size actual store (code.rename ξ) value finalStore →
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Match program stages sourceSize invocation context environment before
        resolution outcome after ∧
      Represents model finalMap finalWorld false expected type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ Post bridge context expected outcome reached

/-- The corresponding Source-to-native port retains successful branch typing,
fallthrough admission, and the same final heap for every admitted caller. -/
def MatchPreserves (context : SourceSemantics.Context) (scope : SourceCoreLocalCell.Scope)
    (resolution : MatchResolution) (expected : TypeSystem.Ty) (type : Ty) (code : Expr) (budget : Nat) : Prop :=
  ∀ {size : Nat}, size ≤ budget →
  ∀ {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (_environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (_heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions mapping world before store)
    (_locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (_agrees : EnvironmentsAgree ξ canonical actual)
    (_actualTyped : RuntimeEnvironmentHasTypes world actual actualContext (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (_reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (_read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (_unmapped : contextLocation ∉ mapping)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (_conditioned : condition contextLocation native)
    (_admitted : Admission bridge context initial),
    ∀ {outcome : Staging.Recursive.BodyOutcome} {after : Dynamic.Heap},
      Staging.Recursive.Size.Match program stages size invocation context environment before
        resolution outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      Represents model finalMap finalWorld false expected type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ Post bridge context expected outcome reached


private theorem fallthrough_environment {program registry size invocation context before after resolution outer inner}
    (trace : Staging.Recursive.Size.Match program registry size invocation context outer before
      resolution (.fallthrough inner) after) : inner = outer := by
  generalize outcomeEq : (Staging.Recursive.BodyOutcome.fallthrough inner) = outcome at trace
  cases trace with
  | scrutineeFault => cases outcomeEq
  | patternFault => cases outcomeEq
  | @arm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ outcome _ _ _ _ _ _ _ =>
      cases outcome <;> simp_all [Staging.Recursive.BodyOutcome.restore]
  | @default _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ outcome _ _ _ _ _ =>
      cases outcome <;> simp_all [Staging.Recursive.BodyOutcome.restore]
  | noBranch => exact Staging.Recursive.BodyOutcome.fallthrough.inj outcomeEq

private theorem breaking_environment {program registry size invocation context before after resolution outer inner}
    (trace : Staging.Recursive.Size.Match program registry size invocation context outer before
      resolution (.breaking inner) after) : inner = outer := by
  generalize outcomeEq : (Staging.Recursive.BodyOutcome.breaking inner) = outcome at trace
  cases trace with
  | scrutineeFault => cases outcomeEq
  | patternFault => cases outcomeEq
  | @arm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ outcome _ _ _ _ _ _ _ =>
      cases outcome <;> simp_all [Staging.Recursive.BodyOutcome.restore]
  | @default _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ outcome _ _ _ _ _ =>
      cases outcome <;> simp_all [Staging.Recursive.BodyOutcome.restore]
  | noBranch => cases outcomeEq

private theorem continuing_environment {program registry size invocation context before after resolution outer inner}
    (trace : Staging.Recursive.Size.Match program registry size invocation context outer before
      resolution (.continuing inner) after) : inner = outer := by
  generalize outcomeEq : (Staging.Recursive.BodyOutcome.continuing inner) = outcome at trace
  cases trace with
  | scrutineeFault => cases outcomeEq
  | patternFault => cases outcomeEq
  | @arm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ outcome _ _ _ _ _ _ _ =>
      cases outcome <;> simp_all [Staging.Recursive.BodyOutcome.restore]
  | @default _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ outcome _ _ _ _ _ =>
      cases outcome <;> simp_all [Staging.Recursive.BodyOutcome.restore]
  | noBranch => cases outcomeEq

private theorem stopped_not_fallthrough {program registry size invocation context before after resolution environment inner id statement}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupStatement? id = some statement)
    (form : statement.form = .matchWith resolution)
    (stopped : ReachableMatchContinuations.DefaultStopped invocation.source id resolution)
    (trace : Staging.Recursive.Size.Match program registry size invocation context environment before
      resolution (.fallthrough inner) after) : False := by
  have executed := trace.sound.plain id statement (lookupStatement?_sound found) form
  cases stopped.terminates unique executed

variable {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {resolution : MatchResolution} {expected : TypeSystem.Ty} {type : Ty} {innerCode : Expr}

variable {mode : Bool} {id : StatementId} {statement : StatementNode}
  {rest : List StatementId} {body : Expr}

include bridge functions condition in
theorem reflects {budget : Nat}
    (innerCorrect : MatchReflects (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) (faults := faults) bridge functions condition context scope resolution expected type innerCode budget)
    (statementFound : invocation.source.lookupStatement? id = some statement)
    (form : statement.form = .matchWith resolution)
    (remaining : FlowReflects (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals) (stages := stages) (invocation := invocation) (faults := faults) bridge functions condition context scope mode rest expected type body budget ∨
      (NodeOccurrencesUnique invocation.source ∧ ReachableMatchContinuations.DefaultStopped invocation.source id resolution))
    {size : Nat} (within : size ≤ budget)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame} {value : Value}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (conditioned : condition contextLocation native)
    (admitted : Admission bridge context initial)
    (completed : EvaluationSize size actual store ((LocalLoop.sequence type innerCode body).rename ξ) value finalStore) :
    ∃ sourceSize finalContext outcome after finalMap finalWorld,
      Staging.Recursive.Size.StatementsIn program stages mode sourceSize invocation context environment before
        (id :: rest) finalContext outcome after ∧
      Represents model finalMap finalWorld mode expected type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ Post bridge context expected outcome reached := by
  rw [LoopRenaming.sequence] at completed
  obtain ⟨headSize, middleStore, headValue, headSmaller, headEval⟩ := completed.bind_computation
  obtain ⟨headSourceSize, headOutcome, middle, middleMap, middleWorld, headTrace, represented,
      middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, headRelated, headPost⟩ :=
    innerCorrect (Nat.le_trans (Nat.le_of_lt headSmaller) within)
      environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted headEval
  cases represented with
  | returned payload =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (LocalLoop.sequence_returned _ headEval.sound)
      exact ⟨_, context, _, middle, middleMap, middleWorld,
        .matchReturned (lookupStatement?_sound statementFound) form headTrace,
        .returned payload, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata,
        middleState, headRelated, headPost⟩
  | breaking innerEnvironment =>
      have environmentEq := breaking_environment headTrace
      subst innerEnvironment
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (LocalLoop.sequence_transfer _ headEval.sound)
      exact ⟨_, context, _, middle, middleMap, middleWorld,
        .matchBreaking (lookupStatement?_sound statementFound) form headTrace,
        .breaking environment, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata,
        middleState, headRelated, headPost⟩
  | continuing innerEnvironment =>
      have environmentEq := continuing_environment headTrace
      subst innerEnvironment
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (LocalLoop.sequence_transfer _ headEval.sound)
      exact ⟨_, context, _, middle, middleMap, middleWorld,
        .matchContinuing (lookupStatement?_sound statementFound) form headTrace,
        .continuing environment, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata,
        middleState, headRelated, headPost⟩
  | fault matched =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (LocalLoop.sequence_failure _ headEval.sound)
      exact ⟨_, context, _, middle, middleMap, middleWorld,
        .matchFault (lookupStatement?_sound statementFound) form headTrace,
        .fault matched, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata,
        middleState, headRelated, headPost⟩
  | fallthrough innerEnvironment _ =>
      have environmentEq := fallthrough_environment headTrace
      subst innerEnvironment
      rcases remaining with remaining | ⟨unique, stopped⟩
      · obtain ⟨tailSize, smaller, tailEval⟩ := completed.sequence_fallthrough headEval.sound
        obtain ⟨tailSourceSize, finalContext, outcome, after, finalMap, finalWorld, tailTrace, represented,
            finalHeaps, maps, worlds, framePreserved, metadata, reached, tailRelated, post⟩ :=
          remaining (Nat.le_trans (Nat.le_of_lt smaller) within)
            (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
            (GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix
              (GenericExpressionMeaning.agree_prefix agrees (.inLeft LocalLoop.transferType (.inLeft type .unit))) (.inLeft type .unit)) .unit)
            (.cons .unit (.cons (.inLeft .unit) (.cons (.inLeft (.inLeft .unit)) (actualTyped.weaken firstWorlds)))) reference
            ((firstFrame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
            (firstFrame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
            middleState conditioned headPost
            (by simpa only [GenericExpressionMeaning.rename_prefix] using tailEval)
        exact ⟨_, finalContext, outcome, after, finalMap, finalWorld,
          .matchFallthrough (lookupStatement?_sound statementFound) form headTrace tailTrace,
          represented, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
          firstFrame.trans framePreserved, firstMetadata.trans metadata, reached,
          callerProtocol.trans headRelated tailRelated, post⟩
      · exact False.elim (stopped_not_fallthrough unique statementFound form stopped headTrace)

include bridge functions condition in
theorem preserves {budget : Nat}
    (innerCorrect : MatchPreserves (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) (faults := faults) bridge functions condition context scope resolution expected type innerCode budget)
    (unique : NodeOccurrencesUnique invocation.source)
    (statementFound : invocation.source.lookupStatement? id = some statement)
    (form : statement.form = .matchWith resolution)
    (remaining : FlowPreserves (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions condition context scope mode rest expected type body budget ∨
      (ReachableMatchContinuations.DefaultStopped invocation.source id resolution))
    {size : Nat} (within : size ≤ budget)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (conditioned : condition contextLocation native)
    (admitted : Admission bridge context initial)
    {finalContext : SourceSemantics.Context} {outcome : Staging.Recursive.BodyOutcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.StatementsIn program stages mode size invocation context environment before
      (id :: rest) finalContext outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((LocalLoop.sequence type innerCode body).rename ξ) value finalStore ∧
      Represents model finalMap finalWorld mode expected type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ Post bridge context expected outcome reached := by
  have finish {headSize : Nat}
      {headOutcome : Staging.Recursive.BodyOutcome}
      (headTrace : Staging.Recursive.Size.Match program stages headSize invocation context
        environment before resolution headOutcome after)
      (terminal : ∀ innerEnvironment, headOutcome ≠ .fallthrough innerEnvironment)
      (bounded : headSize ≤ budget) :
      ∃ value finalStore finalMap finalWorld,
        Evaluates actual store ((LocalLoop.sequence type innerCode body).rename ξ) value finalStore ∧
        Represents model finalMap finalWorld mode expected type faults headOutcome value ∧
        CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions finalMap finalWorld after finalStore ∧
        LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
        AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
        ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
          callerProtocol.Relates initial reached ∧ Post bridge context expected headOutcome reached := by
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
        maps, worlds, preservation, metadata, reached, related, post⟩ :=
      innerCorrect bounded environments heaps locals agrees actualTyped
        reference read unmapped initial conditioned admitted headTrace
    cases represented with
    | returned payload =>
        refine ⟨_, finalStore, finalMap, finalWorld, ?_, .returned payload, finalHeaps,
          maps, worlds, preservation, metadata, reached, related, post⟩
        rw [LoopRenaming.sequence]
        exact LocalLoop.sequence_returned _ evaluated
    | breaking innerEnvironment =>
        refine ⟨_, finalStore, finalMap, finalWorld, ?_, .breaking innerEnvironment, finalHeaps,
          maps, worlds, preservation, metadata, reached, related, post⟩
        rw [LoopRenaming.sequence]
        exact LocalLoop.sequence_transfer _ evaluated
    | continuing innerEnvironment =>
        refine ⟨_, finalStore, finalMap, finalWorld, ?_, .continuing innerEnvironment, finalHeaps,
          maps, worlds, preservation, metadata, reached, related, post⟩
        rw [LoopRenaming.sequence]
        exact LocalLoop.sequence_transfer _ evaluated
    | fault matched =>
        refine ⟨_, finalStore, finalMap, finalWorld, ?_, .fault matched, finalHeaps,
          maps, worlds, preservation, metadata, reached, related, post⟩
        rw [LoopRenaming.sequence]
        exact LocalLoop.sequence_failure _ evaluated
    | fallthrough innerEnvironment _ => exact False.elim (terminal innerEnvironment rfl)
  rcases CallableIndexedOwnedPreparedStagedScopedMatchSourceInversion.match_and_tail unique statementFound form trace with
    ⟨innerSize, sourceValue, sameSize, contextEq, outcomeEq, innerTrace⟩ |
    ⟨innerSize, failure, sameSize, contextEq, outcomeEq, innerTrace⟩ |
    ⟨innerSize, sameSize, contextEq, outcomeEq, innerTrace⟩ |
    ⟨innerSize, sameSize, contextEq, outcomeEq, innerTrace⟩ |
    ⟨innerSize, tailSize, middle, sameSize, innerTrace, tailTrace⟩
  · subst outcome
    exact finish innerTrace (by intros; intro impossible; cases impossible)
      (Nat.le_trans (Nat.le_of_lt (sameSize ▸ Staging.Recursive.Size.child_lt_stepSize (by simp))) within)
  · subst outcome
    exact finish innerTrace (by intros; intro impossible; cases impossible)
      (Nat.le_trans (Nat.le_of_lt (sameSize ▸ Staging.Recursive.Size.child_lt_stepSize (by simp))) within)
  · subst outcome
    exact finish innerTrace (by intros; intro impossible; cases impossible)
      (Nat.le_trans (Nat.le_of_lt (sameSize ▸ Staging.Recursive.Size.child_lt_stepSize (by simp))) within)
  · subst outcome
    exact finish innerTrace (by intros; intro impossible; cases impossible)
      (Nat.le_trans (Nat.le_of_lt (sameSize ▸ Staging.Recursive.Size.child_lt_stepSize (by simp))) within)
  · rcases remaining with remaining | stopped
    · have headWithin : innerSize ≤ budget := Nat.le_trans (Nat.le_of_lt (by
        rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))) within
      obtain ⟨value, middleStore, middleMap, middleWorld, headEval, represented, middleHeaps,
          maps, worlds, preservation, metadata, middleState, headRelated, headPost⟩ :=
        innerCorrect headWithin environments heaps locals agrees actualTyped
          reference read unmapped initial conditioned admitted innerTrace
      cases represented with
      | fallthrough innerEnvironment _ =>
          have tailWithin : tailSize ≤ budget := Nat.le_trans (Nat.le_of_lt (by
            rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))) within
          obtain ⟨value, finalStore, finalMap, finalWorld, tailEval, represented, finalHeaps,
              lastMaps, lastWorlds, lastFrame, lastMetadata, reached, tailRelated, post⟩ :=
            remaining tailWithin (environments.extend maps worlds) middleHeaps (locals.mono metadata)
              (GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix
                (GenericExpressionMeaning.agree_prefix agrees (.inLeft LocalLoop.transferType (.inLeft type .unit))) (.inLeft type .unit)) .unit)
              (.cons .unit (.cons (.inLeft .unit) (.cons (.inLeft (.inLeft .unit)) (actualTyped.weaken worlds)))) reference
              ((preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
              (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
              middleState conditioned headPost tailTrace
          refine ⟨value, finalStore, finalMap, finalWorld, ?_, represented, finalHeaps,
            maps.trans lastMaps, worlds.trans lastWorlds, preservation.trans lastFrame,
            metadata.trans lastMetadata, reached, callerProtocol.trans headRelated tailRelated, post⟩
          rw [LoopRenaming.sequence]
          simp only [GenericExpressionMeaning.rename_prefix] at tailEval
          exact LocalLoop.sequence_fallthrough _ headEval tailEval
    · exact False.elim (stopped_not_fallthrough unique statementFound form stopped innerTrace)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedMatchSequences
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedMatchTreeHeads
/-! The actual finite compiler requests close the match head's selected branch
ports. Source contexts and numeric pattern evidence come from original pattern
typing; the genuine marked allocator supplies the actual hidden and arm cells. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedMatchTreeHeads
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState
open SourceCoreCompatibleDataMatches CompatibleMatchCertificates GenericMatchChildren
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedAdmittedStagedConditionalHeads
open CallableIndexedOwnedAdmittedStagedMatchSequences
universe u

/-- No branch execution is assumed: each authentic finite request is supplied
by the surrounding compiler-tree induction at its exact Source context. -/
theorem reflects {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
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
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
  (allocator : (((SourceCoreCompatibleDataMatches.Context.mk (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) solved sourceCells ambientDefinitions))).sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
    (layouts.allocatorAt owner active onError)))
  (definitions : layouts.definitions = ((CallableIndexedAmbient.ambientDefinitions compiled.indexed)).definitions) (registered : frame.Registered ((CallableIndexedAmbient.ambientDefinitions compiled.indexed)).definitions)
  (extension : SourceCoreRawMetadata.Extends (((SourceCoreCompatibleDataMatches.Context.mk (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) solved sourceCells ambientDefinitions))).values.registry receiving)
  {context : SourceSemantics.Context} {control : ControlContext} {scope : Scope}
  {id : StatementId} {resolution : MatchResolution} {expected : TypeSystem.Ty} {type : Ty} {reason : Word}
  {expressionCertificate : ExpressionCertificate} {requests : List Request} {code : Expr}
  (receipt : CompatibleMatchCertificates.Certificate ((SourceCoreCompatibleDataMatches.Context.mk (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) solved sourceCells ambientDefinitions)) invocation.source scope id resolution type reason
    expressionCertificate (Occurs requests) code)
  (ordinary : CompatibleMatchSelectionPrefix.Ordinary receipt)
  (signatures : context.signatures = (((SourceCoreCompatibleDataMatches.Context.mk (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) solved sourceCells ambientDefinitions))).signatures)
  (catalog : SignatureCatalogWellFormed (((SourceCoreCompatibleDataMatches.Context.mk (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) solved sourceCells ambientDefinitions))).checked.signatures)
  {node : ExpressionNode} (found : invocation.source.lookupExpression? resolution.scrutinee = some node)
  (typed : ExpressionHasType invocation.source context resolution.scrutinee node.type)
  {caseFacts : List BodyFacts}
  (casesTyped : MatchCasesHaveType invocation.source control context node.type resolution.cases caseFacts)
  (defaultTyped : ∀ statements, resolution.defaultBody = some statements →
    ∃ finalContext facts, StatementsHaveType invocation.source control context statements finalContext facts)
  (budget : Nat) (condition : Location → NativeFrame → Prop)
  (producer : ProtectedStateTransition.MarkedAllocation.Producer callerProtocol layouts frame (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions))
  (bindings : ProtectedStateTransition.Bindings callerProtocol)
  (acquire : ∀ location native, condition location native →
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary location native)

    (_children : ∀ childSize, childSize < budget →
      ReflectsAt bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions) stages invocation expressionCertificate faults childSize)
    (_bodies : ∀ request, request ∈ requests → ∀ childContext,
      ScopedContextFor invocation.source context (resolution.hiddenScrutinee :: scope.map Prod.fst)
        node.type resolution.cases resolution.defaultBody request childContext →
      ProtectedStateImperativeTypedSourceSites.Statements invocation.source childContext request.statements →
      BranchReflects (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
        (stages := stages) (invocation := invocation) (faults := faults)
        bridge functions condition childContext request.scope request.statements expected type request.code budget) :
    MatchReflects (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions condition context scope resolution expected type code budget := by
  obtain ⟨lowered, child, restricted⟩ := GenericImperativeMatch.Certificate.singleton receipt
  intro size within mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted completed
  refine CallableIndexedOwnedAdmittedStagedMatchReflection.reflects
    (expressionCertificate := GenericImperativeMatch.Singleton scope resolution.scrutinee lowered) (lowered := lowered) bridge functions onError allocator definitions registered extension
    restricted (show CompatibleMatchSelectionPrefix.Ordinary restricted from ordinary)
    (fun numeric => RequirementProves context numeric.requirement numeric.predicate) signatures (fun _ proof => proof)
    (CompatibleMatchTypedLiteralSites.Certificate.sites restricted signatures found casesTyped) catalog found typed
    (by intro other actual; exact actual.2.2) casesTyped (fun same => defaultTyped _ same) budget condition producer bindings acquire
    ?_ ?_ ?_ within environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted completed
  · intro childSize smaller actualScope actualId actualCode singleton
    rcases singleton with ⟨rfl, rfl, rfl⟩
    exact _children childSize smaller child
  · intro sourceValue hiddenScope environment heap statements bindings finalScope finalEnvironment finalHeap body sameScope selected bodySelected
      armContext staticFinal facts extended bodyTyped
    have scopeIds := selected_arm_ids bodySelected
    rw [sameScope] at scopeIds
    cases bodySelected with
    | arm binders allocated certified =>
      exact @_bodies ⟨_, statements, body⟩ certified armContext
        (ScopedContextFor.selected_arm_at ⟨_, statements, body⟩ rfl scopeIds casesTyped selected extended)
        ⟨control, staticFinal, facts, bodyTyped⟩
  · intro sourceValue hiddenScope environment heap statements finalScope finalEnvironment finalHeap body sameScope selected bodySelected
      staticFinal facts bodyTyped
    have scopeIds := (selected_default_ids bodySelected).trans sameScope
    cases bodySelected with
    | default certified =>
      exact @_bodies ⟨_, statements, body⟩ certified context (.default selected.defaultBody_eq scopeIds) ⟨control, staticFinal, facts, bodyTyped⟩

theorem preserves {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
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
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
  (allocator : (((SourceCoreCompatibleDataMatches.Context.mk (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) solved sourceCells ambientDefinitions))).sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
    (layouts.allocatorAt owner active onError)))
  (definitions : layouts.definitions = ((CallableIndexedAmbient.ambientDefinitions compiled.indexed)).definitions) (registered : frame.Registered ((CallableIndexedAmbient.ambientDefinitions compiled.indexed)).definitions)
  (extension : SourceCoreRawMetadata.Extends (((SourceCoreCompatibleDataMatches.Context.mk (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) solved sourceCells ambientDefinitions))).values.registry receiving)
  {context : SourceSemantics.Context} {control : ControlContext} {scope : Scope}
  {id : StatementId} {resolution : MatchResolution} {expected : TypeSystem.Ty} {type : Ty} {reason : Word}
  {expressionCertificate : ExpressionCertificate} {requests : List Request} {code : Expr}
  (receipt : CompatibleMatchCertificates.Certificate ((SourceCoreCompatibleDataMatches.Context.mk (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) solved sourceCells ambientDefinitions)) invocation.source scope id resolution type reason
    expressionCertificate (Occurs requests) code)
  (ordinary : CompatibleMatchSelectionPrefix.Ordinary receipt)
  (signatures : context.signatures = (((SourceCoreCompatibleDataMatches.Context.mk (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) solved sourceCells ambientDefinitions))).signatures)
  (catalog : SignatureCatalogWellFormed (((SourceCoreCompatibleDataMatches.Context.mk (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) solved sourceCells ambientDefinitions))).checked.signatures)
  {node : ExpressionNode} (found : invocation.source.lookupExpression? resolution.scrutinee = some node)
  (typed : ExpressionHasType invocation.source context resolution.scrutinee node.type)
  {caseFacts : List BodyFacts}
  (casesTyped : MatchCasesHaveType invocation.source control context node.type resolution.cases caseFacts)
  (defaultTyped : ∀ statements, resolution.defaultBody = some statements →
    ∃ finalContext facts, StatementsHaveType invocation.source control context statements finalContext facts)
  (budget : Nat) (condition : Location → NativeFrame → Prop)
  (producer : ProtectedStateTransition.MarkedAllocation.Producer callerProtocol layouts frame (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions))
  (bindings : ProtectedStateTransition.Bindings callerProtocol)
  (acquire : ∀ location native, condition location native →
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary location native)

    (_unique : NodeOccurrencesUnique invocation.source)
    (_children : ∀ childSize, childSize < budget →
      PreservesAt bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions) stages invocation expressionCertificate faults childSize)
    (_bodies : ∀ request, request ∈ requests → ∀ childContext,
      ScopedContextFor invocation.source context (resolution.hiddenScrutinee :: scope.map Prod.fst)
        node.type resolution.cases resolution.defaultBody request childContext →
      ProtectedStateImperativeTypedSourceSites.Statements invocation.source childContext request.statements →
      BranchPreserves (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
        (stages := stages) (invocation := invocation) (faults := faults)
        bridge functions condition childContext request.scope request.statements expected type request.code budget) :
    MatchPreserves (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions condition context scope resolution expected type code budget := by
  obtain ⟨lowered, child, restricted⟩ := GenericImperativeMatch.Certificate.singleton receipt
  intro size within mapping world actualContext environment canonical actual before store ξ contextLocation native
    environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted outcome after trace
  refine CallableIndexedOwnedAdmittedStagedMatchPreservation.preserves
    (expressionCertificate := GenericImperativeMatch.Singleton scope resolution.scrutinee lowered) (lowered := lowered) bridge functions onError allocator definitions registered extension
    restricted (show CompatibleMatchSelectionPrefix.Ordinary restricted from ordinary) _unique
    (fun numeric => RequirementProves context numeric.requirement numeric.predicate) signatures (fun _ proof => proof)
    (CompatibleMatchTypedLiteralSites.Certificate.sites restricted signatures found casesTyped) catalog found typed
    (by intro other actual; exact actual.2.2) casesTyped (fun same => defaultTyped _ same) budget condition producer bindings acquire
    ?_ ?_ ?_ within environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted trace
  · intro childSize smaller actualScope actualId actualCode singleton
    rcases singleton with ⟨rfl, rfl, rfl⟩
    exact _children childSize smaller child
  · intro sourceValue hiddenScope environment heap statements bindings finalScope finalEnvironment finalHeap body sameScope selected bodySelected
      armContext staticFinal facts extended bodyTyped
    have scopeIds := selected_arm_ids bodySelected
    rw [sameScope] at scopeIds
    cases bodySelected with
    | arm binders allocated certified =>
      exact @_bodies ⟨_, statements, body⟩ certified armContext
        (ScopedContextFor.selected_arm_at ⟨_, statements, body⟩ rfl scopeIds casesTyped selected extended)
        ⟨control, staticFinal, facts, bodyTyped⟩
  · intro sourceValue hiddenScope environment heap statements finalScope finalEnvironment finalHeap body sameScope selected bodySelected
      staticFinal facts bodyTyped
    have scopeIds := (selected_default_ids bodySelected).trans sameScope
    cases bodySelected with
    | default certified =>
      exact @_bodies ⟨_, statements, body⟩ certified context (.default selected.defaultBody_eq scopeIds) ⟨control, staticFinal, facts, bodyTyped⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedMatchTreeHeads
end
