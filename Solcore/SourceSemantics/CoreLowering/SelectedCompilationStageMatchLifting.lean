import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedMatchHeads
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageMatchSourceInversion

/-! Ordinary match traces lift through the actual allocation prefix. The
selected branch receives its captured cells at the genuine reached state. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageMatchLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open SourceCoreCompatibleDataMatches CompatibleMatchCertificates CompatibleMatchMeaning
open DataMatchBranchPrefix GenericLexicalContext CallableIndexedHistory
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)
open CallableIndexedOwnedAdmittedStagedMatchHeads
open SelectedCompilationStageScopedLiftBounds SelectedCompilationStageBodyLiftBounds
open SelectedCompilationStageLiftBounds (LiftsAt)
open SelectedCompilationStageMatchSourceInversion (PlainMatch)
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


section Ports
variable {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  (condition : Location → NativeFrame → Prop)
  (parent : SourceSemantics.Context) (control : ControlContext) (resolution : MatchResolution)
  (bodyCertificate : BodyCertificate) (type : Ty) (budget : Nat)
def ArmLiftsBelow (outerScope : Scope) : Prop :=
  ∀ {sourceValue scope environment heap statements bindings finalScope finalEnvironment finalHeap body},
    scope.map Prod.fst = resolution.hiddenScrutinee :: outerScope.map Prod.fst →
    Dynamic.MatchCasesSelect parent sourceValue resolution.cases resolution.defaultBody (.arm statements bindings) →
    SelectedBody bodyCertificate scope environment heap type (.arm statements bindings)
      finalScope finalEnvironment finalHeap body →
    ∀ {armContext staticFinal facts},
    BindersExtend invocation.source.owner parent (bindings.map Prod.fst) armContext →
    StatementsHaveType invocation.source control armContext statements staticFinal facts →
    FlowLifts (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation)
      bridge functions condition armContext finalScope false statements budget

def DefaultLiftsBelow (outerScope : Scope) : Prop :=
  ∀ {sourceValue scope environment heap statements finalScope finalEnvironment finalHeap body},
    scope.map Prod.fst = resolution.hiddenScrutinee :: outerScope.map Prod.fst →
    Dynamic.MatchCasesSelect parent sourceValue resolution.cases resolution.defaultBody (.default statements) →
    SelectedBody bodyCertificate scope environment heap type (.default statements)
      finalScope finalEnvironment finalHeap body →
    ∀ {staticFinal facts}, StatementsHaveType invocation.source control parent statements staticFinal facts →
    FlowLifts (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation)
      bridge functions condition parent finalScope false statements budget

end Ports

/-- Restoring lexical scope retains the exact ordinary completion or the
same authentic earlier stage failure. -/
theorem restore_adapted {plainFinal finalContext outer : SourceSemantics.Context}
    {plain : Dynamic.ControlOutcome} {staged : Staging.Recursive.BodyOutcome}
    {after reached : Dynamic.Heap} (environment : Dynamic.Environment)
    (adapted : BodyAdapted plainFinal plain after finalContext staged reached) :
    BodyAdapted outer (Dynamic.restoreControl environment plain) after outer (staged.restore environment) reached := by
  cases adapted with
  | completed matched => cases matched with
    | returned value => exact .completed (.returned value)
    | fallthrough inner => exact .completed (.fallthrough environment)
    | fault reason => exact .completed (.fault reason)
  | rejected origin call reason finalContext reached => exact .rejected origin call reason outer reached

def MatchLift (program : Program) (stages : Staging.Recursive.Registry)
    (invocation : Staging.Recursive.Scope) (context : SourceSemantics.Context)
    (environment : Dynamic.Environment) (before : Dynamic.Heap) (resolution : MatchResolution)
    (plain : Dynamic.ControlOutcome) (after : Dynamic.Heap) : Prop :=
  ∃ staged reached, Staging.Recursive.Match program stages invocation context environment before resolution staged reached ∧
    BodyAdapted context plain after context staged reached

include bridge functions in
theorem lifts
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (allocator : (compilation).sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (definitions : layouts.definitions = (ambient).definitions) (registered : frame.Registered (ambient).definitions)
    (extended : SourceCoreRawMetadata.Extends (compilation).values.registry receiving)
    {context : SourceSemantics.Context} {control : ControlContext} {scope : Scope}
    {id : StatementId} {resolution : MatchResolution} {type : Ty} {reason : Word}
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
    (children : ∀ child, child < budget → LiftsAt bridge context model stages invocation expressionCertificate child)
    (preservation : ∀ child, PreservesAt bridge context model stages invocation expressionCertificate faults child)
    (armMeaning : ArmLiftsBelow (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      bridge functions condition context control resolution bodyCertificate type budget scope)
    (defaultMeaning : DefaultLiftsBelow (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      bridge functions condition context control resolution bodyCertificate type budget scope)
    {size : Nat} (within : size ≤ budget)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    {outcome : Dynamic.ControlOutcome}
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
    (trace : PlainMatch program size invocation context environment before resolution outcome after) :
    MatchLift program stages invocation context environment before resolution outcome after := by
  have expression : expressionCertificate scope resolution.scrutinee lowered := by
    cases certificate with
    | matchWith _ _ _ _ _ _ _ _ _ certified => exact (uniqueExpression _ certified) ▸ certified
  cases trace with
  | scrutineeFault failed =>
    obtain ⟨staged, reached, lifted, adapted⟩ := children _
      (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) within)
      expression found typed environments heaps locals agrees actualTyped initial admitted (.fault failed)
    cases adapted with
    | completed => exact ⟨_, _, .scrutineeFault lifted, .completed (.fault _)⟩
    | rejected origin call reason reached =>
      exact ⟨_, _, .scrutineeFault lifted, .rejected origin call reason context reached⟩
  | patternFault contains evaluated allocated failed =>
    obtain ⟨staged, reached, lifted, adapted⟩ := children _
      (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) within)
      expression found typed environments heaps locals agrees actualTyped initial admitted (.value evaluated)
    cases adapted with
    | completed => exact ⟨_, _, .patternFault contains lifted allocated failed, .completed (.fault _)⟩
    | rejected origin call reason reached =>
      exact ⟨_, _, .scrutineeFault lifted, .rejected origin call reason context reached⟩
  | @arm exprSize bodySize _ _ armContext innerFinal _ armEnvironment _ middle hidden bound _ _ sourceNode sourceValue
      location statements bindings innerOutcome contains sourceEval sourceHidden selected sourceExtended sourceAllocated sourceBody =>
    have exprSmaller : exprSize < budget := Nat.lt_of_lt_of_le
      (SourceExecutionSize.child_lt_stepSize (by simp)) within
    have bodyWithin : bodySize ≤ budget := Nat.le_trans
      (Nat.le_of_lt (SourceExecutionSize.child_lt_stepSize (by simp))) within
    have nodeEq : sourceNode = node := Option.some.inj
      ((lookupExpression?_complete unique contains).symm.trans found)
    subst sourceNode
    obtain ⟨staged, reached, lifted, adapted⟩ := children _ exprSmaller
      expression found typed environments heaps locals agrees actualTyped initial admitted (.value sourceEval)
    cases adapted with
    | rejected origin call reason reached =>
      exact ⟨_, _, .scrutineeFault lifted, .rejected origin call reason context reached⟩
    | completed =>
      obtain ⟨stagedSize, measured⟩ := Staging.Recursive.Size.Expression.of_trace lifted
      obtain ⟨value, middleStore, middleMap, middleWorld, coreEval, represented, middleRelated,
        firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, firstRelated, firstPost⟩ :=
        preservation stagedSize expression found typed environments heaps locals agrees actualTyped initial admitted measured
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
          obtain ⟨finalContext, result, finalHeap, bodyTrace, bodyAdapted⟩ :=
            armMeaning rfl selected (.arm binders allocated bodyCertified) sourceExtended typed bodyWithin selectedEnv selectedRelated
              (binders_agree sourceExtended (arm_monomorphic casesTyped selected)
                (locals.mono (firstMetadata.trans (.of_allocation sourceHidden))) sourceAllocated)
              selectedLayout selectedTyped selectedReference selectedRead selectedUnmapped selectedState conditioned selectedReady sourceBody
          exact ⟨_, finalHeap, .arm contains lifted sourceHidden selected sourceExtended sourceAllocated bodyTrace,
            restore_adapted environment bodyAdapted⟩
  | @default exprSize bodySize _ _ innerFinal _ _ middle hidden _ _ sourceNode sourceValue location statements innerOutcome
      contains sourceEval sourceHidden selected sourceBody =>
    have exprSmaller : exprSize < budget := Nat.lt_of_lt_of_le
      (SourceExecutionSize.child_lt_stepSize (by simp)) within
    have bodyWithin : bodySize ≤ budget := Nat.le_trans
      (Nat.le_of_lt (SourceExecutionSize.child_lt_stepSize (by simp))) within
    have nodeEq : sourceNode = node := Option.some.inj
      ((lookupExpression?_complete unique contains).symm.trans found)
    subst sourceNode
    obtain ⟨staged, reached, lifted, adapted⟩ := children _ exprSmaller
      expression found typed environments heaps locals agrees actualTyped initial admitted (.value sourceEval)
    cases adapted with
    | rejected origin call reason reached =>
      exact ⟨_, _, .scrutineeFault lifted, .rejected origin call reason context reached⟩
    | completed =>
      obtain ⟨stagedSize, measured⟩ := Staging.Recursive.Size.Expression.of_trace lifted
      obtain ⟨value, middleStore, middleMap, middleWorld, coreEval, represented, middleRelated,
        firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, firstRelated, firstPost⟩ :=
        preservation stagedSize expression found typed environments heaps locals agrees actualTyped initial admitted measured
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
          obtain ⟨finalContext, result, finalHeap, bodyTrace, bodyAdapted⟩ :=
            defaultMeaning (environment := environment) (heap := hidden) rfl selected (.default bodyCertified) typed bodyWithin selectedEnv selectedRelated
              (locals.mono (firstMetadata.trans (.of_allocation sourceHidden))) selectedLayout selectedTyped selectedReference selectedRead selectedUnmapped selectedState conditioned selectedReady sourceBody
          exact ⟨_, finalHeap, .default contains lifted sourceHidden selected bodyTrace,
            restore_adapted environment bodyAdapted⟩
  | noBranch contains evaluated allocated selected =>
    obtain ⟨staged, reached, lifted, adapted⟩ := children _
      (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) within)
      expression found typed environments heaps locals agrees actualTyped initial admitted (.value evaluated)
    cases adapted with
    | completed => exact ⟨_, _, .noBranch contains lifted allocated selected, .completed (.fallthrough _)⟩
    | rejected origin call reason reached =>
      exact ⟨_, _, .scrutineeFault lifted, .rejected origin call reason context reached⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageMatchLifting
