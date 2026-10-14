import Solcore.SourceSemantics.CoreLowering.ProtectedLoopStatementControlShape
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageLexicalTreeLifting
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageAssignmentLifting
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageWhileSequenceLifting
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageMatchTreeHeads
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForSequenceLifting
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForInitialLifting
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedScopedImperativePreservation

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageImperativeLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedAllocationCompletion
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedPreparedStagedLexicalTree (TypedCertificate)
open CallableIndexedOwnedPreparedStagedBranchingTree (Shape PositionShape)
open CallableIndexedOwnedAdmittedStagedImperativePositions (PositionTyping InitializerTyping)
open GenericImperativeMatch (Tree)
open TypedLexicalControl (sequence_rename)
universe u

open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post restore_post)
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (bindings : ProtectedStateTransition.Bindings callerProtocol)
  (transport : ProtectedStateTransition.AdministrativeTransport callerProtocol)

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry receiving)
  (definitions : layouts.definitions = (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
  (registered : frame.Registered (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
  (producer : ProtectedStateTransition.MarkedAllocation.Producer callerProtocol layouts frame
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions))
  (condition : Location → NativeFrame → Prop)
  (acquire : ∀ location native, condition location native →
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary location native)
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {faults : RecursiveStageMeaning.FaultRep}

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions

open SelectedCompilationStageScopedLiftBounds
open SelectedCompilationStageLiftBounds (LiftsAt)
open SelectedCompilationStageForInitialBounds (InitializersLifts)

def PositionLifts {administrative : Core.Context} (context : SourceSemantics.Context)
    (scope : SourceCoreLocalCell.Scope) (position : GenericImperativeMatch.Position) (budget : Nat) : Prop :=
  match position with
  | .statements mode statements => FlowLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      bridge functions condition context scope mode statements budget
  | .initializers items test post statements => InitializersLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      (context := context) (scope := scope) bridge functions condition items test post statements budget

include bridge bindings definitions registered producer acquire transport extension in
theorem preserves_position
    (preservation : ∀ context size, PreservesAt bridge context model stages invocation (certificates context) faults size)
    (unique : NodeOccurrencesUnique invocation.source)
    {expressionSyntax : ExpressionId → Prop} {administrative : Core.Context}
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {position : GenericImperativeMatch.Position} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError (.initial compiled.compatible.checked)
      invocation.source expressionSyntax (TypedCertificate invocation.source certificates)
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions administrative context scope position expected type code)
    {diagnosticPolicy : AssignmentDiagnosticPolicy} {catalogRegistry : SourceCoreRawMetadata.Registry} {catalogFaults : FunctionCalls.FaultRep}
    (catalogSites : Tree.CatalogSites diagnosticPolicy catalogRegistry catalogFaults tree)
    (semantic : ∀ reason token, catalogFaults reason token → faults (.semantic reason) token)
    (shape : PositionShape invocation.source position)
    (sourceTyped : PositionTyping invocation.source context position)
    (projection : compiled.compatible.checked.catalog.project expected = .ok type) :
    ∀ budget, CallableIndexedOwnedAdmittedStagedImperativePositions.Preserves
      (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions condition context scope position expected type code budget := by
  intro budget
  exact CallableIndexedOwnedAdmittedStagedScopedImperativePreservation.preserves_position (semantic := semantic) bridge bindings transport
    functions extension definitions registered producer condition acquire (fun context size _ => preservation context size)
    unique tree catalogSites shape sourceTyped projection

include bridge bindings definitions registered producer acquire transport extension in
theorem lifts_position {budget : Nat}
    (children : ∀ context childSize, childSize < budget → LiftsAt bridge context model stages invocation (certificates context) childSize)
    (preservation : ∀ context size, PreservesAt bridge context model stages invocation (certificates context) faults size)
    (unique : NodeOccurrencesUnique invocation.source)
    {expressionSyntax : ExpressionId → Prop} {administrative : Core.Context}
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {position : GenericImperativeMatch.Position} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError (.initial compiled.compatible.checked)
      invocation.source expressionSyntax (TypedCertificate invocation.source certificates)
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions administrative context scope position expected type code)
    {diagnosticPolicy : AssignmentDiagnosticPolicy} {catalogRegistry : SourceCoreRawMetadata.Registry} {catalogFaults : FunctionCalls.FaultRep}
    (catalogSites : Tree.CatalogSites diagnosticPolicy catalogRegistry catalogFaults tree)
    (semantic : ∀ reason token, catalogFaults reason token → faults (.semantic reason) token)
    (shape : PositionShape invocation.source position)
    (sourceTyped : PositionTyping invocation.source context position)
    (projection : compiled.compatible.checked.catalog.project expected = .ok type) :
    PositionLifts (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) bridge functions condition context scope position budget := by
  have typedChildren (context : SourceSemantics.Context) (size : Nat) (smaller : size < budget) :
      LiftsAt bridge context model stages invocation (TypedCertificate invocation.source certificates context) size := by
    intro scope id lowered generated node found typed
    obtain ⟨actualNode, nodeFound, nodeTyped, certified⟩ := generated
    exact children context size smaller certified found typed
  have typedPreservation (context : SourceSemantics.Context) (size : Nat) :
      PreservesAt bridge context model stages invocation (TypedCertificate invocation.source certificates context) faults size := by
    intro scope id lowered generated node found typed
    obtain ⟨actualNode, nodeFound, nodeTyped, certified⟩ := generated
    exact preservation context size certified found typed
  revert shape sourceTyped projection
  induction catalogSites with
  | @body context scope mode statements expected type code syntaxTree body =>
    intro shape sourceTyped projection size within mapping world actualContext environment canonical actual before store ξ
      contextLocation native environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted
      finalContext outcome after trace
    exact SelectedCompilationStageLexicalTreeLifting.lifts bridge bindings functions definitions registered producer.toOrdinary
      condition acquire children preservation unique body shape projection within environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted trace
  | @uninitialized context nextContext scope mode id node binder rest expected type body payload found form mono extended ordinary projected allocation annotation same tail remainingErrors ih =>
    intro shape sourceTyped projection size within mapping world actualContext environment canonical actual before store ξ
      contextLocation native environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted
      finalContext outcome after trace
    exact SelectedCompilationStageLexicalLifting.absent bridge functions definitions registered producer.toOrdinary condition acquire
      unique found form mono extended ordinary projected allocation annotation same
      (ih (shape.tail_of_let found form) (ProtectedStateImperativeStatementSuffixTyping.let_decl unique sourceTyped found form extended) projection) within environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted trace
  | @initialized context nextContext scope mode id node binder initializer initializerNode lowered body rest expected type found form mono extended ordinary initialFound sourceType child allocation annotation same remaining remainingErrors ih =>
    intro shape sourceTyped projection size within mapping world actualContext environment canonical actual before store ξ
      contextLocation native environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted
      finalContext outcome after trace
    obtain ⟨typedNode, typedFound, typed, certified⟩ := child
    cases Option.some.inj (initialFound.symm.trans typedFound)
    exact SelectedCompilationStageLexicalLifting.initialized bridge functions definitions registered producer.toOrdinary condition acquire
      unique found form mono extended ordinary initialFound sourceType typed certified allocation annotation same
      (children _) (preservation _)
      (ih (shape.tail_of_let found form) (ProtectedStateImperativeStatementSuffixTyping.let_decl unique sourceTyped found form extended) projection) within environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted trace
  | @discard context scope mode id node expression expressionNode semi rest expected lowered type body found form guard expressionFound child remaining remainingErrors ih =>
    intro shape sourceTyped projection size within mapping world actualContext environment canonical actual before store ξ
      contextLocation native environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted
      finalContext outcome after trace
    obtain ⟨continuing, tailShape⟩ := shape.discard_tail found form guard
    obtain ⟨typedNode, typedFound, typed, certified⟩ := child
    cases Option.some.inj (expressionFound.symm.trans typedFound)
    exact SelectedCompilationStageDiscardLifting.lifts bridge functions condition unique found form continuing expressionFound typed certified
      (children _) (preservation _) (ih tailShape (ProtectedStateImperativeStatementSuffixTyping.discard unique sourceTyped found form) projection) within environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted trace
  | @assign context scope mode id node assignment operator rhs rest expected type body found form head remaining remainingErrors headErrors ih =>
    intro shape sourceTyped projection size within mapping world actualContext environment canonical actual before store ξ
      contextLocation native environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted
      finalContext outcome after trace
    obtain ⟨_profile, bare, tailShape⟩ := shape.assign_tail found form
    have assignmentTyped := ProtectedStateImperativeTypedSourceSites.assignment unique
      (ProtectedStateImperativeTypedSourceSites.head sourceTyped) found form
    exact SelectedCompilationStageAssignmentLifting.lifts bridge functions transport extension condition unique found form head bare assignmentTyped
      (typedChildren context) (typedPreservation context)
      (ih tailShape (ProtectedStateImperativeStatementSuffixTyping.assignment unique sourceTyped found form) projection) within environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted trace
  | @block context scope mode id node statements rest expected type innerCode body found form inner remaining innerErrors remainingErrors innerIH remainingIH =>
    intro shape sourceTyped projection size within mapping world actualContext environment canonical actual before store ξ
      contextLocation native environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted
      finalContext outcome after trace
    obtain ⟨innerShape, restShape⟩ := shape.block_children found form
    have innerTyped := CallableIndexedOwnedPreparedStagedScopedBlockSourceTyping.inner unique sourceTyped found form
    have restTyped := CallableIndexedOwnedPreparedStagedScopedBlockSourceTyping.suffix unique sourceTyped found form
    exact SelectedCompilationStageBlockLifting.lifts bridge functions condition unique found form
      (innerIH innerShape innerTyped projection)
      (preserves_position (semantic := semantic) bridge bindings transport functions extension definitions registered producer condition acquire
        preservation unique inner innerErrors innerShape innerTyped projection)
      (.inl (remainingIH restShape restTyped projection)) within environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted trace
  | @ifThen context scope mode id node conditionId conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body found form conditionFound conditionType conditionTree thenTree elseTree remaining thenTreeErrors elseTreeErrors remainingErrors thenIH elseIH remainingIH =>
    intro shape sourceTyped projection size within mapping world actualContext environment canonical actual before store ξ
      contextLocation native environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted
      finalContext outcome after trace
    obtain ⟨leftShape, rightShape, restShape⟩ := shape.branches found form
    obtain ⟨typedNode, typedFound, typed, certified⟩ := conditionTree
    cases Option.some.inj (conditionFound.symm.trans typedFound)
    have leftTyped := ProtectedStateImperativeTypedSourceSites.branch_typed true unique
      (ProtectedStateImperativeTypedSourceSites.head sourceTyped) found form
    have rightTyped := ProtectedStateImperativeTypedSourceSites.branch_typed false unique
      (ProtectedStateImperativeTypedSourceSites.head sourceTyped) found form
    refine SelectedCompilationStageConditionalLifting.lifts (expected := expected) (type := type)
      (branchCode := fun truth => if truth then thenCode else elseCode) bridge functions condition unique found form
      conditionFound typed certified (children _) (preservation _) ?_ ?_ ?_ within environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted trace
    · intro truth; cases truth
      · exact elseIH rightShape rightTyped projection
      · exact thenIH leftShape leftTyped projection
    · intro truth; cases truth
      · exact preserves_position (semantic := semantic) bridge bindings transport functions extension definitions registered producer condition acquire preservation unique elseTree elseTreeErrors rightShape rightTyped projection
      · exact preserves_position (semantic := semantic) bridge bindings transport functions extension definitions registered producer condition acquire preservation unique thenTree thenTreeErrors leftShape leftTyped projection
    · exact .inl (remainingIH restShape (CallableIndexedOwnedPreparedStagedScopedBranchSourceTyping.suffix unique sourceTyped found form) projection)
  | @terminalBlock context scope mode id node statements rest expected type innerCode suffix exactUnique found form inner stops issued innerErrors ih =>
    intro shape sourceTyped projection size within mapping world actualContext environment canonical actual before store ξ
      contextLocation native environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted
      finalContext outcome after trace
    obtain ⟨innerShape, _restShape⟩ := shape.block_children found form
    have innerTyped := CallableIndexedOwnedPreparedStagedScopedBlockSourceTyping.inner unique sourceTyped found form
    exact SelectedCompilationStageBlockLifting.lifts bridge functions condition unique found form
      (ih innerShape innerTyped projection)
      (preserves_position (semantic := semantic) bridge bindings transport functions extension definitions registered producer condition acquire preservation unique inner innerErrors innerShape innerTyped projection)
      (.inr stops) within environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted trace
  | @terminalIf context scope mode id node conditionId conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode suffix exactUnique found form conditionFound conditionType conditionTree thenTree elseTree thenStops elseStops issued thenErrors elseErrors thenIH elseIH =>
    intro shape sourceTyped projection size within mapping world actualContext environment canonical actual before store ξ
      contextLocation native environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted
      finalContext outcome after trace
    obtain ⟨leftShape, rightShape, _restShape⟩ := shape.branches found form
    obtain ⟨typedNode, typedFound, typed, certified⟩ := conditionTree
    cases Option.some.inj (conditionFound.symm.trans typedFound)
    have leftTyped := ProtectedStateImperativeTypedSourceSites.branch_typed true unique (ProtectedStateImperativeTypedSourceSites.head sourceTyped) found form
    have rightTyped := ProtectedStateImperativeTypedSourceSites.branch_typed false unique (ProtectedStateImperativeTypedSourceSites.head sourceTyped) found form
    refine SelectedCompilationStageConditionalLifting.lifts (expected := expected) (type := type)
      (branchCode := fun truth => if truth then thenCode else elseCode) bridge functions condition unique found form
      conditionFound typed certified (children _) (preservation _) ?_ ?_ ?_ within environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted trace
    · intro truth; cases truth
      · exact elseIH rightShape rightTyped projection
      · exact thenIH leftShape leftTyped projection
    · intro truth; cases truth
      · exact preserves_position (semantic := semantic) bridge bindings transport functions extension definitions registered producer condition acquire preservation unique elseTree elseErrors rightShape rightTyped projection
      · exact preserves_position (semantic := semantic) bridge bindings transport functions extension definitions registered producer condition acquire preservation unique thenTree thenErrors leftShape leftTyped projection
    · exact .inr ⟨thenStops, elseStops⟩
  | @whileLoop context scope mode id node conditionId conditionNode statements rest expected type conditionCode loopCode body selfReason found form conditionFound conditionType conditionTree loopTree nativeTyped remaining loopBodyErrors remainingErrors loopIH remainingIH =>
    intro shape sourceTyped projection size within mapping world actualContext environment canonical actual before store ξ
      contextLocation native environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted
      finalContext outcome after trace
    obtain ⟨loopShape, restShape⟩ := shape.loop found form
    obtain ⟨typedNode, typedFound, typed, certified⟩ := conditionTree
    cases Option.some.inj (conditionFound.symm.trans typedFound)
    have loopTyped := (CallableIndexedOwnedPreparedStagedScopedWhileSourceTyping.children unique sourceTyped found form).2
    have restTyped := CallableIndexedOwnedPreparedStagedScopedWhileSourceTyping.suffix unique sourceTyped found form
    exact SelectedCompilationStageWhileSequenceLifting.lifts bridge functions condition transport
      (children _) (preservation _) conditionFound conditionType typed certified nativeTyped
      (loopIH loopShape loopTyped projection)
      (preserves_position (semantic := semantic) bridge bindings transport functions extension definitions registered producer condition acquire preservation unique loopTree loopBodyErrors loopShape loopTyped projection)
      unique found form (remainingIH restShape restTyped projection) within environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted trace
  | @matchWith context scope mode id node resolution scrutineeNode rest expected type matched body selfReason control caseFacts found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary matchChildren remaining catalog patternContext childErrors remainingErrors matchIH remainingIH =>
    intro shape sourceTyped projection size within mapping world actualContext environment canonical actual before store ξ
      contextLocation native environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted
      finalContext outcome after trace
    cases compilation with
    | mk values solved sourceCells ambientDefinitions =>
      cases sameValues
      have selectedMeaning : SelectedCompilationStageMatchSequences.MatchLifts
          (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
          (stages := stages) (invocation := invocation)
          bridge functions condition context scope resolution budget :=
        SelectedCompilationStageMatchTreeHeads.lifts bridge functions onError allocator definitions registered extension receipt ordinary
          patternContext.signatures catalog scrutineeFound scrutineeTyped casesTyped defaultTyped budget condition producer bindings acquire unique
          (typedChildren context) (typedPreservation context)
          (fun request member childContext selectedContext bodyTyped =>
            matchIH request member childContext selectedContext (shape.match_request found form selectedContext.forget) bodyTyped projection)
      have selectedPreservation : ∀ n, CallableIndexedOwnedAdmittedStagedMatchSequences.MatchPreserves
          (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
          (stages := stages) (invocation := invocation) (faults := faults)
          bridge functions condition context scope resolution expected type matched n := by
        intro n matchSize
        exact CallableIndexedOwnedAdmittedStagedMatchTreeHeads.preserves (size := matchSize)
          bridge functions onError allocator definitions registered extension receipt ordinary
          patternContext.signatures catalog scrutineeFound scrutineeTyped casesTyped defaultTyped
          n condition producer bindings acquire unique (fun childSize _ => typedPreservation context childSize)
          (fun request member childContext selectedContext bodyTyped =>
            preserves_position (semantic := semantic) bridge bindings transport functions extension definitions registered producer condition acquire
              preservation unique (matchChildren request member childContext selectedContext)
              (childErrors request member childContext selectedContext)
              (shape.match_request found form selectedContext.forget) bodyTyped projection n)
      obtain ⟨_armShapes, _defaultShape, restShape⟩ := shape.match_children found form
      exact SelectedCompilationStageMatchSequences.lifts bridge functions condition unique found form selectedMeaning selectedPreservation
        (.inl (remainingIH restShape (CallableIndexedOwnedPreparedStagedScopedMatchSourceTyping.suffix unique sourceTyped found form) projection)) within environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted trace
  | @terminalMatch context scope mode id node resolution scrutineeNode rest expected type matched suffix selfReason control caseFacts exactUnique found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary matchChildren stops issued catalog patternContext childErrors matchIH =>
    intro shape sourceTyped projection size within mapping world actualContext environment canonical actual before store ξ
      contextLocation native environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted
      finalContext outcome after trace
    cases compilation with
    | mk values solved sourceCells ambientDefinitions =>
      cases sameValues
      have selectedMeaning : SelectedCompilationStageMatchSequences.MatchLifts
          (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
          (stages := stages) (invocation := invocation)
          bridge functions condition context scope resolution budget :=
        SelectedCompilationStageMatchTreeHeads.lifts bridge functions onError allocator definitions registered extension receipt ordinary
          patternContext.signatures catalog scrutineeFound scrutineeTyped casesTyped defaultTyped budget condition producer bindings acquire unique
          (typedChildren context) (typedPreservation context)
          (fun request member childContext selectedContext bodyTyped =>
            matchIH request member childContext selectedContext (shape.match_request found form selectedContext.forget) bodyTyped projection)
      have selectedPreservation : ∀ n, CallableIndexedOwnedAdmittedStagedMatchSequences.MatchPreserves
          (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
          (stages := stages) (invocation := invocation) (faults := faults)
          bridge functions condition context scope resolution expected type matched n := by
        intro n matchSize
        exact CallableIndexedOwnedAdmittedStagedMatchTreeHeads.preserves (size := matchSize)
          bridge functions onError allocator definitions registered extension receipt ordinary
          patternContext.signatures catalog scrutineeFound scrutineeTyped casesTyped defaultTyped
          n condition producer bindings acquire unique (fun childSize _ => typedPreservation context childSize)
          (fun request member childContext selectedContext bodyTyped =>
            preserves_position (semantic := semantic) bridge bindings transport functions extension definitions registered producer condition acquire
              preservation unique (matchChildren request member childContext selectedContext)
              (childErrors request member childContext selectedContext)
              (shape.match_request found form selectedContext.forget) bodyTyped projection n)
      obtain ⟨_armShapes, _defaultShape, restShape⟩ := shape.match_children found form
      exact SelectedCompilationStageMatchSequences.lifts bridge functions condition unique found form selectedMeaning selectedPreservation
        (.inr stops) within environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted trace
  | @breaking context scope mode id node rest expected type found form =>
    intro shape sourceTyped projection size within mapping world actualContext environment canonical actual before store ξ
      contextLocation native environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted
      finalContext outcome after trace
    have ordinary : TypedScopedStatements.Executes mode program context invocation.evidence invocation.source
        environment before (id :: rest) finalContext outcome after := by
      cases mode <;> exact trace.sound
    obtain ⟨rfl, rfl, rfl⟩ := ProtectedLoopStatements.breaking_view unique found form ordinary
    exact ⟨_, _, _, .breaking (lookupStatement?_sound found) form, .completed (.breaking environment)⟩
  | @continuing context scope mode id node rest expected type found form =>
    intro shape sourceTyped projection size within mapping world actualContext environment canonical actual before store ξ
      contextLocation native environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted
      finalContext outcome after trace
    have ordinary : TypedScopedStatements.Executes mode program context invocation.evidence invocation.source
        environment before (id :: rest) finalContext outcome after := by
      cases mode <;> exact trace.sound
    obtain ⟨rfl, rfl, rfl⟩ := ProtectedLoopStatements.continuing_view unique found form ordinary
    exact ⟨_, _, _, .continuing (lookupStatement?_sound found) form, .completed (.continuing environment)⟩
  | @bitNot _ _ _ _ _ _ _ _ _ _ found form _ _ _ _ _ =>
    intro shape sourceTyped projection size within mapping world actualContext environment canonical actual before store ξ
      contextLocation native environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted
      finalContext outcome after trace
    have impossible := shape.head_allowed found
    simp only [form, CallableIndexedOwnedPreparedStagedBranchingTree.allowedForm, Bool.false_eq_true] at impossible
  | @forLoop context scope mode id node items test post statements rest expected type initialCode body found form initialTree remaining initialErrors remainingErrors initialIH remainingIH =>
    intro shape sourceTyped projection size within mapping world actualContext environment canonical actual before store ξ
      contextLocation native environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted
      finalContext outcome after trace
    obtain ⟨initialShape, postShape, loopShape, restShape⟩ := shape.for_children found form
    have initialTyped := CallableIndexedOwnedPreparedStagedScopedForSourceTyping.children unique sourceTyped found form
    have tailTyped := CallableIndexedOwnedPreparedStagedScopedForSourceTyping.suffix unique sourceTyped found form
    exact SelectedCompilationStageForSequenceLifting.lifts bridge functions condition
      (initialIH ⟨initialShape, postShape, loopShape⟩ initialTyped projection)
      (preserves_position (semantic := semantic) bridge bindings transport functions extension definitions registered producer condition acquire
        preservation unique initialTree initialErrors ⟨initialShape, postShape, loopShape⟩ initialTyped projection)
      unique found form (remainingIH restShape tailTyped projection) within environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted trace
  | @initializersDone context scope test node post statements expected type testCode bodyCode postCode selfReason found nodeType certified bodyTree postTree nativeTyped bodyErrors postErrors bodyIH =>
    intro shape sourceTyped projection
    obtain ⟨control, _testTyped, bodyTyped, postTyped⟩ := InitializerTyping.nil sourceTyped
    obtain ⟨typedNode, typedFound, typed, generated⟩ := certified
    cases Option.some.inj (found.symm.trans typedFound)
    intro size within environment canonical actual actualContext ξ contextLocation native before after ready outcome trace
    exact SelectedCompilationStageForInitialLifting.done bridge functions definitions registered condition transport extension
      bindings producer acquire children preservation unique found typed generated
      (bodyIH shape.2.2 bodyTyped projection)
      (preserves_position (semantic := semantic) bridge bindings transport functions extension definitions registered producer condition acquire
        preservation unique bodyTree bodyErrors shape.2.2 bodyTyped projection)
      postTree postErrors semantic shape.2.1 postTyped within ready trace
  | @initializerUninitialized context nextContext scope binder rest body payload test post statements expected type mono extended ordinary projected allocation annotation same tail remainingErrors ih =>
    intro shape sourceTyped projection
    intro size within environment canonical actual actualContext ξ contextLocation native before after ready outcome trace
    exact SelectedCompilationStageForInitialLifting.absent bridge functions definitions registered producer.toOrdinary condition acquire
      mono extended ordinary projected allocation annotation same
      (ih ⟨shape.1.let_tail, shape.2⟩ (InitializerTyping.absent sourceTyped extended) projection) within ready trace
  | @initializerInitialized context nextContext scope binder initializer initializerNode lowered body rest test post statements expected type mono extended ordinary initialFound sourceType child allocation annotation same remaining remainingErrors ih =>
    intro shape sourceTyped projection
    obtain ⟨typedNode, typedFound, typed, certified⟩ := child
    cases Option.some.inj (initialFound.symm.trans typedFound)
    intro size within environment canonical actual actualContext ξ contextLocation native before after ready outcome trace
    exact SelectedCompilationStageForInitialLifting.initialized bridge functions definitions registered producer.toOrdinary condition acquire
      mono extended ordinary initialFound sourceType typed certified allocation annotation same (children _) (preservation _)
      (ih ⟨shape.1.let_tail, shape.2⟩ (InitializerTyping.initialized sourceTyped mono extended) projection) within ready trace
  | @initializerDiscard context scope expression expressionNode rest lowered body test post statements expected type expressionFound child remaining remainingErrors ih =>
    intro shape sourceTyped projection
    obtain ⟨typedNode, typedFound, typed, certified⟩ := child
    cases Option.some.inj (expressionFound.symm.trans typedFound)
    intro size within environment canonical actual actualContext ξ contextLocation native before after ready outcome trace
    exact SelectedCompilationStageForInitialLifting.discard bridge functions condition expressionFound typed certified
      (children _) (preservation _)
      (ih ⟨shape.1.discard_tail, shape.2⟩ (InitializerTyping.expression sourceTyped) projection) within ready trace
  | @initializerAssign context scope assignment operator rhs rest body test post statements expected type head remaining remainingErrors headErrors ih =>
    intro shape sourceTyped projection
    obtain ⟨_profile, bare, tailShape⟩ := shape.1.assign_tail
    intro size within environment canonical actual actualContext ξ contextLocation native before after ready outcome trace
    exact SelectedCompilationStageForInitialLifting.assign bridge functions condition transport extension unique head bare
      (InitializerTyping.assignment sourceTyped).1 (typedChildren context) (typedPreservation context)
      (ih ⟨tailShape, shape.2⟩ (InitializerTyping.assignment sourceTyped).2 projection) within ready trace
  | initializerBitNot =>
    intro shape sourceTyped projection
    cases shape.1

include bridge bindings definitions registered producer acquire transport extension in
theorem lifts_at {budget : Nat}
    (children : ∀ context childSize, childSize < budget → LiftsAt bridge context model stages invocation (certificates context) childSize)
    (preservation : ∀ context size, PreservesAt bridge context model stages invocation (certificates context) faults size)
    (unique : NodeOccurrencesUnique invocation.source)
    {expressionSyntax : ExpressionId → Prop} {administrative : Core.Context}
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {position : GenericImperativeMatch.Position} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError (.initial compiled.compatible.checked)
      invocation.source expressionSyntax (TypedCertificate invocation.source certificates)
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions administrative context scope position expected type code)
    {diagnosticPolicy : AssignmentDiagnosticPolicy} {catalogRegistry : SourceCoreRawMetadata.Registry} {catalogFaults : FunctionCalls.FaultRep}
    (catalogSites : Tree.CatalogSites diagnosticPolicy catalogRegistry catalogFaults tree)
    (semantic : ∀ reason token, catalogFaults reason token → faults (.semantic reason) token)
    {mode : Bool} {statements : List StatementId}
    (atStatements : position = .statements mode statements)
    (shape : Shape invocation.source mode statements)
    (sourceTyped : ProtectedStateImperativeTypedSourceSites.Statements invocation.source context statements)
    (projection : compiled.compatible.checked.catalog.project expected = .ok type) :
    FlowLifts (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) bridge functions condition context scope mode statements budget := by
  cases atStatements
  exact lifts_position (semantic := semantic) bridge bindings transport functions extension definitions registered producer condition acquire
    children preservation unique tree catalogSites shape sourceTyped projection

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageImperativeLifting
