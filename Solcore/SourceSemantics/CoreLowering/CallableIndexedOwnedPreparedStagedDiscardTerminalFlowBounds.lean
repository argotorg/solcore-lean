import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodySupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedCallerFromRecursiveBodies
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDiscardSourceBodyInversion

/-! A real semicolon discard and an original terminal tail compose two
authentic Source Roots. Every expression and called-body law is supplied
internally by the checked selected caller family. The intermediate state is
the head producer's actual reached state. This flow adapter leaves the same
accepted statement/compiler and mixed invoked-body factory joins explicit. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDiscardTerminalFlowBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPublicFaultReceiverTables (IssuedAt)
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)
open CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds (TerminalFor)
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)
open CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport (RootAt NamedSupport ClosureSupportFor)
open CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds (Point)
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedAdmittedStagedTerminalStatements (Head control ResultRepresents)
open GenericExpressionMeaning (agree_prefix rename_prefix)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
    completion.result.extension completion.result.diagnostics)
  {stages : Staging.Recursive.Registry}
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile) identities)
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry
    completion.result.context.registry)
  (semantic : ∀ reason token, semanticFaults reason token →
    CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token)
  (closureTerminals : ∀ {mapping world function native bindings parameterCore resultCore}
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore), TerminalFor association stages)
  (namedTerminals : ∀ header, header ∈ headers → Terminal header)
  (closureSupport : ∀ {mapping world function native bindings parameterCore resultCore}
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore),
    ClosureSupportFor association stages (closureTerminals association))
  (namedSupport : ∀ header (member : header ∈ headers),
    CallableIndexedOwnedPreparedStagedNamedBodySupport.Support headers keys bodyRegistry
      header stages (namedTerminals header member) semanticFaults)

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys
  bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked
  completion.result.context.registry functions
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include bridge receiver stagePrepared observations extension semantic
  closureTerminals namedTerminals closureSupport namedSupport in
private theorem internal_preserves_below {context invocation scope expression lowered}
    (root : RootAt compiled context invocation scope expression lowered semanticFaults)
    (budget : Nat) :
    PreservesBelow bridge context model stages invocation (Point scope expression lowered) callFaults budget := by
  intro childSize _strict
  exact CallableIndexedOwnedPreparedStagedSelectedCallerFromRecursiveBodies.preserves
    (bridge := bridge) (receiver := receiver) (stagePrepared := stagePrepared)
    (profile := profile) (observations := observations) (extension := extension) (semantic := semantic)
    (closureTerminals := closureTerminals) (namedTerminals := namedTerminals)
    (closureSupport := closureSupport) (namedSupport := namedSupport) root childSize

include bridge receiver stagePrepared observations extension semantic
  closureTerminals namedTerminals closureSupport namedSupport in
private theorem internal_reflects_below
    (stageEq : stages = RecursiveNamedPreparedStageScopes.registry stagePrepared)
    {context invocation scope expression lowered}
    (root : RootAt compiled context invocation scope expression lowered semanticFaults)
    (budget : Nat) :
    ReflectsBelow bridge context model stages invocation (Point scope expression lowered) callFaults budget := by
  intro childSize _strict
  exact CallableIndexedOwnedPreparedStagedSelectedCallerFromRecursiveBodies.reflects
    (bridge := bridge) (receiver := receiver) (stagePrepared := stagePrepared)
    (profile := profile) (observations := observations) (extension := extension) (semantic := semantic)
    (closureTerminals := closureTerminals) (namedTerminals := namedTerminals)
    (closureSupport := closureSupport) (namedSupport := namedSupport) stageEq root childSize

section Flow
variable {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {scope : SourceCoreLocalCell.Scope} {firstExpression terminalExpression : ExpressionId}
  {firstCode terminalCode : SourceCoreBasic.LoweredExpr}
  (firstRoot : RootAt compiled context invocation scope firstExpression firstCode semanticFaults)
  (terminalRoot : RootAt compiled context invocation scope terminalExpression terminalCode semanticFaults)
  {statement : StatementId} {rest : List StatementId} {statementNode : StatementNode}
  (contains : ContainsStatement invocation.source statement statementNode)
  (form : statementNode.form = .expression firstExpression true)
  (terminal : Head invocation terminalExpression rest)
  {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
  {store : Store} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents
    (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
  (heaps : GenericHeap.HeapRepresents
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry
      (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile))
    mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)

include bridge receiver stagePrepared observations extension semantic
  closureTerminals namedTerminals closureSupport namedSupport
  firstRoot contains form terminal environments heaps locals agrees actualTyped admitted in
/-- Original statement inversion selects both genuine children. Successful
head effects feed the tail at its reached Admission and the inserted native
temporary binder. The public theorem accepts no child execution law. -/
theorem preserves {size : Nat} {finalContext : SourceSemantics.Context}
    {bodyOutcome : Staging.Recursive.BodyOutcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Statements (Program.ofChecked compiled.sourceProgram)
      stages size invocation context environment before (statement :: rest) finalContext bodyOutcome after) :
    finalContext = context ∧ ∃ outcome,
      bodyOutcome = control outcome ∧ ∃ value finalStore finalMap finalWorld,
      Evaluates actual store
        ((LocalSequence.discard (LocalLoop.controlType terminalCode.type) firstCode.expression
          (LocalLoop.returnValue terminalCode.type terminalCode.expression)).rename ξ) value finalStore ∧
      ResultRepresents model finalMap finalWorld terminalRoot.support.node.type terminalCode.type
        callFaults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧
        PostAdmission bridge context terminalRoot.support.node.type outcome reached := by
  have firstBelow := internal_preserves_below bridge receiver stagePrepared profile observations extension
    semantic closureTerminals namedTerminals closureSupport namedSupport firstRoot size
  have terminalBelow := internal_preserves_below bridge receiver stagePrepared profile observations extension
    semantic closureTerminals namedTerminals closureSupport namedSupport terminalRoot size
  rcases CallableIndexedOwnedPreparedStagedDiscardSourceBodyInversion.child_and_tail
      firstRoot.support.unique contains form trace with
    ⟨firstSize, failure, sameSize, rfl, rfl, firstTrace⟩ |
    ⟨firstSize, tailSize, sourceValue, middle, sameSize, firstTrace, tailTrace⟩
  · have firstStrict : firstSize < size := by
      rw [sameSize]
      exact Staging.Recursive.Size.child_lt_stepSize (by simp)
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
        maps, worlds, frame, metadata, reached, related, post⟩ :=
      firstBelow firstSize firstStrict ⟨rfl, rfl, rfl⟩ firstRoot.support.found firstRoot.support.typed
        environments heaps locals agrees actualTyped initial admitted firstTrace
    cases represented with
    | fault matched =>
        refine ⟨rfl, .fault failure, rfl, _, finalStore, finalMap, finalWorld, ?_, .fault matched,
          finalHeaps, maps, worlds, frame, metadata, reached, related, post.at_fault_type⟩
        rw [LoopRenaming.discard]
        exact LocalSequence.discard_failure _ evaluated
  · have firstStrict : firstSize < size := by
      rw [sameSize]
      exact Staging.Recursive.Size.child_lt_stepSize (by simp)
    obtain ⟨value, middleStore, middleMap, middleWorld, first, represented, middleHeaps,
        firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, firstRelated, firstPost⟩ :=
      firstBelow firstSize firstStrict ⟨rfl, rfl, rfl⟩ firstRoot.support.found firstRoot.support.typed
        environments heaps locals agrees actualTyped initial admitted firstTrace
    cases represented with
    | @value sourceValue coreValue payload =>
        obtain ⟨terminalSize, outcome, sameTailSize, rfl, rfl, terminalTrace⟩ :=
          CallableIndexedOwnedPreparedStagedTerminalSourceBodyInversion.child_of_body
            terminalRoot.support.unique terminal tailTrace
        have tailWithin : Staging.Recursive.Size.stepSize [terminalSize] ≤ size := by
          rw [← sameTailSize, sameSize]
          exact Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))
        obtain ⟨_tailTrace, value, finalStore, finalMap, finalWorld, second, represented, finalHeaps,
            maps, worlds, frame, metadata, reached, related, post⟩ :=
          CallableIndexedOwnedAdmittedStagedTerminalStatements.preserves bridge terminal
            ⟨rfl, rfl, rfl⟩ terminalRoot.support.found terminalRoot.support.typed
            (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
            (agree_prefix agrees coreValue)
            (.cons ((model).runtime_hasType payload) (actualTyped.weaken firstWorlds))
            middleState firstPost.at_value.2 size terminalBelow terminalTrace tailWithin
        refine ⟨rfl, outcome, rfl, value, finalStore, finalMap, finalWorld, ?_, represented, finalHeaps,
          firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame,
          firstMetadata.trans metadata, reached, callerProtocol.trans firstRelated related, post⟩
        rw [LoopRenaming.discard]
        rw [rename_prefix] at second
        exact LocalSequence.discard_success _ first second

include bridge receiver stagePrepared observations extension semantic
  closureTerminals namedTerminals closureSupport namedSupport
  firstRoot contains form terminal environments heaps locals agrees actualTyped admitted in
/-- Native inversion supplies strict executed children. Reflection rebuilds
the original discard and terminal Source traces with independent grades,
retaining the same stores, record relations and exact nested Failure. -/
theorem reflects (stageEq : stages = RecursiveNamedPreparedStageScopes.registry stagePrepared)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store
      ((LocalSequence.discard (LocalLoop.controlType terminalCode.type) firstCode.expression
        (LocalLoop.returnValue terminalCode.type terminalCode.expression)).rename ξ) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Statements (Program.ofChecked compiled.sourceProgram) stages sourceSize
        invocation context environment before (statement :: rest) context (control outcome) after ∧
      ResultRepresents model finalMap finalWorld terminalRoot.support.node.type terminalCode.type
        callFaults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧
        PostAdmission bridge context terminalRoot.support.node.type outcome reached := by
  have firstBelow := internal_reflects_below bridge receiver stagePrepared profile observations extension
    semantic closureTerminals namedTerminals closureSupport namedSupport stageEq firstRoot size
  have terminalBelow := internal_reflects_below bridge receiver stagePrepared profile observations extension
    semantic closureTerminals namedTerminals closureSupport namedSupport stageEq terminalRoot size
  have original := completed
  rw [LoopRenaming.discard] at original
  change EvaluationSize size actual store
    (LanguageResult.bind (LocalLoop.controlType terminalCode.type) (firstCode.expression.rename ξ)
      (((LocalLoop.returnValue terminalCode.type terminalCode.expression).rename ξ).weakenAt 0))
    value finalStore at original
  cases CallableIndirectCallBounds.bind_completed original (Nat.le_refl _) with
  | failed first strict =>
      obtain ⟨firstSize, outcome, after, finalMap, finalWorld, firstTrace, represented, finalHeaps,
          maps, worlds, frame, metadata, reached, related, post⟩ :=
        firstBelow _ strict ⟨rfl, rfl, rfl⟩ firstRoot.support.found firstRoot.support.typed
          environments heaps locals agrees actualTyped initial admitted first
      cases represented with
      | fault matched =>
          exact ⟨_, .fault _, after, finalMap, finalWorld,
            .expressionFault contains form firstTrace, .fault matched, finalHeaps,
            maps, worlds, frame, metadata, reached, related, post.at_fault_type⟩
  | continued first remaining firstStrict remainingStrict =>
      obtain ⟨firstSize, outcome, middle, middleMap, middleWorld, firstTrace, represented, middleHeaps,
          firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, firstRelated, firstPost⟩ :=
        firstBelow _ firstStrict ⟨rfl, rfl, rfl⟩ firstRoot.support.found firstRoot.support.typed
          environments heaps locals agrees actualTyped initial admitted first
      cases represented with
      | @value sourceValue coreValue payload =>
          have shifted := remaining
          rw [← rename_prefix] at shifted
          obtain ⟨tailSize, outcome, after, finalMap, finalWorld, tailTrace, represented, finalHeaps,
              maps, worlds, frame, metadata, reached, related, post⟩ :=
            CallableIndexedOwnedAdmittedStagedTerminalStatements.reflects bridge terminal
              ⟨rfl, rfl, rfl⟩ terminalRoot.support.found terminalRoot.support.typed
              (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (agree_prefix agrees _)
              (.cons ((model).runtime_hasType payload) (actualTyped.weaken firstWorlds))
              middleState firstPost.at_value.2 size terminalBelow shifted (Nat.le_of_lt remainingStrict)
          exact ⟨_, outcome, after, finalMap, finalWorld, .discard contains form firstTrace tailTrace,
            represented, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
            firstFrame.trans frame, firstMetadata.trans metadata, reached,
            callerProtocol.trans firstRelated related, post⟩
end Flow
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDiscardTerminalFlowBounds
