import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodySupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDiscardTerminalCompilerFlowBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalBodyMeaning

/-! The same accepted discard receipt supplies the literal whole-body footer.
The checked compiler-flow family constructs both child meanings internally;
the existing finish and prefix lemmas preserve its exact returned value or
staged failure and reached caller state. Native reflection uses the actual
strict flow child and determinism. No body execution law or desired result
is an input. Mixed called-body support remains a separate grammar extension. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDiscardTerminalCompilerBodyBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPublicFaultReceiverTables (IssuedAt)
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)
open CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds (TerminalFor)
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)
open CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport (NamedSupport ClosureSupportFor)
open CallableIndexedOwnedPreparedStagedDiscardTerminalCompilerReceipts (Receipt)
open CallableIndexedOwnedPreparedStagedDiscardTerminalCompilerFlowBounds (Static Ready)
open CallableIndexedOwnedAdmittedStagedTerminalStatements (control)
open CallableIndexedOwnedPreparedStagedTerminalBodyMeaning (fallback)

/-- The actual accepted statement action fixes the flow and footer together. -/
theorem emitted_rename {policy : SourceCoreLoops.Policy} {fuel : Nat}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {statement : StatementId}
    {firstExpression terminalExpression : ExpressionId} {rest : List StatementId}
    {result : Ty} {reasonAt : ExpressionId → Word} {fellThrough escaped : Word} {code : Expr}
    (receipt : Receipt policy fuel source scope statement firstExpression terminalExpression rest
      result reasonAt fellThrough escaped code) (ξ : Renaming) :
    code.rename ξ = CallableIndexedOwnedAdmittedStagedTerminalBody.code result
      ((LocalSequence.discard (LocalLoop.controlType result) receipt.first.expression
        (LocalLoop.returnValue result receipt.tail.child.expression)).rename ξ)
      escaped ((fallback result fellThrough).rename ξ) := by
  have footer := congrArg (fun generated : Expr => generated.rename ξ) receipt.emitted
  exact footer.trans (by
    simpa only [CompatibleStatements.finish,
      CallableIndexedOwnedAdmittedStagedTerminalBody.code, fallback] using
      (CallableIndexedOwnedAdmittedStagedTerminalBody.code_rename result
        (LocalSequence.discard (LocalLoop.controlType result) receipt.first.expression
          (LocalLoop.returnValue result receipt.tail.child.expression))
        escaped (fallback result fellThrough) ξ))

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
    CallableIndexedOwnedPreparedStagedNamedBodySupport.LegacySupport headers keys bodyRegistry
      header stages (namedTerminals header member) semanticFaults)

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys
  bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked
  completion.result.context.registry functions
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

section Bounds
variable {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {scope : SourceCoreLocalCell.Scope} {statement next : StatementId} {rest : List StatementId}
  {firstExpression terminalExpression : ExpressionId} {result : Ty}
  {reasonAt : ExpressionId → Word} {fellThrough escaped : Word} {code : Expr}
  {statementPolicy : SourceCoreLoops.Policy} {fuel : Nat} {view : TypedSource}
  {function : Dynamic.Closure} {types : List TypeSystem.Ty}
  {changed : List ExpressionId} {roots : List NodeId}
  {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
  {compilation : SourceCoreFunctions.Context} {readFuel bodyFuel : Nat}
  {native : Option SourceCoreGeneralFunctions.CallableContext} {active : TypeSystem.Substitution}
  {receipt : Receipt statementPolicy fuel view scope statement firstExpression terminalExpression
    (next :: rest) result reasonAt fellThrough escaped code}
  (packet : Static (compiled := compiled) (function := function) (context := context)
    (types := types) (invocation := invocation) (changed := changed) (roots := roots)
    (policy := policy) (lowerBody := lowerBody) (compilation := compilation)
    (readFuel := readFuel) (bodyFuel := bodyFuel) (semanticFaults := semanticFaults)
    (native := native) (active := active) receipt)
  (ready : Ready packet)
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
  closureTerminals namedTerminals closureSupport namedSupport packet ready
  environments heaps locals agrees actualTyped admitted in
/-- The complete Source trace constructs its actual BodyResult and the whole
native code from the same internally issued head and terminal certificates. -/
theorem preserves_body {size : Nat} {finalContext : SourceSemantics.Context}
    {bodyOutcome : Staging.Recursive.BodyOutcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Statements (Program.ofChecked compiled.sourceProgram)
      stages size invocation context environment before (statement :: next :: rest)
      finalContext bodyOutcome after) :
    finalContext = context ∧ ∃ outcome,
      bodyOutcome = control outcome ∧
      Staging.Recursive.BodyResult function.resultType bodyOutcome outcome ∧
      ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
        function.resultType result callFaults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
          bridge context function.resultType outcome reached := by
  obtain ⟨sameContext, outcome, sameBody, value, finalStore, finalMap, finalWorld,
      evaluated, represented, finalHeaps, maps, worlds, frame, metadata, reached, related, post⟩ :=
    CallableIndexedOwnedPreparedStagedDiscardTerminalCompilerFlowBounds.preserves
    (bridge := bridge) (receiver := receiver) (stagePrepared := stagePrepared)
    (profile := profile) (observations := observations) (extension := extension) (semantic := semantic)
    (closureTerminals := closureTerminals) (namedTerminals := namedTerminals)
    (closureSupport := closureSupport) (namedSupport := namedSupport)
    (packet := packet) (ready := ready)
    (environments := environments) (heaps := heaps) (locals := locals) (agrees := agrees)
    (actualTyped := actualTyped) (initial := initial) (admitted := admitted) trace
  obtain ⟨wholeValue, whole, resultRep⟩ :=
    CallableIndexedOwnedAdmittedStagedTerminalBody.terminal_evaluates
      (fallback := (fallback result fellThrough).rename ξ) represented evaluated escaped
  have evaluatedBody : Evaluates actual store (code.rename ξ) wholeValue finalStore := by
    rw [emitted_rename receipt ξ]
    exact whole
  have bodyResult : Staging.Recursive.BodyResult function.resultType bodyOutcome outcome := by
    rw [sameBody]
    exact CallableIndexedOwnedAdmittedStagedTerminalBody.body_result _ _
  exact ⟨sameContext, outcome, sameBody, bodyResult, wholeValue, finalStore, finalMap, finalWorld,
    evaluatedBody, resultRep, finalHeaps, maps, worlds, frame, metadata, reached, related, post⟩

include bridge receiver stagePrepared observations extension semantic
  closureTerminals namedTerminals closureSupport namedSupport packet ready
  environments heaps locals agrees actualTyped admitted in
/-- Footer inversion obtains a real strict flow child. Its constructive
reflection and deterministic footer retain the original completed endpoint. -/
theorem reflects_body (stageEq : stages = RecursiveNamedPreparedStageScopes.registry stagePrepared)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (code.rename ξ) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Statements (Program.ofChecked compiled.sourceProgram) stages sourceSize
        invocation context environment before (statement :: next :: rest) context (control outcome) after ∧
      Staging.Recursive.BodyResult function.resultType (control outcome) outcome ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
        function.resultType result callFaults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
          bridge context function.resultType outcome reached := by
  have original := completed
  rw [emitted_rename receipt ξ] at original
  obtain ⟨flowSize, flowValue, flowStore, flowTrace, _strict⟩ :=
    CallableIndexedOwnedAdmittedStagedTerminalBody.flow_prefix original (Nat.le_refl size)
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented,
      finalHeaps, maps, worlds, frame, metadata, reached, related, post⟩ :=
    CallableIndexedOwnedPreparedStagedDiscardTerminalCompilerFlowBounds.reflects
    (bridge := bridge) (receiver := receiver) (stagePrepared := stagePrepared)
    (profile := profile) (observations := observations) (extension := extension) (semantic := semantic)
    (closureTerminals := closureTerminals) (namedTerminals := namedTerminals)
    (closureSupport := closureSupport) (namedSupport := namedSupport)
    (packet := packet) (ready := ready)
    (environments := environments) (heaps := heaps) (locals := locals) (agrees := agrees)
    (actualTyped := actualTyped) (initial := initial) (admitted := admitted) stageEq flowTrace
  obtain ⟨wholeValue, whole, resultRep⟩ :=
    CallableIndexedOwnedAdmittedStagedTerminalBody.terminal_evaluates
      (fallback := (fallback result fellThrough).rename ξ) represented flowTrace.sound escaped
  obtain ⟨same, stores⟩ := evaluation_deterministic original.sound whole
  cases same
  subst stores
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace,
    CallableIndexedOwnedAdmittedStagedTerminalBody.body_result _ _, resultRep,
    finalHeaps, maps, worlds, frame, metadata, reached, related, post⟩
end Bounds
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDiscardTerminalCompilerBodyBounds
