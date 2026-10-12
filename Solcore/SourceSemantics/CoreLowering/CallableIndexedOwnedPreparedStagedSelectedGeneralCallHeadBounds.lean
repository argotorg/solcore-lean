import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedIndirectTerminalCallBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRecursiveCallerSourceReceipts

/-! Internal call-head interfaces for the later numeric recursive-body family.
The actual original compiler receipt, raw typing and ordered children feed the
additive selected whole-call proof. Caller and called-body strict hypotheses
are separate inputs here; the eventual public numeric family must construct
them. Runtime states and execution laws are not fields of the static Port.
The called-body hypotheses refer only to the statically chosen terminal.
-/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedGeneralCallHeadBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters (Prepared SourceParent)
open CallableIndexedOwnedContextualDiagnosticSources (SourceView)
open CallableIndexedOwnedPublicFaultReceiverTables (IssuedAt)
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)
open CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds (TerminalFor ReflectsBelowFor)
open CallableIndexedOwnedPreparedStagedTerminalClosureParentPreservation (PreservesBelowFor)
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)
open CallableIndexedOwnedAdmittedStagedExpressionBounds
universe u

def Point (scope : SourceCoreLocalCell.Scope) (id : ExpressionId)
    (lowered : SourceCoreBasic.LoweredExpr) : GenericExpressionMeaning.Certificate :=
  fun current child code => current = scope ∧ child = id ∧ code = lowered

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : SourceCoreCallableIndexedPrograms.Completion compiled.indexed}
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}

/-- Actual accepted compiler and sidecar authority. Every field is static.
The callee's raw typing is derived from the supplied original parent typing. -/
structure Port (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation
    source scope id callee ids metadata reasonAt lowered) where
  prepared : Prepared compiler compiled.indexed.ancestry.graph.inputs.callable
  sidecar : SourceCoreStageContracts.Sidecar
  caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar
  view : SourceView sidecar.source source
  guardFrame : invocation.guards = CallableLedger.frame sidecar
  originalUnique : NodeOccurrencesUnique sidecar.source
  sourceParent : SourceParent compiler
  calleeNode : ExpressionNode
  calleeFound : source.lookupExpression? callee = some calleeNode

variable {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
    completion.result.extension completion.result.diagnostics)
  {stages : Staging.Recursive.Registry}
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)
  (sourceEq : invocation.source = source)
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
  (covers : invocation.evidence.Covers context)
  (unique : NodeOccurrencesUnique invocation.source)
  (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile) identities)
  (closureTerminals : ∀ {mapping world function native bindings parameterCore resultCore}
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore), TerminalFor association stages)
  (namedTerminals : ∀ header, header ∈ headers → Terminal header)

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys
  bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked
  completion.result.context.registry functions
local notation "poolBridge" => CallableIndexedOwnedBodyRestorationAdmission.bridge (headers := headers) (keys := keys)
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
  completion.result.diagnostics

include bridge receiver stagePrepared sourceEq profile wellFormed runtime covers unique
  actualFunctionType observations closureTerminals namedTerminals in
/-- Reuse the original whole-call producer at the supplied genuine Source
grade. The returned caller state and post are retained literally. -/
theorem preserves
    (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
      id callee ids metadata reasonAt lowered)
    (port : Port (compiled := compiled) (invocation := invocation) compiler)
    {certificate : GenericExpressionMeaning.Certificate}
    (calleeCertified : certificate scope callee compiler.calleeCode)
    {sourceTypes : List TypeSystem.Ty}
    (tree : DataExpressionSequence.Tree invocation.source certificate scope ids sourceTypes compiler.codes)
    (size : Nat)
    (children : PreservesBelow bridge context model stages invocation certificate callFaults size)
    (closureChildren : ∀ {mapping world function native bindings parameterCore resultCore}
      (association : Association headers keys bodyRegistry semanticFaults mapping world function native
        bindings parameterCore resultCore),
      PreservesBelowFor (registry := completion.result.context.registry) (faults := callFaults)
        association (closureTerminals association) functions size)
    (namedChildren : ∀ header (member : header ∈ headers),
      ∀ {child : Staging.Recursive.Scope}, stages.Closure header.function child →
      CallableIndexedOwnedPreparedStagedNamedChildBounds.PreservesBelow (headers := headers) (keys := keys)
        header model stages child
        (namedTerminals header member).certificate callFaults size) :
    PreservesAt bridge context model stages invocation (Point scope id lowered) callFaults size := by
  intro current child code point node found parentTyped
    mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees actualTyped initial admitted trace
  obtain ⟨rfl, rfl, rfl⟩ := point
  cases sourceEq
  cases Option.some.inj (found.symm.trans compiler.found)
  obtain ⟨parameter, result, rawTypes, calleeTyped, _argumentsTyped, _bundle, _resultType⟩ :=
    CallableIndexedOwnedPreparedStagedRecursiveCallerSourceReceipts.original_child_types
      compiler port.sourceParent unique parentTyped
  have reported := CallableIndexedOwnedContextualInitializedClosureReceipts.reported_type_at
    unique port.calleeFound calleeTyped
  have sourceTyped : ExpressionHasType invocation.source context callee port.calleeNode.type := by
    simpa only [reported] using calleeTyped
  have occurrence : Staging.Recursive.Occurrence invocation child (.call callee ids (.indirect metadata)) :=
    ⟨compiler.original, lookupExpression?_sound compiler.found, compiler.originalForm,
      port.sourceParent.requirements, port.sourceParent.coercions⟩
  exact (CallableIndexedOwnedPreparedStagedSelectedIndirectTerminalCallBounds.preserves_parent
    bridge receiver compiler port.prepared stagePrepared rfl occurrence initial port.view port.guardFrame
    profile calleeCertified port.calleeFound sourceTyped environments heaps locals agrees actualTyped
    admitted port.caller port.originalUnique port.sourceParent tree unique parentTyped
    wellFormed runtime covers actualFunctionType observations
    size children closureTerminals closureChildren namedTerminals namedChildren trace (Nat.le_refl _)).2

include bridge receiver stagePrepared sourceEq profile wellFormed runtime covers unique
  actualFunctionType observations closureTerminals namedTerminals in
/-- The native completion keeps its independent Source grade and exact
staged fault scope. Only the duplicate native evaluation witness is omitted. -/
theorem reflects
    (stageEq : stages = RecursiveNamedPreparedStageScopes.registry stagePrepared)
    (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
      id callee ids metadata reasonAt lowered)
    (port : Port (compiled := compiled) (invocation := invocation) compiler)
    {certificate : GenericExpressionMeaning.Certificate}
    (calleeCertified : certificate scope callee compiler.calleeCode)
    {sourceTypes : List TypeSystem.Ty}
    (tree : DataExpressionSequence.Tree invocation.source certificate scope ids sourceTypes compiler.codes)
    (size : Nat)
    (children : ReflectsBelow bridge context model stages invocation certificate callFaults size)
    (closureChildren : ∀ {mapping world function native bindings parameterCore resultCore}
      (association : Association headers keys bodyRegistry semanticFaults mapping world function native
        bindings parameterCore resultCore),
      ReflectsBelowFor (registry := completion.result.context.registry) (faults := callFaults)
        association (closureTerminals association) functions size)
    (namedChildren : ∀ header (member : header ∈ headers),
      ∀ {child : Staging.Recursive.Scope}, stages.Closure header.function child →
      CallableIndexedOwnedPreparedStagedNamedChildBounds.ReflectsBelow (headers := headers) (keys := keys)
        header model stages child
        (namedTerminals header member).certificate callFaults size) :
    ReflectsAt bridge context model stages invocation (Point scope id lowered) callFaults size := by
  intro current child code point node found parentTyped
    mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees actualTyped initial admitted completed
  obtain ⟨rfl, rfl, rfl⟩ := point
  cases sourceEq
  cases Option.some.inj (found.symm.trans compiler.found)
  obtain ⟨parameter, result, rawTypes, calleeTyped, _argumentsTyped, _bundle, _resultType⟩ :=
    CallableIndexedOwnedPreparedStagedRecursiveCallerSourceReceipts.original_child_types
      compiler port.sourceParent unique parentTyped
  have reported := CallableIndexedOwnedContextualInitializedClosureReceipts.reported_type_at
    unique port.calleeFound calleeTyped
  have sourceTyped : ExpressionHasType invocation.source context callee port.calleeNode.type := by
    simpa only [reported] using calleeTyped
  have occurrence : Staging.Recursive.Occurrence invocation child (.call callee ids (.indirect metadata)) :=
    ⟨compiler.original, lookupExpression?_sound compiler.found, compiler.originalForm,
      port.sourceParent.requirements, port.sourceParent.coercions⟩
  have actualNamedChildren : ∀ header (member : header ∈ headers),
      ∀ {child : Staging.Recursive.Scope},
        (RecursiveNamedPreparedStageScopes.registry stagePrepared).Closure header.function child →
        CallableIndexedOwnedPreparedStagedNamedChildBounds.ReflectsBelow (headers := headers) (keys := keys)
        header model
          (RecursiveNamedPreparedStageScopes.registry stagePrepared) child
          (namedTerminals header member).certificate callFaults size := by
    simpa only [stageEq] using namedChildren
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, _evaluated,
    represented, finalHeaps, maps, worlds, frame, metadataExtended, reached, related, post⟩ :=
    CallableIndexedOwnedPreparedStagedSelectedIndirectTerminalCallBounds.reflects_parent
      bridge receiver compiler port.prepared stagePrepared rfl occurrence initial port.view port.guardFrame
      profile calleeCertified port.calleeFound sourceTyped environments heaps locals agrees actualTyped
      admitted port.caller port.originalUnique port.sourceParent tree unique parentTyped
      wellFormed runtime covers actualFunctionType observations
      stageEq size children closureTerminals closureChildren namedTerminals actualNamedChildren completed (Nat.le_refl _)
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadataExtended, reached, related, post⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedGeneralCallHeadBounds
