import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedIndirectTerminalPreservationDispatch
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedIndirectTerminalReflectionDispatch
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedClosureUserDispatch

/-! The original caller prefix classifies fault, builtin, closure and global
branches once. Mixed closure packets retain their exact Association and static
support; strict Root children use the same parent budget. Authentic named
global prefixes and every reached state remain the existing contracts. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedIndirectDispatch
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters (Prepared)
open CallableIndexedOwnedContextualDiagnosticSources (SourceView)
open CallableIndexedOwnedPublicFaultReceiverTables (IssuedAt)
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)
open CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport (PacketFor SupportFor)
open CallableIndexedOwnedPreparedStagedIndirectBuiltinPreservationDispatch (ParentAt)
open CallableIndexedOwnedPreparedStagedIndirectBuiltinApplicationDispatch (ParentResult)
open CallableIndexedOwnedPreparedStagedTerminalClosureUserDispatch (GlobalApplicationPrefix)
open CallableIndexedOwnedPreparedStagedTerminalClosureUserPreservationDispatch (GlobalAppliedPrefix)
open CallableIndexedOwnedPreparedStagedIndirectTerminalPreservationDispatch (GlobalAt)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
    completion.result.extension completion.result.diagnostics)
  {context : SourceSemantics.Context}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}

section Calls
variable {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  (prepared : Prepared compiler compiled.indexed.ancestry.graph.inputs.callable)
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)
  (sourceEq : invocation.source = source)
  (occurrence : Staging.Recursive.Occurrence invocation id (.call callee ids (.indirect metadata)))
  {calleeNode : ExpressionNode}
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  {sidecar : SourceCoreStageContracts.Sidecar}
  (view : SourceView sidecar.source source)
  (guardFrame : invocation.guards = CallableLedger.frame sidecar)

section PositiveModel
variable {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {certificate : GenericExpressionMeaning.Certificate}
  (certified : certificate scope callee compiler.calleeCode)
  (found : source.lookupExpression? callee = some calleeNode)
  (sourceTyped : ExpressionHasType source context callee calleeNode.type)
  {administrative actualContext : Core.Context}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked completion.result.context.registry
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile)
    mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (admitted : Admission bridge context initial)
  (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (originalUnique : NodeOccurrencesUnique sidecar.source)
  (sourceParent : CallableIndexedOwnedIndirectSourceAdapters.SourceParent compiler)
  {sourceTypes : List TypeSystem.Ty}
  (tree : DataExpressionSequence.Tree invocation.source certificate scope ids sourceTypes compiler.codes)
  (unique : NodeOccurrencesUnique invocation.source)
  (parentTyped : ExpressionHasType invocation.source context id compiler.original.type)

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys
  bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked
  completion.result.context.registry functions
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
  completion.result.diagnostics


variable (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
  (covers : invocation.evidence.Covers context)
  (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile) identities)

include receiver prepared stagePrepared sourceEq occurrence certified found sourceTyped
  environments heaps locals agrees typed admitted caller view originalUnique guardFrame
  sourceParent tree unique parentTyped wellFormed runtime covers actualFunctionType observations in
/-- One original Source parent constructs its complete native result or
retains the authentic named suffix. The concrete call producers reuse the
literal callee and argument evaluations and their reached pool. -/
theorem preserves_parent_or_global (budget : Nat)
    (children : CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow
      bridge context model stages invocation certificate callFaults budget)
    (packets : ∀ {mapping world function native bindings parameterCore resultCore}
      (association : Association headers keys bodyRegistry semanticFaults mapping world function native
        bindings parameterCore resultCore), PacketFor association stages)
    (supported : ∀ {mapping world function native bindings parameterCore resultCore}
      (association : Association headers keys bodyRegistry semanticFaults mapping world function native
        bindings parameterCore resultCore), SupportFor association stages (packets association))
    (bodyChildren : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.PreservesRootsAt
        (completion := completion) (stages := stages) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile childSize)
    {size : Nat} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages size
      invocation context environment before id outcome after)
    (within : size ≤ budget) :
    ParentAt (completion := completion) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (stages := stages) (invocation := invocation) (environment := environment)
      (actual := actual) (ξ := ξ) bridge profile compiler initial size outcome after ∨
    GlobalAt (completion := completion) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (stages := stages) (invocation := invocation) (environment := environment)
      (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes) (calleeNode := calleeNode) (sidecar := sidecar)
      bridge (profile := profile) compiler prepared initial budget size outcome after := by
  rcases CallableIndexedOwnedPreparedStagedIndirectSourcePrefixDispatch.preserves_fault_or_application
      bridge profile compiler prepared sourceEq occurrence certified found sourceTyped
      environments heaps locals agrees typed initial admitted caller view originalUnique guardFrame
      sourceParent tree unique parentTyped stagePrepared receiver budget children trace within with fault | application
  · exact .inl ⟨trace, fault⟩
  · obtain ⟨calleeSize, argumentsSize, applicationSize, sourceValue, calleeHeap, argumentsHeap,
      sources, sizeEq, strict, calleeTrace, accepted, argumentsTrace, called, constructedPrefix⟩ := application
    cases sizeEq
    rcases CallableIndexedOwnedPreparedStagedIndirectBuiltinPreservationDispatch.preserves_builtin_or_user
        bridge profile compiler prepared initial sourceParent occurrence stagePrepared receiver
        actualFunctionType observations calleeTrace accepted argumentsTrace called constructedPrefix with user | parent
    · rcases CallableIndexedOwnedPreparedStagedMixedClosureUserDispatch.preserves_closure_or_global
          bridge profile compiler prepared initial sourceParent occurrence stagePrepared receiver
          wellFormed runtime covers locals sourceEq tree unique parentTyped found guardFrame actualFunctionType
          packets supported budget bodyChildren user.1 calleeTrace accepted argumentsTrace called (Nat.le_of_lt strict)
          user.2 with closureParent | global
      · exact .inl closureParent
      · exact .inr ⟨calleeSize, argumentsSize, applicationSize, sourceValue, calleeHeap,
          argumentsHeap, sources, rfl, strict, global⟩
    · exact .inl parent

include receiver prepared stagePrepared sourceEq occurrence certified found sourceTyped
  environments heaps locals agrees typed admitted caller view originalUnique guardFrame
  sourceParent tree unique parentTyped wellFormed runtime covers actualFunctionType observations in
/-- One original native parent completion either gives full Source parent
meaning or retains its actual named application prefix. Concrete call branches
share the same reached state; no caller or argument trace is replayed. -/
theorem reflects_parent_or_global (budget : Nat)
    (children : CallableIndexedOwnedAdmittedStagedExpressionBounds.ReflectsBelow
      bridge context model stages invocation certificate callFaults budget)
    (packets : ∀ {mapping world function native bindings parameterCore resultCore}
      (association : Association headers keys bodyRegistry semanticFaults mapping world function native
        bindings parameterCore resultCore), PacketFor association stages)
    (supported : ∀ {mapping world function native bindings parameterCore resultCore}
      (association : Association headers keys bodyRegistry semanticFaults mapping world function native
        bindings parameterCore resultCore), SupportFor association stages (packets association))
    (bodyChildren : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.ReflectsRootsAt
        (completion := completion) (stages := stages) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile childSize)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore)
    (within : size ≤ budget) :
    ParentResult (completion := completion) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (stages := stages) (invocation := invocation) (environment := environment)
      (actual := actual) (ξ := ξ) bridge profile compiler initial value finalStore ∨
    GlobalApplicationPrefix (completion := completion) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (stages := stages) (invocation := invocation) (environment := environment)
      (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes) (calleeNode := calleeNode) (sidecar := sidecar)
      bridge profile compiler prepared initial budget value finalStore := by
  rcases CallableIndexedOwnedPreparedStagedIndirectRetainedCalleeFaultDispatch.reflects_fault_or_application
      bridge receiver compiler prepared stagePrepared sourceEq occurrence initial view guardFrame profile
      certified found sourceTyped environments heaps locals agrees typed admitted caller originalUnique
      sourceParent tree unique parentTyped budget children completed within with fault | application
  · obtain ⟨sourceSize, failure, after, token, finalMap, finalWorld, trace, valueEq,
      native, represented, finalHeaps, maps, worlds, frame, metadata,
      returned, related, post⟩ := fault
    cases valueEq
    exact .inl ⟨sourceSize, .fault failure, after, finalMap, finalWorld, trace, native,
      represented, finalHeaps, maps, worlds, frame, metadata, returned, related, post⟩
  · rcases CallableIndexedOwnedPreparedStagedIndirectBuiltinApplicationDispatch.reflects_builtin_or_user
        bridge profile compiler prepared initial sourceParent occurrence stagePrepared receiver
        actualFunctionType observations completed application with user | parent
    · exact CallableIndexedOwnedPreparedStagedMixedClosureUserDispatch.reflects_closure_or_global
        bridge profile compiler prepared initial sourceParent occurrence stagePrepared receiver
        wellFormed runtime covers locals sourceEq tree unique parentTyped found actualFunctionType
        packets supported bodyChildren completed user
    · exact .inl parent

end PositiveModel
end Calls
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedIndirectDispatch
