import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectTerminalCallBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedIndirectTerminalReflectionDispatch
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedIndirectTerminalPreservationDispatch
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedTerminalNamedGlobalDispatch


import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectTerminalReflectionDispatch
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectTerminalPreservationDispatch
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch

/-! Internal chosen-terminal dispatch for the eventual numeric body family.
The static factory selects one genuine packet; the body hypothesis belongs to
that packet alone. Existing failure, physical arity, parameter/body execution
and saved caller restoration proofs retain their original indices. Original
Source typing and compiler-policy transport remain separate static obligations.
-/
/-! Whole terminal indirect calls construct both directions of the original
parent meaning. Existing failure, builtin and closure producers retain their
actual traces; the authentic named producer consumes the global branch once.
Static terminal coverage and strict child expression meaning remain explicit. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedIndirectTerminalCallBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters (Prepared)
open CallableIndexedOwnedContextualDiagnosticSources (SourceView)
open CallableIndexedOwnedPublicFaultReceiverTables (IssuedAt)
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)
open CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds (TerminalFor ReflectsBelowFor)
open CallableIndexedOwnedPreparedStagedIndirectBuiltinApplicationDispatch (ParentResult)
open CallableIndexedOwnedPreparedStagedTerminalClosureParentPreservation (PreservesBelowFor)
open CallableIndexedOwnedPreparedStagedIndirectBuiltinPreservationDispatch (ParentAt)
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {completion : SourceCoreCallableIndexedPrograms.Completion compiled.indexed}
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
local notation "poolBridge" => CallableIndexedOwnedBodyRestorationAdmission.bridge (headers := headers) (keys := keys)
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
/-- One original native completion gives full staged Source parent meaning,
including the actual named global branch and restored caller post. -/
theorem reflects_parent
    (stageEq : stages = RecursiveNamedPreparedStageScopes.registry stagePrepared)
    (budget : Nat)
    (children : CallableIndexedOwnedAdmittedStagedExpressionBounds.ReflectsBelow
      bridge context model stages invocation certificate callFaults budget)
    (closureTerminals : ∀ {mapping world function native bindings parameterCore resultCore}
      (association : Association headers keys bodyRegistry semanticFaults mapping world function native
        bindings parameterCore resultCore), TerminalFor association stages)
    (closureChildren : ∀ {mapping world function native bindings parameterCore resultCore}
      (association : Association headers keys bodyRegistry semanticFaults mapping world function native
        bindings parameterCore resultCore),
      ReflectsBelowFor (registry := completion.result.context.registry) (faults := callFaults)
        association (closureTerminals association) functions budget)
    (namedTerminals : ∀ header, header ∈ headers → Terminal header)
    (namedChildren : ∀ header, ∀ member : header ∈ headers,
      ∀ {child : Staging.Recursive.Scope},
        (RecursiveNamedPreparedStageScopes.registry stagePrepared).Closure header.function child →
        CallableIndexedOwnedPreparedStagedNamedChildBounds.ReflectsBelow (headers := headers) (keys := keys)
        header model (RecursiveNamedPreparedStageScopes.registry stagePrepared)
          child (namedTerminals header member).certificate callFaults budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore)
    (within : size ≤ budget) :
    ParentResult (completion := completion) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (stages := stages) (invocation := invocation) (environment := environment)
      (actual := actual) (ξ := ξ) bridge profile compiler initial value finalStore := by
  rcases CallableIndexedOwnedPreparedStagedSelectedIndirectTerminalReflectionDispatch.reflects_parent_or_global
      bridge receiver compiler prepared stagePrepared sourceEq occurrence initial view guardFrame profile
      certified found sourceTyped environments heaps locals agrees typed admitted caller originalUnique
      sourceParent tree unique parentTyped wellFormed runtime covers actualFunctionType observations
      budget children closureTerminals closureChildren completed within with parent | global
  · exact parent
  · exact CallableIndexedOwnedPreparedStagedSelectedTerminalNamedGlobalDispatch.reflects_global
      bridge profile compiler prepared initial sourceParent occurrence stagePrepared stageEq caller receiver
      wellFormed runtime covers locals sourceEq tree unique parentTyped found actualFunctionType
      namedTerminals namedChildren completed global

include receiver prepared stagePrepared sourceEq occurrence certified found sourceTyped
  environments heaps locals agrees typed admitted caller view originalUnique guardFrame
  sourceParent tree unique parentTyped wellFormed runtime covers actualFunctionType observations in
/-- One original staged Source parent constructs its native completion and
full caller post. The authentic named branch uses its actual strict application
child; Source and native grades remain independent. -/
theorem preserves_parent (budget : Nat)
    (children : CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow
      bridge context model stages invocation certificate callFaults budget)
    (closureTerminals : ∀ {mapping world function native bindings parameterCore resultCore}
      (association : Association headers keys bodyRegistry semanticFaults mapping world function native
        bindings parameterCore resultCore), TerminalFor association stages)
    (closureChildren : ∀ {mapping world function native bindings parameterCore resultCore}
      (association : Association headers keys bodyRegistry semanticFaults mapping world function native
        bindings parameterCore resultCore),
      PreservesBelowFor (registry := completion.result.context.registry) (faults := callFaults)
        association (closureTerminals association) functions budget)
    (namedTerminals : ∀ header, header ∈ headers → Terminal header)
    (namedChildren : ∀ header, ∀ member : header ∈ headers,
      ∀ {child : Staging.Recursive.Scope}, stages.Closure header.function child →
        CallableIndexedOwnedPreparedStagedNamedChildBounds.PreservesBelow (headers := headers) (keys := keys)
        header model stages child (namedTerminals header member).certificate callFaults budget)
    {size : Nat} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages size
      invocation context environment before id outcome after)
    (within : size ≤ budget) :
    ParentAt (completion := completion) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (stages := stages) (invocation := invocation) (environment := environment)
      (actual := actual) (ξ := ξ) bridge profile compiler initial size outcome after := by
  rcases CallableIndexedOwnedPreparedStagedSelectedIndirectTerminalPreservationDispatch.preserves_parent_or_global
      bridge receiver compiler prepared stagePrepared sourceEq occurrence initial view guardFrame profile
      certified found sourceTyped environments heaps locals agrees typed admitted caller originalUnique
      sourceParent tree unique parentTyped wellFormed runtime covers actualFunctionType observations
      budget children closureTerminals closureChildren trace within with parent | global
  · exact parent
  · obtain ⟨calleeSize, argumentsSize, applicationSize, sourceValue, calleeHeap, argumentsHeap,
      sources, sizeEq, strict, globalPrefix⟩ := global
    cases sizeEq
    exact CallableIndexedOwnedPreparedStagedSelectedTerminalNamedGlobalDispatch.preserves_global
      bridge profile compiler prepared initial sourceParent occurrence stagePrepared caller receiver
      wellFormed runtime covers locals sourceEq tree unique parentTyped found actualFunctionType
      namedTerminals guardFrame budget namedChildren globalPrefix (Nat.le_of_lt strict)

end PositiveModel
end Calls
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedIndirectTerminalCallBounds
