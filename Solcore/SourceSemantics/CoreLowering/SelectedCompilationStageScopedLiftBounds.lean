import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageBodyLiftBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedConditionalHeads

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageScopedLiftBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open SelectedCompilationStageBodyLiftBounds
universe u

/-- The original function and scoped statement relations retain their distinct
execution modes and all ordinary control outcomes. -/
def PlainStatements (program : Program) (mode : Bool) (size : Nat)
    (invocation : Staging.Recursive.Scope) (context : SourceSemantics.Context)
    (environment : Dynamic.Environment) (before : Dynamic.Heap) (statements : List StatementId)
    (finalContext : SourceSemantics.Context) (outcome : Dynamic.ControlOutcome)
    (after : Dynamic.Heap) : Prop :=
  if mode then RecursiveNamedCallBounds.FunctionOutcome program size context invocation.evidence
    invocation.source environment before statements finalContext outcome after
  else RecursiveNamedCallBounds.StatementsOutcome program size context invocation.evidence
    invocation.source environment before statements finalContext outcome after

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

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions

/-- A scoped compiler child starts at its genuine physical entry. Every
recursive use is discharged by the internal sized body induction. -/
def FlowLifts (context : SourceSemantics.Context) (scope : SourceCoreLocalCell.Scope) (mode : Bool)
    (statements : List StatementId) (budget : Nat) : Prop :=
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
    ∀ {finalContext : SourceSemantics.Context} {outcome : Dynamic.ControlOutcome} {after : Dynamic.Heap},
      PlainStatements program mode size invocation context environment before
        statements finalContext outcome after →
    BodyLift program stages mode invocation context environment before statements
      finalContext outcome after

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageScopedLiftBounds
