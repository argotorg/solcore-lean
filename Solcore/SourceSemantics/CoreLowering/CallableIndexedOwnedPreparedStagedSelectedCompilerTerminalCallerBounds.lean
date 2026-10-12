import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedCallerFromRecursiveBodies
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedBodySupportFactories

/-! Compiler terminal callers consume the constructive recursive body family.
Each chosen Association/Header packet is bundled with its original static
authority and the reachable-call authority of its exact issued certificate.
Selectors and body support are constructed internally from those bundles.
The public terminal endpoints issue their own original Root before invoking
the checked caller family; they accept no expression/body execution law.

Actual callback, policy, declaration, typing, diagnostic and CallsReady links
remain static inputs at the literal chosen packet and original caller scope.
Independent grades and full returned caller admission use the checked family.
-/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedCompilerTerminalCallerBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedPublicFaultReceiverTables (IssuedAt)
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)
open CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds (TerminalFor)
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)
open CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport (RootAt ClosureSupportFor NamedSupport)
open CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds (Point)
open CallableIndexedOwnedAdmittedStagedExpressionBounds
universe u

section Static
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {stages : Staging.Recursive.Registry}

/-- One original contextual Association retains its actual Code and parameter
context. Ready refers only to certificates issued from this same packet. -/
structure ClosurePacket {mapping : LocationMap} {world : StoreTyping}
    {function : Dynamic.Closure} {native : Value}
    {bindings : List CallableIndexedParameterCertificates.Binding}
    {parameterCore resultCore : Ty}
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore) where
  terminal : TerminalFor association stages
  authority : CallableIndexedOwnedPreparedStagedSelectedBodySupportFactories.ClosureAuthorityFor
    association terminal
  ready : CallableIndexedOwnedPreparedStagedSelectedBodySupportFactories.ClosureReadyFor
    association terminal authority

/-- A chosen Header retains its literal terminal receipt and original static
compiler conditions for every genuine Source-selected body scope. -/
structure NamedPacket
    (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)) where
  terminal : Terminal header
  authority : CallableIndexedOwnedPreparedStagedSelectedBodySupportFactories.NamedAuthority
    header terminal (stages := stages) (semanticFaults := semanticFaults)
  ready : CallableIndexedOwnedPreparedStagedSelectedBodySupportFactories.NamedReady authority

/-- This is a static factory family, not a family of executions. It neither
equates Association contexts nor quantifies over arbitrary terminal certificates. -/
structure FactoryFamily where
  closures : ∀ {mapping world function native bindings parameterCore resultCore}
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore), ClosurePacket (stages := stages) association
  named : ∀ header, header ∈ headers →
    NamedPacket (stages := stages) (semanticFaults := semanticFaults) header

variable (factories : FactoryFamily (headers := headers) (keys := keys)
  (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) (stages := stages))

/-- Only the certificate is narrowed. The chosen Code, receipt, child and
physical parameter scope remain those of the original Association packet. -/
def closure_terminals {mapping world function native bindings parameterCore resultCore}
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore) : TerminalFor association stages :=
  CallableIndexedOwnedPreparedStagedSelectedTerminalCertificates.closureFor
    association (factories.closures association).terminal

/-- The same Header membership chooses the packet and all of its support. -/
def named_terminals
    (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
    (member : header ∈ headers) : Terminal header :=
  CallableIndexedOwnedPreparedStagedSelectedTerminalCertificates.named
    header (factories.named header member).terminal

/-- Original raw typing and acceptance are manufactured by the authentic
factory at every selected body scope. No body meaning is stored in the bundle. -/
def closure_support {mapping world function native bindings parameterCore resultCore}
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore) :
    ClosureSupportFor association stages (closure_terminals factories association) :=
  CallableIndexedOwnedPreparedStagedSelectedBodySupportFactories.closure_support_for
    association (factories.closures association).terminal
    (factories.closures association).authority (factories.closures association).ready

/-- Named support uses the original Header source and the same chosen packet;
it does not infer an expression callback from the Header's statement policy. -/
def named_support
    (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
    (member : header ∈ headers) :
    NamedSupport header stages (named_terminals factories header member) semanticFaults :=
  CallableIndexedOwnedPreparedStagedSelectedBodySupportFactories.named_support
    (factories.named header member).authority (factories.named header member).ready
end Static

section Meaning
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
  (factories : FactoryFamily (headers := headers) (keys := keys)
    (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) (stages := stages))

include bridge receiver stagePrepared observations extension semantic factories in
private theorem preserves_issued {context invocation scope expression lowered}
    (root : RootAt compiled context invocation scope expression lowered semanticFaults) (size : Nat) :
    PreservesAt bridge context
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry
        (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile))
      stages invocation (Point scope expression lowered)
      (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics) size := by
  exact CallableIndexedOwnedPreparedStagedSelectedCallerFromRecursiveBodies.preserves
    (bridge := bridge) (receiver := receiver) (stagePrepared := stagePrepared)
    (profile := profile) (observations := observations) (extension := extension) (semantic := semantic)
    (closureTerminals := closure_terminals factories) (namedTerminals := named_terminals factories)
    (closureSupport := closure_support factories) (namedSupport := fun header member => .recursive (named_support factories header member)) root size

include bridge receiver stagePrepared observations extension semantic factories in
private theorem reflects_issued
    (stageEq : stages = RecursiveNamedPreparedStageScopes.registry stagePrepared)
    {context invocation scope expression lowered}
    (root : RootAt compiled context invocation scope expression lowered semanticFaults) (size : Nat) :
    ReflectsAt bridge context
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry
        (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile))
      stages invocation (Point scope expression lowered)
      (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics) size := by
  exact CallableIndexedOwnedPreparedStagedSelectedCallerFromRecursiveBodies.reflects
    (bridge := bridge) (receiver := receiver) (stagePrepared := stagePrepared)
    (profile := profile) (observations := observations) (extension := extension) (semantic := semantic)
    (closureTerminals := closure_terminals factories) (namedTerminals := named_terminals factories)
    (closureSupport := closure_support factories) (namedSupport := fun header member => .recursive (named_support factories header member)) stageEq root size

section Closure
variable {function : Dynamic.Closure} {localScope : SourceCoreLocalCell.Scope}
  {administrative : Core.Context}
  {code : Code compiled.indexed function localScope administrative}
  {inputs : CallableIndexedLambdaEntryPrefix.Context
    (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
    (prepared := compiled.indexed) code}
  {packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.Terminal code stages}

include bridge receiver stagePrepared observations extension semantic factories in
/-- Frame typing, the actual terminal compiler action and original-source
transport construct this caller root internally at the literal parameter entry. -/
theorem preserves_closure
    (authority : CallableIndexedOwnedPreparedStagedSelectedBodySupportFactories.ClosureAuthority
      code inputs packet (semanticFaults := semanticFaults))
    (ready : CallableIndexedOwnedPreparedStagedSelectedBodySupportFactories.ClosureReady authority)
    (child : Staging.Recursive.Scope) (selected : stages.Closure function child) (size : Nat) :
    PreservesAt bridge inputs.context
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry
        (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile))
      stages child
      (Point (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ localScope)
        packet.expression packet.receipt.child)
      (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics) size := by
  let support := CallableIndexedOwnedPreparedStagedSelectedBodySupportFactories.selected_body authority ready
  have root : RootAt compiled inputs.context child
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ localScope)
      packet.expression packet.receipt.child semanticFaults := by
    simpa only [CallableIndexedOwnedPreparedStagedSelectedTerminalCertificates.closure,
      CallableIndexedOwnedPreparedTerminalClosureUsedChildBounds.narrow] using support.rootAt child selected
  intro current id lowered certified
  exact preserves_issued (bridge := bridge) (receiver := receiver) (stagePrepared := stagePrepared)
    (profile := profile) (observations := observations) (extension := extension) (semantic := semantic) (factories := factories)
    root size certified

include bridge receiver stagePrepared observations extension semantic factories in
/-- Reflection keeps its own native grade and authentic selected Source scope;
the independent Source grade and full returned post come from the checked family. -/
theorem reflects_closure
    (stageEq : stages = RecursiveNamedPreparedStageScopes.registry stagePrepared)
    (authority : CallableIndexedOwnedPreparedStagedSelectedBodySupportFactories.ClosureAuthority
      code inputs packet (semanticFaults := semanticFaults))
    (ready : CallableIndexedOwnedPreparedStagedSelectedBodySupportFactories.ClosureReady authority)
    (child : Staging.Recursive.Scope) (selected : stages.Closure function child) (size : Nat) :
    ReflectsAt bridge inputs.context
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry
        (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile))
      stages child
      (Point (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ localScope)
        packet.expression packet.receipt.child)
      (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics) size := by
  let support := CallableIndexedOwnedPreparedStagedSelectedBodySupportFactories.selected_body authority ready
  have root : RootAt compiled inputs.context child
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ localScope)
      packet.expression packet.receipt.child semanticFaults := by
    simpa only [CallableIndexedOwnedPreparedStagedSelectedTerminalCertificates.closure,
      CallableIndexedOwnedPreparedTerminalClosureUsedChildBounds.narrow] using support.rootAt child selected
  intro current id lowered certified
  exact reflects_issued (bridge := bridge) (receiver := receiver) (stagePrepared := stagePrepared)
    (profile := profile) (observations := observations) (extension := extension) (semantic := semantic) (factories := factories)
    stageEq root size certified
end Closure

section Named
variable {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  {packet : Terminal header}

include bridge receiver stagePrepared observations extension semantic factories in
/-- The actual Header source, ordered physical bindings and terminal receipt
issue the named root before recursive caller/body meaning is invoked. -/
theorem preserves_named
    (authority : CallableIndexedOwnedPreparedStagedSelectedBodySupportFactories.NamedAuthority
      header packet (stages := stages) (semanticFaults := semanticFaults))
    (ready : CallableIndexedOwnedPreparedStagedSelectedBodySupportFactories.NamedReady authority)
    (child : Staging.Recursive.Scope) (selected : stages.Closure header.function child) (size : Nat) :
    PreservesAt bridge header.context
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry
        (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile))
      stages child
      (Point (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
        packet.expression packet.receipt.child)
      (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics) size := by
  let support := CallableIndexedOwnedPreparedStagedSelectedBodySupportFactories.named_support authority ready
  have root : RootAt compiled header.context child
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      packet.expression packet.receipt.child semanticFaults := by
    simpa only [CallableIndexedOwnedPreparedStagedSelectedTerminalCertificates.named] using
      (support.roots child selected).val
  intro current id lowered certified
  exact preserves_issued (bridge := bridge) (receiver := receiver) (stagePrepared := stagePrepared)
    (profile := profile) (observations := observations) (extension := extension) (semantic := semantic) (factories := factories)
    root size certified

include bridge receiver stagePrepared observations extension semantic factories in
/-- The chosen Header and returned child pool stay literal. Registry equality
is required only for reflection; no Source/native grade equality is introduced. -/
theorem reflects_named
    (stageEq : stages = RecursiveNamedPreparedStageScopes.registry stagePrepared)
    (authority : CallableIndexedOwnedPreparedStagedSelectedBodySupportFactories.NamedAuthority
      header packet (stages := stages) (semanticFaults := semanticFaults))
    (ready : CallableIndexedOwnedPreparedStagedSelectedBodySupportFactories.NamedReady authority)
    (child : Staging.Recursive.Scope) (selected : stages.Closure header.function child) (size : Nat) :
    ReflectsAt bridge header.context
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry
        (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile))
      stages child
      (Point (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
        packet.expression packet.receipt.child)
      (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics) size := by
  let support := CallableIndexedOwnedPreparedStagedSelectedBodySupportFactories.named_support authority ready
  have root : RootAt compiled header.context child
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      packet.expression packet.receipt.child semanticFaults := by
    simpa only [CallableIndexedOwnedPreparedStagedSelectedTerminalCertificates.named] using
      (support.roots child selected).val
  intro current id lowered certified
  exact reflects_issued (bridge := bridge) (receiver := receiver) (stagePrepared := stagePrepared)
    (profile := profile) (observations := observations) (extension := extension) (semantic := semantic) (factories := factories)
    stageEq root size certified
end Named
end Meaning

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedCompilerTerminalCallerBounds
