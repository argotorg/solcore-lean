import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedBranchingTerminalChoice
import Solcore.SourceSemantics.CoreLowering.CallableMethodBodyCoherence
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedBranchingCoercedDirectRoots
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalClosureStaticSupport

/-! The authentic retained terminal callback yields an original coerced root
at every selected Source scope. Body-view transport keeps the complete parent
node and composes the actual ordered argument compiler actions. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3200000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedBranchingCoercedTerminalSupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)
open CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles (NativeMetadataFor)
open CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds (Terminal)
open SelectedCompilationPhysicalClosureStaticSupport (SelectedBody)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled compiled.indexed.ancestry.graph.inputs.callable)
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (code : Code compiled.indexed function scope administrative)
  (support : PreparedLambdaBodySupport.Support code)
  (provenance : PreparedLambdaBodySupport.PreparedAt code support)
  (callerReceipt : CallableIndexedOwnedOrdinaryCallerReceipts.CallerAt support.caller function.context function.evidence)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (bodies : SelectedCompilationBodyTyping.Bodies compiled)
  (certified : SelectedCompilationNamedSourceTyping.Certified support.caller)
  (metadata : NativeMetadataFor compiled.indexed support.caller.named function.source (fun _ => False))
  {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled)}
  (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
    (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
  (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
  (methods : CallableIndexedOwnedPreparedStagedClosedCoercionSelection.Catalog compiled)
  {signature : ProgramFunctionSignature} (signatureMember : signature ∈ compiled.sourceProgram.signatures.functions)
  (sourceOwner : function.source.owner = signature.id)

local notation "stages" => RecursiveNamedPreparedStageScopes.registry stagePrepared
local notation "faults" => CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics
local notation "headers" => CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows



include receiver bodies certified metadata rows checked catalog methods signatureMember sourceOwner provenance callerReceipt in
theorem of_actual
    (methodBodies : ∀ {method : ExecutableImplMethods.CheckedMethod} (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
    (sourceAt : CallablePreparedMethodRuntimeProfileFactory.SourceAt principal.cached.compilation
      (.initial compiled.compatible.checked) principal.sourceBody principal.dictionary)
    (_diagnostic : CallableIndexedOwnedPreparedStagedMethodTerminalSupport.DiagnosticAt principal.cached)
    (_certified : SelectedCompilationMethodBodySupport.Certified principal sourceAt),
    ∃ packet : SelectedCompilationMethodBodySupport.Packet principal,
      packet.sourceAt = sourceAt ∧ SelectedCompilationMethodBodySupport.Support
        principal packet (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
        (RecursiveNamedPreparedStageScopes.registry stagePrepared)
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics))

    (expression : ExpressionId)
    (terminal : CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Terminal
      function.source expression function.body)
    {node : ExpressionNode} {callee : ExpressionId} {ids : List ExpressionId}
    {instantiation : DeclarationInstantiation}
    (found : function.source.lookupExpression? expression = some node)
    (form : node.form = .call callee ids (.declaration instantiation))
    (nonempty : node.coercions ≠ []) (requirements : node.requirements ≠ [])
    (children : ∀ argument ∈ ids, GeneralSyntax function.source argument (fun _ => False))
    (noInitializer : compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (CallableIndexedNamedGeneration.context compiled.indexed support.caller.named).owner ∧
        binding.initializer = expression)) = none)
    (supported : CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported code.compilation.plan instantiation)
    (covered : ∀ index signature,
      SourceCompilationPlan.exactInstantiationKey code.compilation.plan instantiation = .ok signature.key →
      code.compilation.globals[index]? = some signature →
      ∃ header ∈ headers, header.slot = index ∧ header.named.signature = signature)
    (child : Staging.Recursive.Scope) (selected : (stages).Closure function child) :
    Nonempty (Σ packet : Terminal code stages,
      SelectedBody («headers» := headers) code support.body.toContext stages packet faults) := by
  obtain ⟨packet, expressionEq, callback, reason, _child, point, prefixEq⟩ :=
    SelectedCompilationPreparedBranchingTerminalChoice.of_actual code support provenance
      expression terminal child selected
  subst expression
  refine ⟨⟨packet, { point := point, readFuel := compiled.indexed.fuel, «prefix» := prefixEq, roots := ?_ }⟩⟩
  intro selectedChild selectedAt
  apply Classical.choice
  have sameSource := (stages).source selectedAt
  have declarations := CallableIndexedOwnedPreparedLambdaScopeDeclarations.at_selected_scope
    (values := .initial compiled.compatible.checked) code support.body.toContext support.body.frame
    provenance.scope_declarations selectedAt
  obtain ⟨actualNode, actualFound, rawType, typed⟩ :=
    CallableIndexedOwnedPreparedStagedSelectedBodyCompilerRoots.terminal_raw_type
      code packet support.body.toContext support.body.frame selectedChild selectedAt
  have originalFound : function.source.lookupExpression? packet.expression = some actualNode := by
    simpa only [sameSource] using actualFound
  cases Option.some.inj (originalFound.symm.trans found)
  have reached := CallableIndexedOwnedPreparedStagedSelectedBodyCompilerRoots.terminal_reached code packet
  have accepted := CallableIndexedOwnedPreparedStagedSelectedBodyCompilerRoots.accepted_view_action code packet callback reason
  have callables : code.policy.callables = SourceCoreGeneralFunctions.callablePolicy compiled.indexed.base.callableContext [] := by
    rw [code.callables, support.active, compiled.indexed.ancestry.graph.inputs.callableSelected]
  generalize fuelEq : min packet.receipt.childFuel code.fuel = fuel at accepted
  cases fuel with
  | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
  | succ fuel =>
      have original := CallableIndexedOwnedPreparedStagedCoercedBodyViewTransport.accepted_original
        code provenance.policy_recipe provenance.body_view callables
        (CallableIndexedOwnedPreparedStagedGeneralCallerEvidenceProfiles.MetadataFor.of_native metadata)
        noInitializer found form requirements children reached accepted
      obtain ⟨root⟩ := SelectedCompilationPreparedBranchingCoercedDirectRoots.of_original_child
        stagePrepared code support provenance callerReceipt receiver bodies certified metadata rows checked catalog methods
        signatureMember sourceOwner methodBodies selectedAt (Dynamic.RuntimeContextFields.refl _)
        (by simpa only [sameSource] using declarations) children reached found form nonempty requirements
        noInitializer supported covered (by simpa only [sameSource] using typed) original
      refine ⟨.coercedDirect ?_⟩
      simpa only [rawType] using root

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedBranchingCoercedTerminalSupport
