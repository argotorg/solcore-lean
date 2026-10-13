import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodTerminalSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles

/-! An actual terminal method with reads, literals and conditional selection
uses the same recursive compiler certificate and original Source typing. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPrimitiveMethodTerminalSupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedPreparedStagedMethodBodyStaticSupport (Packet Support)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)
open CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles (MetadataFor)

def PrimitiveSource (source : TypedSource) : Prop :=
  ∀ id node, source.lookupExpression? id = some node →
    (∃ name resolution, node.form = .reference name resolution) ∨
    (∃ spelling resolution, node.form = .integerLiteral spelling resolution) ∨
    (∃ condition first second, node.form = .conditional condition first second)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {method : ExecutableImplMethods.CheckedMethod}
  (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
  (packet : Packet principal)
  (diagnostic : CallableIndexedOwnedPreparedStagedMethodTerminalSupport.DiagnosticAt principal.cached)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (forms : PrimitiveSource principal.sourceBody.source)
  (metadata : MetadataFor compiled.indexed principal.named principal.sourceBody.source (fun _ => False))
  (tree : GeneralSyntax principal.sourceBody.source packet.expression (fun _ => False))

include diagnostic receiver wellFormed forms metadata tree in
theorem of_child
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
    {stages : Staging.Recursive.Registry} {child : Staging.Recursive.Scope}
    (selected : stages.Closure principal.sourceFunction child) :
    Nonempty (CallableIndexedOwnedPreparedStagedMethodBodyStaticSupport.Child principal packet headers stages child
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) := by
  have sourceEq : child.source = principal.sourceBody.source := stages.source selected
  obtain ⟨node, childFound, rawType, typed⟩ :=
    CallableIndexedOwnedPreparedStagedMethodBodyStaticSupport.child_typed principal packet wellFormed selected
  have found : principal.sourceBody.source.lookupExpression? packet.expression = some node := sourceEq ▸ childFound
  have originalTyped : ExpressionHasType principal.sourceBody.source packet.sourceAt.context packet.expression node.type := sourceEq ▸ typed
  obtain ⟨fuel, ⟨root⟩⟩ := CallableIndexedOwnedPreparedStagedMethodBodyStaticSupport.policy_receipt principal packet
  have profile := CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.recipe_policy_for
    root.compilerPolicy root.selected.callables (fun _ impossible => False.elim impossible)
    metadata (CallablePreparedMethodRuntimeProfileFactory.scope (named := principal.named))
    (principal.cached.diagnostics.reasonAt principal.named.signature.key)
  let certificate := CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.of_method_steps_functions
    compiled.indexed.ancestry.graph.inputs.callable [] root.callables
    packet.sourceAt.unique packet.sourceAt.declarations profile
    (fun id node tree found => metadata.coercions id tree node found) tree found originalTyped root.selected.accepted
  let childCertificate : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.Certificate
      root.selected.policy root.selected.lowerBody (CallableIndexedNamedGeneration.context compiled.indexed principal.named)
      compiled.indexed.fuel (.initial compiled.compatible.checked) child.source packet.sourceAt.context
      (principal.cached.diagnostics.reasonAt principal.named.signature.key)
      (CallablePreparedMethodRuntimeProfileFactory.scope (named := principal.named)) packet.expression packet.receipt.child := by
    simpa only [sourceEq] using certificate
  have noIndirect : CallableIndexedOwnedPreparedStagedMethodRootStaticSupport.NoIndirect
      (compiled := compiled) (invocation := child) childCertificate := by
    intro callFuel callScope callId callee ids callMetadata code compiler _path
    rcases forms callId compiler.original (by simpa only [sourceEq] using compiler.found) with
      ⟨name, resolution, form⟩ | ⟨spelling, resolution, form⟩ | ⟨condition, first, second, form⟩ <;>
      have impossible := compiler.originalForm <;> simp [form] at impossible
  let actual : CallableIndexedOwnedPreparedStagedMethodRootStaticSupport.Root compiled headers stages
      root.selected.policy root.selected.lowerBody (CallableIndexedNamedGeneration.context compiled.indexed principal.named)
      compiled.indexed.fuel packet.sourceAt.context child (principal.cached.diagnostics.reasonAt principal.named.signature.key)
      (CallablePreparedMethodRuntimeProfileFactory.scope (named := principal.named)) packet.expression packet.receipt.child
      principal.sourceBody.resultType (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics) := {
    compilerFuel := fuel + 1
    accepted := by simpa only [sourceEq] using root.selected.accepted
    certificate := childCertificate
    node := node
    found := childFound
    rawResult := rawType
    typed := typed
    sameLedger := packet.sourceAt.valid.ledger
    runtimeLedger := packet.sourceAt.valid.runtime
    unique := by simpa only [sourceEq] using packet.sourceAt.unique
    wellFormed := wellFormed
    runtime := by simpa only [sourceEq] using CallableIndexedOwnedPreparedStagedMethodBodyStaticSupport.runtime principal packet wellFormed
    covers := by rw [stages.evidence selected]; exact packet.sourceAt.valid.covers
    actualFunctionType := by rw [root.callables]; rfl
    uninitialized := by
      intro current id code read _reached location
      exact CallableIndexedOwnedPreparedStagedMethodTerminalSupport.uninitialized principal diagnostic receiver
        packet.sourceAt.unique (by simpa only [sourceEq] using read) location
    callsReady := by
      intro callFuel callScope callId callee ids callMetadata code compiler path
      exact False.elim (noIndirect compiler path)
    directReady := by
      intro callFuel callScope callId callee ids instantiation code compiler _path
      rcases forms callId compiler.node (by simpa only [sourceEq] using compiler.metadata.found) with
        ⟨name, resolution, form⟩ | ⟨spelling, resolution, form⟩ | ⟨condition, first, second, form⟩ <;>
        have impossible := compiler.form <;> simp [form] at impossible
    indexReady := by
      intro indexScope indexId base key actual baseNode keyNode layout comparison first second indexed _keyFound form _sourceType _scalar _path
      rcases forms indexId actual (by simpa only [sourceEq] using indexed.metadata.found) with
        ⟨name, resolution, nodeForm⟩ | ⟨spelling, resolution, nodeForm⟩ | ⟨condition, first, second, nodeForm⟩ <;>
        simp [nodeForm] at form
    methodReady := by
      intro callFuel callScope callId code compiler _path
      rcases forms callId compiler.node (by simpa only [sourceEq] using compiler.metadata.found) with
        ⟨name, resolution, nodeForm⟩ | ⟨spelling, resolution, nodeForm⟩ | ⟨condition, first, second, nodeForm⟩
      all_goals
        rcases compiler.operator.form with ⟨op, operand, form, _arguments⟩ | ⟨op, left, right, form, _arguments⟩ <;>
          simp [nodeForm] at form
    noIndirect := noIndirect }
  exact ⟨⟨CallableIndexedOwnedPreparedStagedMethodRootStaticSupport.RootAt.ofRoot actual, rfl, rfl, rfl⟩⟩

include diagnostic receiver wellFormed forms metadata tree in
theorem of_actual
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
    {stages : Staging.Recursive.Registry} :
    Support principal packet headers stages
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics) :=
  ⟨fun _ selected => of_child principal packet diagnostic receiver wellFormed forms metadata tree selected⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPrimitiveMethodTerminalSupport
