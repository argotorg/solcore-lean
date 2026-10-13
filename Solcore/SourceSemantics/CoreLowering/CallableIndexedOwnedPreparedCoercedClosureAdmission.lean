import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPrimitiveSourceAdmission
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedSyntaxAdmission
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinaryCoercedTerminalSupport

/-! Finite checks retain each original lambda body and its constrained direct
call. The original coercion rows and captured Source remain unchanged. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 3200000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCoercedClosureAdmission
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedNamedSyntaxAdmission (DirectSite TableAligned)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)

private def allProof? {α : Type} (predicate : α → Prop)
    (check : (item : α) → Option (PLift (predicate item))) :
    (items : List α) → Option (PLift (∀ item ∈ items, predicate item))
  | [] => some ⟨by intro item member; cases member⟩
  | first :: rest => do
      let ⟨head⟩ ← check first
      let ⟨tail⟩ ← allProof? predicate check rest
      pure ⟨by
        intro item member
        rcases List.mem_cons.mp member with same | member
        · exact same ▸ head
        · exact tail item member⟩

structure BodyCertificate (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function)
    (directRows : List SourceSpecialization.SpecializedFunction) (body : List StatementId) where
  expression : ExpressionId
  node : ExpressionNode
  callee : ExpressionId
  arguments : List ExpressionId
  instantiation : DeclarationInstantiation
  terminal : CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Terminal
    named.specialized.function.typedBody expression body
  found : named.specialized.function.typedBody.lookupExpression? expression = some node
  form : node.form = .call callee arguments (.declaration instantiation)
  coercions : node.coercions ≠ []
  requirements : node.requirements ≠ []
  children : ∀ argument ∈ arguments,
    GeneralSyntax named.specialized.function.typedBody argument (fun _ => False)
  initializer : compiled.indexed.base.locals.bindings.find? (fun binding =>
    decide (binding.caller = (CallableIndexedNamedGeneration.context compiled.indexed named).owner ∧
      binding.initializer = expression)) = none
  direct : DirectSite directRows instantiation
  metadata : CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles.NativeMetadataFor
    compiled.indexed named named.specialized.function.typedBody (fun _ => False)
  signature : ProgramFunctionSignature
  signatureMember : signature ∈ compiled.sourceProgram.signatures.functions
  sourceOwner : named.specialized.function.typedBody.owner = signature.id

def certifyBody (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function)
    (directRows : List SourceSpecialization.SpecializedFunction) (fuel : Nat)
    (body : List StatementId) : Option (BodyCertificate compiled named directRows body) := do
  let source := named.specialized.function.typedBody
  let ⟨metadata⟩ ← CallableIndexedOwnedPreparedPrimitiveSourceAdmission.nativeMetadata? compiled.indexed named source
  match signatureFound : compiled.sourceProgram.signatures.functions.find?
      (fun signature => decide (source.owner = signature.id)) with
  | none => none
  | some signature =>
    have signatureMember := List.mem_of_find?_eq_some signatureFound
    have sourceOwner : source.owner = signature.id := by
      simpa only [decide_eq_true_eq] using (List.find?_some
        (p := fun item : ProgramFunctionSignature => decide (source.owner = item.id)) signatureFound)
    match bodyEq : body with
    | [] => none
    | statement :: rest =>
      match statementFound : source.lookupStatement? statement with
      | none => none
      | some statementNode =>
        match statementForm : statementNode.form with
        | .returnStmt (some expression) =>
          match found : source.lookupExpression? expression with
          | none => none
          | some node =>
            match form : node.form with
            | .call callee arguments (.declaration instantiation) =>
              if coercions : node.coercions ≠ [] then
                if requirements : node.requirements ≠ [] then
                  let ⟨children⟩ ← allProof? (fun argument => GeneralSyntax source argument (fun _ => False))
                    (CallableIndexedOwnedPreparedPrimitiveSourceAdmission.expression? source fuel) arguments
                  if initializer : compiled.indexed.base.locals.bindings.find? (fun binding =>
                      decide (binding.caller = (CallableIndexedNamedGeneration.context compiled.indexed named).owner ∧
                        binding.initializer = expression)) = none then
                    let ⟨direct⟩ ← CallableIndexedOwnedPreparedNamedSyntaxAdmission.directSite? directRows instantiation
                    pure {
                      expression, node, callee, arguments, instantiation,
                      terminal := by rw [bodyEq]; exact .returning rest statementFound statementForm,
                      found, form, coercions, requirements, children, initializer, direct,
                      metadata, signature, signatureMember, sourceOwner }
                  else none
                else none
              else none
            | _ => none
        | _ => none

def NodeReady (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function)
    (directRows : List SourceSpecialization.SpecializedFunction) : Node → Prop
  | .expression node => match node.form with
    | .lambda _ _ body => Nonempty (BodyCertificate compiled named directRows body)
    | _ => True
  | .statement _ => True

def certifyNode (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function)
    (directRows : List SourceSpecialization.SpecializedFunction) (fuel : Nat)
    (node : Node) : Option (PLift (NodeReady compiled named directRows node)) :=
  match node with
  | .statement _ => some ⟨True.intro⟩
  | .expression expression => by
    cases form : expression.form
    case lambda parameters result body =>
      exact do
        let certificate ← certifyBody compiled named directRows fuel body
        pure ⟨by simpa only [NodeReady, form] using (show Nonempty (BodyCertificate compiled named directRows body) from ⟨certificate⟩)⟩
    all_goals exact some ⟨by simp only [NodeReady, form]⟩

structure SourceCertificate (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function)
    (directRows : List SourceSpecialization.SpecializedFunction) : Prop where
  nodes : ∀ node ∈ named.specialized.function.typedBody.nodes, NodeReady compiled named directRows node

def certifySource (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function)
    (directRows : List SourceSpecialization.SpecializedFunction) (fuel : Nat) :
    Option (PLift (SourceCertificate compiled named directRows)) := do
  let ⟨nodes⟩ ← allProof? (NodeReady compiled named directRows)
    (certifyNode compiled named directRows fuel) named.specialized.function.typedBody.nodes
  pure ⟨⟨nodes⟩⟩

theorem SourceCertificate.selected {compiled : SourceCoreUnifiedCompilation.Compiled}
    {named : SourceCoreGeneralFunctions.Function} {directRows : List SourceSpecialization.SpecializedFunction}
    (certificate : SourceCertificate compiled named directRows)
    {id : ExpressionId} {node : ExpressionNode} {parameters : List TypedBinder}
    {result : TypeSystem.Ty} {body : List StatementId}
    (found : named.specialized.function.typedBody.lookupExpression? id = some node)
    (form : node.form = .lambda parameters result body) :
    Nonempty (BodyCertificate compiled named directRows body) := by
  have checked := certificate.nodes (.expression node) (lookupExpression?_sound found).1
  simpa only [NodeReady, form] using checked

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled compiled.indexed.ancestry.graph.inputs.callable)
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (code : CallableIndexedLambdaValues.Code compiled.indexed function scope administrative)
  (support : CallableIndexedOwnedOrdinaryLambdaSupport.Support code bodyRegistry semanticFaults)
  (provenance : CallableIndexedOwnedContextualLambdaProvenance.OrdinaryAt code support)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  {inputs : List (Input compiled)} (rows : Inventory inputs)
  {directRows : List SourceSpecialization.SpecializedFunction} (aligned : TableAligned inputs directRows)
  {loaded : LoadedProgram} (checked : Frontend.checkLoadedProgram loaded 1024 = .ok compiled.sourceProgram)
  (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
  (methods : CallableIndexedOwnedPreparedStagedClosedCoercionSelection.Catalog compiled)

include stagePrepared code support provenance receiver wellFormed rows aligned checked catalog methods in
theorem of_actual
    (certificate : BodyCertificate compiled support.caller.named directRows function.body)
    (methodBodies : ∀ {method : ExecutableImplMethods.CheckedMethod}
      (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
      (sourceAt : CallablePreparedMethodRuntimeProfileFactory.SourceAt principal.cached.compilation
        (.initial compiled.compatible.checked) principal.sourceBody principal.dictionary)
      (_diagnostic : CallableIndexedOwnedPreparedStagedMethodTerminalSupport.DiagnosticAt principal.cached),
      ∃ packet : CallableIndexedOwnedPreparedStagedMethodBodyStaticSupport.Packet principal,
        packet.sourceAt = sourceAt ∧ CallableIndexedOwnedPreparedStagedMethodBodyStaticSupport.Support
          principal packet (headers rows) (RecursiveNamedPreparedStageScopes.registry stagePrepared)
          (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) :
    Nonempty (Σ packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.Terminal code
        (RecursiveNamedPreparedStageScopes.registry stagePrepared),
      CallableIndexedOwnedPreparedStagedPhysicalClosureStaticSupport.SelectedBody (headers := headers rows)
        code support.body.toContext (RecursiveNamedPreparedStageScopes.registry stagePrepared) packet
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) := by
  have supported : CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported
      code.compilation.plan certificate.instantiation := by
    rw [support.compilation]
    exact certificate.direct.supported aligned
  have covered : ∀ index signature,
      SourceCompilationPlan.exactInstantiationKey code.compilation.plan certificate.instantiation = .ok signature.key →
      code.compilation.globals[index]? = some signature →
      ∃ header ∈ headers rows, header.slot = index ∧ header.named.signature = signature := by
    intro index signature target global
    rw [support.compilation] at target global
    exact certificate.direct.covered rows aligned target global
  obtain ⟨sidecar, _issued, selected⟩ :=
    CallableIndexedOwnedPreparedDirectStageScopeReceipts.code_scope code support.source_receipt support.body.unique
  exact CallableIndexedOwnedPreparedStagedOrdinaryCoercedTerminalSupport.of_actual
    stagePrepared code support provenance receiver wellFormed
    (by simpa only [support.source, CallableIndexedNamedGeneration.source] using certificate.metadata)
    rows checked catalog methods certificate.signatureMember
    (by simpa only [support.source, CallableIndexedNamedGeneration.source] using certificate.sourceOwner)
    methodBodies certificate.expression
    (by simpa only [support.source, CallableIndexedNamedGeneration.source] using certificate.terminal)
    (by simpa only [support.source, CallableIndexedNamedGeneration.source] using certificate.found)
    certificate.form certificate.coercions certificate.requirements
    (by simpa only [support.source, CallableIndexedNamedGeneration.source] using certificate.children)
    certificate.initializer supported covered _ (.anonymous selected)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCoercedClosureAdmission
