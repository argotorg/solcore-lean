import Solcore.SourceSemantics.CoreLowering.CallableMethodBodyCoherence
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCoercedClosureAdmission
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinaryMethodTerminalSupport

/-! Finite original-source lambda checks cover ordinary terminal roots and the
existing constrained coerced terminal roots. Catalog capability controls the
coerced branch; original bodies and metadata are retained in both branches. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 3200000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedClosureAdmission
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

structure OrdinaryBodyCertificate (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function)
    (directRows : List SourceSpecialization.SpecializedFunction) (body : List StatementId) where
  expression : ExpressionId
  terminal : CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Terminal
    named.specialized.function.typedBody expression body
  tree : GeneralSyntax named.specialized.function.typedBody expression (DirectSite directRows)
  metadata : CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
    compiled.indexed named named.specialized.function.typedBody (DirectSite directRows)
  signature : ProgramFunctionSignature
  signatureMember : signature ∈ compiled.sourceProgram.signatures.functions
  sourceOwner : named.specialized.function.typedBody.owner = signature.id

def certifyOrdinaryBody (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function)
    (directRows : List SourceSpecialization.SpecializedFunction) (fuel : Nat)
    (body : List StatementId) : Option (OrdinaryBodyCertificate compiled named directRows body) := do
  let source := named.specialized.function.typedBody
  let ⟨metadata⟩ ← CallableIndexedOwnedPreparedNamedSyntaxAdmission.metadata?
    compiled.indexed named source (DirectSite directRows)
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
        | .returnStmt (some expression) => do
          let ⟨tree⟩ ← CallableIndexedOwnedPreparedNamedSyntaxAdmission.expression? directRows source fuel expression
          pure {
            expression,
            terminal := by rw [bodyEq]; exact .returning rest statementFound statementForm,
            tree, metadata, signature, signatureMember, sourceOwner }
        | _ => none

inductive BodyCertificate (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function)
    (directRows : List SourceSpecialization.SpecializedFunction) (allowCoerced : Bool)
    (body : List StatementId) where
  | ordinary (certificate : OrdinaryBodyCertificate compiled named directRows body)
  | coerced (enabled : allowCoerced = true)
      (certificate : CallableIndexedOwnedPreparedCoercedClosureAdmission.BodyCertificate compiled named directRows body)

def certifyBody (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function)
    (directRows : List SourceSpecialization.SpecializedFunction) (allowCoerced : Bool)
    (fuel : Nat) (body : List StatementId) : Option (BodyCertificate compiled named directRows allowCoerced body) :=
  match certifyOrdinaryBody compiled named directRows fuel body with
  | some certificate => some (.ordinary certificate)
  | none => if enabled : allowCoerced = true then do
      let certificate ← CallableIndexedOwnedPreparedCoercedClosureAdmission.certifyBody compiled named directRows fuel body
      pure (.coerced enabled certificate)
    else none

def NodeReady (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function)
    (directRows : List SourceSpecialization.SpecializedFunction) (allowCoerced : Bool) : Node → Prop
  | .expression node => match node.form with
    | .lambda _ _ body => Nonempty (BodyCertificate compiled named directRows allowCoerced body)
    | _ => True
  | .statement _ => True

def certifyNode (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function)
    (directRows : List SourceSpecialization.SpecializedFunction) (allowCoerced : Bool) (fuel : Nat)
    (node : Node) : Option (PLift (NodeReady compiled named directRows allowCoerced node)) :=
  match node with
  | .statement _ => some ⟨True.intro⟩
  | .expression expression => by
    cases form : expression.form
    case lambda parameters result body =>
      exact do
        let certificate ← certifyBody compiled named directRows allowCoerced fuel body
        pure ⟨by simpa only [NodeReady, form] using
          (show Nonempty (BodyCertificate compiled named directRows allowCoerced body) from ⟨certificate⟩)⟩
    all_goals exact some ⟨by simp only [NodeReady, form]⟩

structure SourceCertificate (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function)
    (directRows : List SourceSpecialization.SpecializedFunction) (allowCoerced : Bool) : Prop where
  nodes : ∀ node ∈ named.specialized.function.typedBody.nodes, NodeReady compiled named directRows allowCoerced node

def certifySource (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function)
    (directRows : List SourceSpecialization.SpecializedFunction) (allowCoerced : Bool) (fuel : Nat) :
    Option (PLift (SourceCertificate compiled named directRows allowCoerced)) := do
  let ⟨nodes⟩ ← allProof? (NodeReady compiled named directRows allowCoerced)
    (certifyNode compiled named directRows allowCoerced fuel) named.specialized.function.typedBody.nodes
  pure ⟨⟨nodes⟩⟩

theorem SourceCertificate.selected {compiled : SourceCoreUnifiedCompilation.Compiled}
    {named : SourceCoreGeneralFunctions.Function} {directRows : List SourceSpecialization.SpecializedFunction}
    {allowCoerced : Bool} (certificate : SourceCertificate compiled named directRows allowCoerced)
    {id : ExpressionId} {node : ExpressionNode} {parameters : List TypedBinder}
    {result : TypeSystem.Ty} {body : List StatementId}
    (found : named.specialized.function.typedBody.lookupExpression? id = some node)
    (form : node.form = .lambda parameters result body) :
    Nonempty (BodyCertificate compiled named directRows allowCoerced body) := by
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
  (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
  (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
  (methods : CallableIndexedOwnedPreparedStagedMethodSelectionIssuer.Catalog compiled)

include stagePrepared code support provenance receiver wellFormed rows aligned checked catalog methods in
theorem of_ordinary
    (certificate : OrdinaryBodyCertificate compiled support.caller.named directRows function.body) :
    Nonempty (Σ packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.Terminal code
        (RecursiveNamedPreparedStageScopes.registry stagePrepared),
      CallableIndexedOwnedPreparedStagedPhysicalClosureStaticSupport.SelectedBody (headers := headers rows)
        code support.body.toContext (RecursiveNamedPreparedStageScopes.registry stagePrepared) packet
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) := by
  have supported : ∀ instantiation, DirectSite directRows instantiation →
      CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported code.compilation.plan instantiation := by
    intro instantiation site
    rw [support.compilation]
    exact site.supported aligned
  have covered : ∀ instantiation, DirectSite directRows instantiation → ∀ index signature,
      SourceCompilationPlan.exactInstantiationKey code.compilation.plan instantiation = .ok signature.key →
      code.compilation.globals[index]? = some signature →
      ∃ header ∈ headers rows, header.slot = index ∧ header.named.signature = signature := by
    intro instantiation site index signature target global
    rw [support.compilation] at target global
    exact site.covered rows aligned target global
  obtain ⟨sidecar, _issued, selected⟩ :=
    CallableIndexedOwnedPreparedDirectStageScopeReceipts.code_scope code support.source_receipt support.body.unique
  exact CallableIndexedOwnedPreparedStagedOrdinaryMethodTerminalSupport.of_actual_with_catalog
    stagePrepared code support provenance receiver wellFormed supported
    (by simpa only [support.source, CallableIndexedNamedGeneration.source] using certificate.metadata)
    rows covered checked catalog methods certificate.signatureMember
    (by simpa only [support.source, CallableIndexedNamedGeneration.source] using certificate.sourceOwner)
    certificate.expression
    (by simpa only [support.source, CallableIndexedNamedGeneration.source] using certificate.terminal)
    (by simpa only [support.source, CallableIndexedNamedGeneration.source] using certificate.tree)
    _ (.anonymous selected)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedClosureAdmission
