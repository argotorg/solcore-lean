import Solcore.SourceSemantics.CoreLowering.Internal.Accepted.ScopedSourceBodies
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.OrdinaryMethodRoots
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.NamedCollectors
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.CoercionSpine
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.LambdaBodySupport
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.Coercions
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.NativeCollectors
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.LambdaPhysical
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.LambdaReadyFamilies
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedLambdaValues
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.FormationReceipts
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedLambdaTyping
import Solcore.SourceSemantics.CoreLowering.ActualCallablePolicy
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.OrdinaryLambdas
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ContextualOrigins
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ContextualLambdas
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.LiteralReturns
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.BodyReadyState
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicApplicationResults
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.MixedHeads
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.LexicalBodies
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.MixedBodyCompiler

/-!
# Prepared callables: native lambdas and closure admission

Closure admission, native compiler children, lambda receipts, site policies and family qualification.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedScopedClosureAdmission
/-! Compiler-derived scoped body certificates use the existing branching closure
collector at the original Source frame and exact current parameter context. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3200000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedScopedClosureAdmission
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedNamedSyntaxAdmission (DirectSite TableAligned)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)

structure SourceBodyCertificate (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function)
    (directRows : List SourceSpecialization.SpecializedFunction) (body : List StatementId) where
  result : TypeSystem.Ty
  scan : ScopedSourceBodyAdmission.Scan named.specialized.function.typedBody
    (fun id => GeneralSyntax named.specialized.function.typedBody id (DirectSite directRows)) result true body
  metadata : CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
    compiled.indexed named named.specialized.function.typedBody (DirectSite directRows)
  signature : ProgramFunctionSignature
  signatureMember : signature ∈ compiled.sourceProgram.signatures.functions
  sourceOwner : named.specialized.function.typedBody.owner = signature.id

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled compiled.indexed.ancestry.graph.inputs.callable)
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {bodyRegistry : SourceCoreRawMetadata.Registry}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (code : CallableIndexedLambdaValues.Code compiled.indexed function scope administrative)
  (support : CallableIndexedOwnedOrdinaryLambdaSupport.Support code bodyRegistry
    (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics))
  (provenance : CallableIndexedOwnedContextualLambdaProvenance.OrdinaryAt code support)
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  {inputs : List (Input compiled)} (rows : Inventory inputs)
  {directRows : List SourceSpecialization.SpecializedFunction} (aligned : TableAligned inputs directRows)
  (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
  (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
  (methods : CallableIndexedOwnedPreparedStagedMethodSelectionIssuer.Catalog compiled)

include stagePrepared code support provenance receiver wellFormed rows aligned checked catalog methods in
theorem of_actual
    (certificate : SourceBodyCertificate compiled support.caller.named directRows function.body) :
    Nonempty (Σ packet : CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport.Branching code
        (RecursiveNamedPreparedStageScopes.registry stagePrepared),
      CallableIndexedOwnedPreparedStagedPhysicalBranchingClosureStaticSupport.SelectedBody (headers rows)
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
  obtain ⟨finalContext, facts, typed, completed⟩ :=
    CallableIndexedOwnedLambdaSourceAdmission.body_typed_at_parameters support.body.frame support.body.extended
  have scan : ScopedSourceBodyAdmission.Scan function.source
      (fun id => GeneralSyntax function.source id (DirectSite directRows)) certificate.result true function.body := by
    simpa only [support.source, CallableIndexedNamedGeneration.source] using certificate.scan
  have result : function.resultType = certificate.result :=
    scan.result_eq_of_completes support.body.unique typed completed
  have syntaxTree := scan.syntax support.body.unique result typed
  rw [← result] at syntaxTree
  exact CallableIndexedOwnedPreparedStagedOrdinaryMethodScopedSupport.of_actual_with_catalog
    stagePrepared code support provenance receiver wellFormed supported
    (by simpa only [support.source, CallableIndexedNamedGeneration.source] using certificate.metadata)
    rows covered checked catalog methods certificate.signatureMember
    (by simpa only [support.source, CallableIndexedNamedGeneration.source] using certificate.sourceOwner)
    scan.shape syntaxTree
    _ (.anonymous selected)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedScopedClosureAdmission
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCoercedClosureAdmission
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
  (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedClosureAdmission
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
  | scoped (certificate : CallableIndexedOwnedPreparedScopedClosureAdmission.SourceBodyCertificate
      compiled named directRows body)
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedClosedCoercionAdmission
/-! Finite checks on original implementation heads, predicates and actual
selected method shapes construct the closed coercion catalog. Full Source
well-formedness remains an independent premise of its semantic consumer. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedClosedCoercionAdmission
open Core Frontend SourceInference

structure ClosedImplementation (implementation : ProgramImplementationSignature) : Prop where
  parameters : implementation.parameters = []
  variables : TypedTraitResolution.predicateVariables implementation.head = []
  headParameters : TypedTraitResolution.predicateParameters implementation.head = []
  predicates : implementation.wherePredicates = []
  methods : ∀ method ∈ implementation.methods, method.wherePredicates = []

theorem ClosedImplementation.formed {implementation : ProgramImplementationSignature}
    (closed : ClosedImplementation implementation) {method : ProgramImplMethodSignature}
    (member : method ∈ implementation.methods) :
    CallableCoercionMethodInstantiation.Formation implementation method := by
  refine ⟨closed.parameters ▸ List.nodup_nil, ?_, ?_, ?_⟩
  · intro metavariable occurs
    have present := TypedTraitResolution.mem_predicateVariables_iff.mpr occurs
    rw [closed.variables] at present
    cases present
  · intro parameter occurs
    have present := TypedTraitResolution.mem_predicateParameters_iff.mpr occurs
    rw [closed.headParameters] at present
    cases present
  · intro predicate present _parameter _occurs
    rw [closed.methods method member] at present
    cases present

def implementation? (implementation : ProgramImplementationSignature) :
    Option (PLift (ClosedImplementation implementation)) :=
  if parameters : implementation.parameters = [] then
    if variables : TypedTraitResolution.predicateVariables implementation.head = [] then
      if headParameters : TypedTraitResolution.predicateParameters implementation.head = [] then
        if predicates : implementation.wherePredicates = [] then
          if methods : implementation.methods.all (fun method => decide (method.wherePredicates = [])) = true then
            some ⟨⟨parameters, variables, headParameters, predicates,
              fun method member => of_decide_eq_true (List.all_eq_true.mp methods method member)⟩⟩
          else none
        else none
      else none
    else none
  else none

def implementations? : (implementations : List ProgramImplementationSignature) →
    Option (PLift (∀ implementation ∈ implementations, ClosedImplementation implementation))
  | [] => some ⟨by intro implementation member; cases member⟩
  | first :: rest => do
      let ⟨head⟩ ← implementation? first
      let ⟨tail⟩ ← implementations? rest
      pure ⟨by
        intro implementation member
        rcases List.mem_cons.mp member with same | member
        · exact same ▸ head
        · exact tail implementation member⟩

/-- Every implementation and trait in the original finite signatures is checked.
The shape validator retains all original sites in the final specialization plan. -/
def certify (compiled : SourceCoreUnifiedCompilation.Compiled) :
    Option (PLift (CallableIndexedOwnedPreparedStagedClosedCoercionSelection.Catalog compiled)) := do
  let ⟨closed⟩ ← implementations? compiled.sourceProgram.signatures.implementations
  if traits : compiled.sourceProgram.signatures.traits.all
      (fun trait => decide (trait.wherePredicates = [])) = true then
    let ⟨shapes⟩ ← CallableCoercionSourceShapeTable.validate compiled.sourceProgram
      compiled.indexed.base.plan.specializations
    pure ⟨{
      shapes := shapes
      parameters := fun implementation member _method _methodMember => (closed implementation member).parameters
      formed := fun implementation member method methodMember => (closed implementation member).formed methodMember
      assumptions := by
        intro implementation member method methodMember trait traitMember
        have traitEmpty : trait.wherePredicates = [] := of_decide_eq_true (List.all_eq_true.mp traits trait traitMember)
        simp [ProgramImplementationSignature.methodAssumptions, traitEmpty,
          (closed implementation member).predicates, (closed implementation member).methods method methodMember] }⟩
  else none

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedClosedCoercionAdmission
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedDirectLambdaInvocationBounds
/-! A direct prepared closure retains its actual Code, captured runtime
fields and one native-collected JointBody. Its own Source metadata and runtime
typing construct the value model; no universal CatalogSites projection is used.
Actual Entry/Prefix packets feed one strict same-body protocol flow child. The
original invocation and application restore the actual caller once, while the
receiving registry stays independent of the preparation registry. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedDirectLambdaInvocationBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedPreparedNativeDirectCellOrigins (Association)
open CallableIndexedOwnedPreparedContextualQualification (Facet)
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open RecursiveNamedCatalogInvocationBounds (Below)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {qualification : Facet compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {mapping : LocationMap} {world : StoreTyping}
  {function : Dynamic.Closure} {native : Value}
  {bindings : List CallableIndexedParameterCertificates.Binding} {parameterCore resultCore : Ty}
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))

/-- The selected ordinary body uses its actual Header/Nested packet; the
selected method body uses its actual Named/Origin packet. Both are the exact
prepared JointBody projection stored beside the compiler qualification. -/
def FlowPreserves
    (member : Association qualification headers keys bodyRegistry faults
    mapping world function native bindings parameterCore resultCore) (size : Nat) : Prop :=
  match member with
  | .ordinary owner captured code history support _origin _prepared _qualified prefixContext globals _reference _typed =>
    CallableIndexedOwnedTypedLambdaProtocolContinuations.FlowPreserves captured code support.body.toBody functions
        (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller)
        (registry := registry) (faults := faults) size
  | .principal owner captured code history support _origin _prepared _qualified globals leading _reference _typed =>
    CallableIndexedOwnedTypedLambdaProtocolContinuations.FlowPreserves captured code support.body.toBody functions
        (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
        (registry := registry) (faults := faults) size

/-- Native flow is indexed by the same selected packet protocol and original
body. Its measured grade remains independent of the reconstructed Source grade. -/
def FlowReflects
    (member : Association qualification headers keys bodyRegistry faults
    mapping world function native bindings parameterCore resultCore) (size : Nat) : Prop :=
  match member with
  | .ordinary owner captured code history support _origin _prepared _qualified prefixContext globals _reference _typed =>
    CallableIndexedOwnedTypedLambdaProtocolContinuations.FlowReflects captured code support.body.toBody functions
        (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller)
        (registry := registry) (faults := faults) size
  | .principal owner captured code history support _origin _prepared _qualified globals leading _reference _typed =>
    CallableIndexedOwnedTypedLambdaProtocolContinuations.FlowReflects captured code support.body.toBody functions
        (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
        (registry := registry) (faults := faults) size

variable {before : Dynamic.Heap} {store : Store}
  {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  (member : Association qualification headers keys bodyRegistry faults
    mapping world function native bindings parameterCore resultCore)
  (initial : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  {arguments : List Dynamic.Value} {nativeArguments : List Value}
  (represented : CallableIndexedParameterMeaning.Arguments
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    mapping world bindings arguments nativeArguments)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world before store)
  (beforeTyped : Dynamic.HeapWellTyped function.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes function.context before arguments
    (function.parameters.map (fun binder => binder.scheme.body)))
  (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
  (stable : StableRows initial)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))

include represented heaps beforeTyped argumentsTyped locals stable wellFormed in
/-- Each actual branch constructs its genuine parameter packets and consumes
one strict protocol-flow child at the same retained body. The original low
invocation and finite apply edge retain the same restored caller pool. -/
theorem preserves_at (budget : Nat)
    (below : Below budget (FlowPreserves functions member (registry := registry)))
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram)
    size callContext callerEvidence function.evidence before (.closure function) arguments outcome after)
    (within : size ≤ budget) :
    ∃ value finalStore,
    Evaluates [native, DataPatternValues.packValues nativeArguments] store
        CallableIndexedLambdaCalls.applyPayload value finalStore ∧
    CallableIndexedOwnedStoredClosureInvocation.ResultAt (registry := registry) (faults := faults)
        functions initial function resultCore outcome after value finalStore := by
  cases member with
  | ordinary owner captured code history support origin prepared qualified prefixContext globals referenceIndex typed =>
    have raw : Dynamic.ValuesHaveTypes function.context before arguments support.body.types := by
        simpa only [Dynamic.MonoBindersExtend.bodyTypes_eq support.body.extended] using argumentsTyped
    obtain ⟨currentMetadata, currentCarried⟩ := stable owner.position
    have reference : captured.canonical[code.referenceIndex]? =
          some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
        rw [referenceIndex]
        exact globals.reference
    change Below budget (CallableIndexedOwnedTypedLambdaProtocolContinuations.FlowPreserves
        captured code support.body.toBody functions
        (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller)
        (registry := registry) (faults := faults)) at below
    let packets := CallableIndexedOwnedPreparedLambdaProtocolPackets.Ordinary.packets
        (registry := registry) (arguments := arguments) (nativeArguments := nativeArguments)
        captured code history functions owner initial support origin globals prefixContext
    have continuation := CallableIndexedOwnedTypedLambdaProtocolContinuations.source_continuation
        captured code history support.body.toBody functions
        (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller)
        owner initial packets beforeTyped raw stable wellFormed budget below
    obtain ⟨value, finalStore, finalMap, finalWorld, invoked, result, finalHeaps, maps, worlds,
          frame, metadata, reached, related⟩ :=
        CallableIndexedOwnedLambdaInvocationBounds.invocation_preserves_bounded_at_with_continuation
          captured code history support.body.toBody.toContext functions represented owner initial
          heaps locals reference currentCarried (CallableIndexedLambdaTemplatePermission.lambda_allowed code history)
          budget continuation trace within
    exact ⟨value, finalStore, .apply (.second (.first (.var rfl))) (.var rfl) invoked,
        finalMap, finalWorld, result, finalHeaps, maps, worlds, frame, metadata, reached, related,
        StableRows.after_administrative initial reached stable frame⟩
  | principal owner captured code history support origin prepared qualified globals leading referenceIndex typed =>
    have raw : Dynamic.ValuesHaveTypes function.context before arguments support.body.types := by
        simpa only [Dynamic.MonoBindersExtend.bodyTypes_eq support.body.extended] using argumentsTyped
    obtain ⟨currentMetadata, currentCarried⟩ := stable owner.position
    have reference : captured.canonical[code.referenceIndex]? =
          some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
        rw [referenceIndex]
        exact globals.reference
    change Below budget (CallableIndexedOwnedTypedLambdaProtocolContinuations.FlowPreserves
        captured code support.body.toBody functions
        (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
        (registry := registry) (faults := faults)) at below
    let packets := CallableIndexedOwnedPreparedLambdaProtocolPackets.Principal.packets
        (registry := registry) (arguments := arguments) (nativeArguments := nativeArguments)
        captured code history functions owner initial support origin globals leading
    have continuation := CallableIndexedOwnedTypedLambdaProtocolContinuations.source_continuation
        captured code history support.body.toBody functions
        (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
        owner initial packets beforeTyped raw stable wellFormed budget below
    obtain ⟨value, finalStore, finalMap, finalWorld, invoked, result, finalHeaps, maps, worlds,
          frame, metadata, reached, related⟩ :=
        CallableIndexedOwnedLambdaInvocationBounds.invocation_preserves_bounded_at_with_continuation
          captured code history support.body.toBody.toContext functions represented owner initial
          heaps locals reference currentCarried (CallableIndexedLambdaTemplatePermission.lambda_allowed code history)
          budget continuation trace within
    exact ⟨value, finalStore, .apply (.second (.first (.var rfl))) (.var rfl) invoked,
        finalMap, finalWorld, result, finalHeaps, maps, worlds, frame, metadata, reached, related,
        StableRows.after_administrative initial reached stable frame⟩

include represented heaps beforeTyped argumentsTyped locals stable wellFormed in
/-- The real application exposes one strictly smaller native invocation. Each
branch uses its authentic Prefix packet and native typed finish once; the
original restore returns that actual caller, with independent Source grade. -/
theorem reflects_at (budget : Nat)
    (below : Below budget (FlowReflects functions member (registry := registry)))
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {value : Value} {finalStore : Store}
    (completed : EvaluationSize size [native, DataPatternValues.packValues nativeArguments] store
    CallableIndexedLambdaCalls.applyPayload value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after,
    RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram)
        sourceSize callContext callerEvidence function.evidence before (.closure function) arguments outcome after ∧
    CallableIndexedOwnedStoredClosureInvocation.ResultAt (registry := registry) (faults := faults)
        functions initial function resultCore outcome after value finalStore := by
  cases member with
  | ordinary owner captured code history support origin prepared qualified prefixContext globals referenceIndex typed =>
    have raw : Dynamic.ValuesHaveTypes function.context before arguments support.body.types := by
        simpa only [Dynamic.MonoBindersExtend.bodyTypes_eq support.body.extended] using argumentsTyped
    obtain ⟨currentMetadata, currentCarried⟩ := stable owner.position
    have reference : captured.canonical[code.referenceIndex]? =
          some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
        rw [referenceIndex]
        exact globals.reference
    change Below budget (CallableIndexedOwnedTypedLambdaProtocolContinuations.FlowReflects
        captured code support.body.toBody functions
        (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller)
        (registry := registry) (faults := faults)) at below
    let packets := CallableIndexedOwnedPreparedLambdaProtocolPackets.Ordinary.packets
        (registry := registry) (arguments := arguments) (nativeArguments := nativeArguments)
        captured code history functions owner initial support origin globals prefixContext
    have continuation := CallableIndexedOwnedTypedLambdaProtocolContinuations.native_continuation
        captured code history support.body.toBody functions
        (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller)
        owner initial packets beforeTyped raw stable wellFormed budget below
    obtain ⟨bodySize, smaller, applied⟩ := completed.apply_body (.second (.first (.var rfl))) (.var rfl)
    obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, finalHeaps, maps, worlds,
          frame, metadata, reached, related⟩ :=
        CallableIndexedOwnedLambdaInvocationBounds.invocation_reflects_bounded_at_with_continuation
          captured code history support.body.toBody.toContext functions represented owner initial
          heaps locals reference currentCarried (CallableIndexedLambdaTemplatePermission.lambda_allowed code history)
          support.body.frame budget continuation applied (Nat.le_trans (Nat.le_of_lt smaller) within)
    exact ⟨sourceSize, outcome, after, trace, finalMap, finalWorld, result, finalHeaps, maps, worlds,
        frame, metadata, reached, related, StableRows.after_administrative initial reached stable frame⟩
  | principal owner captured code history support origin prepared qualified globals leading referenceIndex typed =>
    have raw : Dynamic.ValuesHaveTypes function.context before arguments support.body.types := by
        simpa only [Dynamic.MonoBindersExtend.bodyTypes_eq support.body.extended] using argumentsTyped
    obtain ⟨currentMetadata, currentCarried⟩ := stable owner.position
    have reference : captured.canonical[code.referenceIndex]? =
          some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
        rw [referenceIndex]
        exact globals.reference
    change Below budget (CallableIndexedOwnedTypedLambdaProtocolContinuations.FlowReflects
        captured code support.body.toBody functions
        (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
        (registry := registry) (faults := faults)) at below
    let packets := CallableIndexedOwnedPreparedLambdaProtocolPackets.Principal.packets
        (registry := registry) (arguments := arguments) (nativeArguments := nativeArguments)
        captured code history functions owner initial support origin globals leading
    have continuation := CallableIndexedOwnedTypedLambdaProtocolContinuations.native_continuation
        captured code history support.body.toBody functions
        (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
        owner initial packets beforeTyped raw stable wellFormed budget below
    obtain ⟨bodySize, smaller, applied⟩ := completed.apply_body (.second (.first (.var rfl))) (.var rfl)
    obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, finalHeaps, maps, worlds,
          frame, metadata, reached, related⟩ :=
        CallableIndexedOwnedLambdaInvocationBounds.invocation_reflects_bounded_at_with_continuation
          captured code history support.body.toBody.toContext functions represented owner initial
          heaps locals reference currentCarried (CallableIndexedLambdaTemplatePermission.lambda_allowed code history)
          support.body.frame budget continuation applied (Nat.le_trans (Nat.le_of_lt smaller) within)
    exact ⟨sourceSize, outcome, after, trace, finalMap, finalWorld, result, finalHeaps, maps, worlds,
        frame, metadata, reached, related, StableRows.after_administrative initial reached stable frame⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedDirectLambdaInvocationBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeCompilerChildren
/-! Actual enclosing compiler typing is retained in each local child certificate.
The same Named compilation works for a Header or a selected Principal. This
factory removes both the broad assignment-native supplier and separately typed
lambda body. One native-aware compiler induction builds the literal JointBody.
An older broad AcceptedAt or Collected does not acquire these local witnesses.
Source authority and compiler acceptance remain independent of native typing. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeCompilerChildren
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration CallableIndexedLambdaValues
open CallableIndexedOwnedContextualCompilerPolicyProfiles
open CallableIndexedOwnedContextualLambdaJointStaticReceipts
open CallableIndexedOwnedContextualLambdaSourceDiagnostics
open CallableIndexedOwnedPreparedNativeJointBodyCollectors
open CallableLambdaViewEdits CallableLambdaBodyReachability GenericImperativeMatch

section Accepted
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {named : Named}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : Compilation compiled.indexed named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) named diagnostics namedCode compilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered)

/-- Native typing is for this exact emitted child and literal entry prefix.
The actual Source read/type and compiler action remain separate fields. -/
inductive AcceptedAt (expressionSyntax : TypedSource → ExpressionId → Prop)
    (administrative : Core.Context) (readFuel : Nat)
    (source : TypedSource) (sourceContext : SourceSemantics.Context) : GenericExpressionMeaning.Certificate where
  | intro {scope id node lowered compilerFuel residualMode nativeType}
      (found : source.lookupExpression? id = some node)
      (typed : ExpressionHasType source sourceContext id node.type)
      (allowed : expressionSyntax source id)
      (declarations : CompatibleExpressionReads.ScopeDeclarations source scope sourceContext)
      (closed : sourceContext.typeVariables = [])
      (residual : sourceContext.residualTypeVariables = residualMode)
      (signatures : sourceContext.signatures = compiled.compatible.checked.signatures)
      (accepted : SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody
        compilerFuel (context compiled.indexed named) source scope id rootReasonAt = .ok lowered)
      (raw : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        lowered.expression nativeType compiled.indexed.layouts.definitions) :
      AcceptedAt expressionSyntax administrative readFuel source sourceContext scope id lowered

def certificates (expressionSyntax : TypedSource → ExpressionId → Prop)
    (administrative : Core.Context) : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate :=
  AcceptedAt root expressionSyntax administrative

end Accepted

section Static
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {expressionSyntax : ExpressionId → Prop}
  {reasonAt : ExpressionId → Word} {definitions : DataEnvironment} {administrative : Core.Context}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Syntax.ValueAssignOp → Word}
  {invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}

/-- Only static policy, actual Source scope and hidden-match freshness remain.
Local expression typing comes from the enclosing emitted code, not this shell. -/
structure StaticInputs (residualMode : Bool) (policy : SourceCoreLoops.Policy)
    (sourceContext : SourceSemantics.Context) (scope : SourceCoreLocalCell.Scope) where
  matchCompilation : SourceCoreCompatibleDataMatches.Context
  matchPolicy : CompatibleMatchAmbientLowering.PolicySuccess policy matchCompilation
  matchValues : matchCompilation.values = values
  matchDefinitions : matchCompilation.definitions = definitions
  matchAllocator : matchCompilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
    (layouts.allocatorAt owner active onError))
  hidden : MatchHiddenFresh source
  readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked
  binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
    policy.lowerBinder source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked source scope binder
  allocationPolicy : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
    (layouts.allocatorAt owner active onError))
  assignments : CompatibleAssignmentStatements.AssignmentPolicy policy values invalidProjection invalidOperand missingDefault
  unaries : CompatibleBitNotStatements.Policy policy values invalidProjection invalidUnary missingDefault
  closed : sourceContext.typeVariables = []
  residual : sourceContext.residualTypeVariables = residualMode
  sourceSignatures : sourceContext.signatures = values.checked.signatures
  declarations : CompatibleExpressionReads.ScopeDeclarations source scope sourceContext
  ledger : sourceContext.solvedRequirements = matchCompilation.solvedRequirements

end Static

section Site
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {named : Named}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : Compilation compiled.indexed named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) named diagnostics namedCode compilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  (expressionSyntax : TypedSource → ExpressionId → Prop)
  {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
  {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (site : Site compiled.indexed named parameters result statements sourceContext evidence [] scope administrative)

/-- The exact chosen Site carries static Source/issuance inputs. Its body
native typing is derived from site.code.typed by literal wrapper inversion. -/
structure SiteShell where
  issuedCompilation : CallableIndexedOwnedContextualLambdaIssuedRecipes.IssuedAt compiled.indexed diagnostics
  issued : IssuedSource compiled site.code.compilation.owner (source named)
  diagnosticPolicy : AssignmentDiagnosticPolicy
  entry : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) site.code
  frame : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram)
    (closure named parameters result statements sourceContext evidence [])
  readFuel : Nat
  canonical : site.code.view = source named
  unique : NodeOccurrencesUnique (source named)
  sameLedger : sourceContext.solvedRequirements = site.code.compilation.solvedRequirements
  syntaxTree : Syntax (source named) (expressionSyntax (source named))
    entry.context (.statements true statements) result
  projection : compiled.compatible.checked.catalog.project result = .ok site.code.receipt.resultCore
  residualMode : Bool
  static : StaticInputs (layouts := compiled.indexed.layouts) (owner := site.code.compilation.owner)
    (active := site.code.active) (frame := compiled.indexed.ancestry.layout.frame)
    (globals := compiled.indexed.base.globals.length) (onError := site.code.allocationError)
    (values := .initial compiled.compatible.checked) (source := site.code.view)
    (definitions := compiled.indexed.layouts.definitions)
    (invalidOperand := issued.invalidOperand) (invalidUnary := issued.invalidUnary)
    (invalidProjection := issued.invalidProjection) (missingDefault := issued.missingDefault)
    residualMode (bodyPolicy compilation site.code) entry.context
    (site.code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)

/-- Actual callback acceptance fixes the minimum compiler fuel. The local
native witness is retained verbatim alongside independent Source facts. -/
theorem accepted_child
    (policyEq : site.code.policy = root.selected.policy)
    (bodyEq : site.code.lowerBody = root.selected.lowerBody)
    (reasonEq : site.code.reasonAt = rootReasonAt)
    {currentContext : SourceSemantics.Context} {childScope : SourceCoreLocalCell.Scope}
    {fuel : Nat} {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    {residualMode : Bool} {nativeType : Ty}
    (closed : currentContext.typeVariables = []) (residual : currentContext.residualTypeVariables = residualMode)
    (signatures : currentContext.signatures = compiled.compatible.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations site.code.view childScope currentContext)
    (allowed : expressionSyntax site.code.view id) (found : site.code.view.lookupExpression? id = some node)
    (typed : ExpressionHasType site.code.view currentContext id node.type)
    (accepted : (bodyPolicy compilation site.code).lowerExpression fuel
      site.code.view childScope id site.code.reasonAt = .ok lowered)
    (raw : HasType (SourceCoreLocalCell.coreContext childScope ++ administrative)
      lowered.expression nativeType compiled.indexed.layouts.definitions)
    (readFuel : Nat) :
    AcceptedAt root expressionSyntax administrative readFuel site.code.view currentContext childScope id lowered := by
  change FunctionCode.children site.code.policy site.code.lowerBody site.code.fuel site.code.compilation
    fuel site.code.view childScope id site.code.reasonAt = .ok lowered at accepted
  rw [FunctionCode.children, policyEq, bodyEq, reasonEq, site.compilation] at accepted
  exact .intro found typed allowed declarations closed residual signatures accepted raw

/-- Both static and local native child fields are constructed internally from
one enclosing compiler extraction; no final expression Tree is requested. -/
def SiteShell.extraction (shell : SiteShell (compilation := compilation) expressionSyntax site)
    (policyEq : site.code.policy = root.selected.policy)
    (bodyEq : site.code.lowerBody = root.selected.lowerBody)
    (reasonEq : site.code.reasonAt = rootReasonAt) :
    NativeExtractionInputs (layouts := compiled.indexed.layouts) (owner := site.code.compilation.owner)
      (active := site.code.active) (frame := compiled.indexed.ancestry.layout.frame)
      (globals := compiled.indexed.base.globals.length) (onError := site.code.allocationError)
      (values := .initial compiled.compatible.checked) (source := site.code.view)
      (expressionSyntax := expressionSyntax site.code.view)
      (certificates := certificates root expressionSyntax administrative shell.readFuel site.code.view)
      (reasonAt := site.code.reasonAt) (definitions := compiled.indexed.layouts.definitions) (administrative := administrative)
      (invalidOperand := shell.issued.invalidOperand) (invalidUnary := shell.issued.invalidUnary)
      (invalidProjection := shell.issued.invalidProjection) (missingDefault := shell.issued.missingDefault)
      shell.residualMode (bodyPolicy compilation site.code) shell.entry.context
      (site.code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope) where
  matchCompilation := shell.static.matchCompilation
  matchPolicy := shell.static.matchPolicy
  matchValues := shell.static.matchValues
  matchDefinitions := shell.static.matchDefinitions
  matchAllocator := shell.static.matchAllocator
  matchChildStatic := MatchChildStatic.of_hidden shell.static.hidden
  readPolicy := shell.static.readPolicy
  binderPolicy := shell.static.binderPolicy
  allocationPolicy := shell.static.allocationPolicy
  expressions := by
    intro currentContext closed residual signatures childScope fuel id node lowered declarations allowed found typed accepted nativeType raw
    exact accepted_child root expressionSyntax site policyEq bodyEq reasonEq closed residual signatures
      declarations allowed found typed accepted raw shell.readFuel
  assignments := shell.static.assignments
  unaries := shell.static.unaries
  closed := shell.static.closed
  residual := shell.static.residual
  sourceSignatures := shell.static.sourceSignatures
  declarations := shell.static.declarations
  ledger := shell.static.ledger

/-- One same-Code joint body is built at the actual selected Site. The owning
Named record/dictionary is supplied by the caller's actual ordinary or Principal
producer; no Header is synthesized for a selected method. -/
theorem SiteShell.joint (shell : SiteShell (compilation := compilation) expressionSyntax site)
    (policyEq : site.code.policy = root.selected.policy)
    (bodyEq : site.code.lowerBody = root.selected.lowerBody)
    (reasonEq : site.code.reasonAt = rootReasonAt) :
    ∃ body : JointBody compilation site.code (Program.ofChecked compiled.sourceProgram)
        expressionSyntax (certificates root expressionSyntax administrative) shell.diagnosticPolicy
        shell.issued.invalidOperand shell.issued.invalidUnary shell.issued.invalidProjection shell.issued.missingDefault,
      body.toContext = shell.entry ∧ body.readFuel = shell.readFuel := by
  have recipe : BodyRecipe compilation site.code := bodyEq.trans root.selected.recipe
  have edited : LocalView (source named) site.code.view [] := by
    rw [shell.canonical]
    exact LocalView.refl _
  exact CallableIndexedOwnedPreparedNativeJointBodyCollectors.at_site compilation site recipe
    (Program.ofChecked compiled.sourceProgram) shell.entry shell.frame expressionSyntax
    (certificates root expressionSyntax administrative) shell.readFuel shell.diagnosticPolicy
    shell.issued.invalidOperand shell.issued.invalidUnary shell.issued.invalidProjection shell.issued.missingDefault
    edited (by intro id member; cases member) shell.unique shell.sameLedger
    (by intro id reached allowed; simpa only [shell.canonical] using allowed)
    (by intro currentContext childScope id lowered reached given; simpa only [shell.canonical] using given)
    shell.syntaxTree (shell.canonical.symm ▸ shell.syntaxTree) shell.projection
    (SiteShell.extraction root expressionSyntax site shell policyEq bodyEq reasonEq)
    (CallableIndexedOwnedPreparedLambdaBodyNativeInversion.body_native site.code)

end Site
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeCompilerChildren
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedLambdaOccurrenceNativeTyping
/-! Native inversion at an actual emitted compiler occurrence initially gives
an existential result type. The genuine lambda hook and callable decoration fix
that type through their literal annotations. This normalization retains the
original accepted certificate and native context; it constructs no Source
lookup, Source typing, selected implementation or body execution law. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedLambdaOccurrenceNativeTyping
open Core Frontend SourceInference
open CallableIndexedLambdaCertificates

private theorem descriptor_exists (table : SourceCoreStageCodebook.Table)
    {origin : SourceCoreStageCodebook.Origin} {id : Word}
    (selected : table.idAt? origin = some id) :
    Nonempty (SourceCoreCallableContracts.Descriptor table origin) := by
  cases accepted : SourceCoreCallableContracts.descriptor table origin with
  | error error =>
    unfold SourceCoreCallableContracts.descriptor at accepted
    split at accepted
    · rename_i absent
      rw [selected] at absent
      cases absent
    · cases accepted
  | ok descriptor => exact ⟨descriptor⟩

/-- The selected snapshot has literal lambda annotations. Any typing of that
same expression fixes its result; no second expected typing is assumed. -/
theorem snapshot_result {definitions : DataEnvironment} {context : Core.Context}
    (table : SourceCoreCallableIndexedDispatch.Table) (layout : SourceCoreCallableIndexedFrames.Layout)
    (origin : Word) (referenceIndex : Nat) (parameter result : Ty) (body : Expr)
    {nativeType : Ty}
    (typed : HasType context
      (SourceCoreCallableIndexedAncestry.snapshotLambda table layout origin referenceIndex parameter result body)
      nativeType definitions) :
    nativeType = .function parameter (LanguageResult.resultType result) := by
  cases typed with
  | letE _ closure =>
    cases closure
    rfl

/-- The actual anonymous identity and descriptor word remain in their
original product order. Constructor inversion fixes the full result type. -/
theorem decorated_snapshot_result {definitions : DataEnvironment} {context : Core.Context}
    {table : SourceCoreStageCodebook.Table} {origin : SourceCoreStageCodebook.Origin}
    (descriptor : SourceCoreCallableContracts.Descriptor table origin)
    (dispatch : SourceCoreCallableIndexedDispatch.Table) (layout : SourceCoreCallableIndexedFrames.Layout)
    (selected : Word) (referenceIndex : Nat) (parameter result : Ty) (body : Expr)
    {nativeType : Ty}
    (typed : HasType context
      (LanguageResult.success (descriptor.wrap (TaggedFunction.anonymous
        (SourceCoreCallableIndexedAncestry.snapshotLambda dispatch layout selected referenceIndex parameter result body))))
      nativeType definitions) :
    nativeType = LanguageResult.resultType (CallableContract.functionType parameter result) := by
  cases typed with
  | inRight _ wrapped =>
    cases wrapped with
    | pair tagged contract =>
      cases contract
      cases tagged with
      | pair identity closure =>
        cases identity with
        | inLeft _ unit =>
          cases unit
          have same := snapshot_result dispatch layout selected referenceIndex parameter result body closure
          cases same
          rfl

/-- Renaming keeps the literal annotations of the decorated snapshot, so any
typing of a renamed copy fixes the same result. -/
theorem decorated_snapshot_result_rename {definitions : DataEnvironment} {context : Core.Context}
    {table : SourceCoreStageCodebook.Table} {origin : SourceCoreStageCodebook.Origin}
    (descriptor : SourceCoreCallableContracts.Descriptor table origin)
    (dispatch : SourceCoreCallableIndexedDispatch.Table) (layout : SourceCoreCallableIndexedFrames.Layout)
    (selected : Word) (referenceIndex : Nat) (parameter result : Ty) (body : Expr) (σ : Renaming)
    {nativeType : Ty}
    (typed : HasType context
      ((LanguageResult.success (descriptor.wrap (TaggedFunction.anonymous
        (SourceCoreCallableIndexedAncestry.snapshotLambda dispatch layout selected referenceIndex parameter result
          body)))).rename σ)
      nativeType definitions) :
    nativeType = LanguageResult.resultType (CallableContract.functionType parameter result) := by
  cases typed with
  | inRight _ wrapped =>
    cases wrapped with
    | pair tagged contract =>
      cases contract
      cases tagged with
      | pair identity closure =>
        cases identity with
        | inLeft _ unit =>
          cases unit
          cases closure with
          | letE _ lambda =>
            cases lambda
            rfl

/-- A typed copy chain types its innermost expression at the same type, in a
context extended by the copies. Only the chain's `let`s are inverted, so this
holds for any allocator. -/
private theorem copyChain_type {definitions : DataEnvironment} {allocator : Option SourceCoreSourceCells.Allocator}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {base : Nat → Nat} (inner : Expr) :
    ∀ (rest : SourceCoreLocalCell.Scope) (index ordinal : Nat) {emitted : Expr} {context : Core.Context} {type : Ty},
      SourceCoreSourceCells.copyChain allocator source scope base rest index ordinal inner = .ok emitted →
      HasType context emitted type definitions → ∃ extended, HasType extended inner type definitions := by
  intro rest
  induction rest with
  | nil =>
    intro index ordinal emitted context type accepted typed
    simp only [SourceCoreSourceCells.copyChain, pure, Except.pure, Except.ok.injEq] at accepted
    subst accepted
    exact ⟨context, typed⟩
  | cons slot rest ih =>
    intro index ordinal emitted context type accepted typed
    obtain ⟨id, slotType⟩ := slot
    cases copied : SourceSemantics.CaptureBinders.copiedBinder? source id with
    | none =>
      simp only [SourceCoreSourceCells.copyChain, copied] at accepted
      exact ih (index + 1) ordinal accepted typed
    | some binder =>
      simp only [SourceCoreSourceCells.copyChain, copied] at accepted
      cases copyAccepted : SourceCoreSourceCells.copyCell allocator source scope
          (SourceCoreSourceCells.copyReferences source scope binder base ordinal) binder slotType
          (.var (base index + ordinal)) with
      | error error => simp [copyAccepted, bind, Except.bind] at accepted
      | ok copy =>
        cases chainAccepted : SourceCoreSourceCells.copyChain allocator source scope base rest (index + 1)
            (ordinal + 1) inner with
        | error error => simp [copyAccepted, chainAccepted, bind, Except.bind] at accepted
        | ok continuation =>
          simp only [copyAccepted, chainAccepted, bind, Except.bind, pure, Except.pure,
            Except.ok.injEq] at accepted
          subst accepted
          cases typed with
          | letE _ body => exact ih (index + 1) (ordinal + 1) chainAccepted body

/-- One authentic compiler lambda certificate normalizes the raw child
typing obtained from its actual enclosing body. Descriptor existence is derived
from that hook's selected codebook row, before any Code/Site is constructed. -/
theorem certificate_native {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCallableIndexedPrograms.Prepared checked)
    {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {compilation : SourceCoreFunctions.Context} {view : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
    {reported : Ty} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : Certificate policy lowerBody fuel compilation view scope id node parameters result statements reported reasonAt lowered)
    (found : view.lookupExpression? id = some node)
    (expressionHook : policy.rawLambdaExpression =
      SourceCoreCallableIndexedAncestry.expressionHook prepared.ancestry compilation.owner [])
    (callables : policy.callables =
      SourceCoreGeneralFunctions.callablePolicy (some prepared.ancestry.graph.inputs.callable) [])
    {nativeContext : Core.Context} {nativeType : Ty}
    (typed : HasType nativeContext lowered.expression nativeType prepared.layouts.definitions) :
    HasType nativeContext lowered.expression (LanguageResult.resultType lowered.type) prepared.layouts.definitions := by
  obtain ⟨origin, body, selected, _raw, _owner, _globals, _source, emitted⟩ :=
    CallableIndexedFormation.expressionHook_receipt prepared.ancestry (expressionHook ▸ receipt.expressionHook)
  rw [(lookupExpression?_sound found).2] at selected
  obtain ⟨descriptor⟩ := descriptor_exists _ selected
  have decorated := receipt.decoration
  rw [callables, ActualCallablePolicy.lambda_decoration _ [] compilation view node id
    receipt.parameterCore receipt.resultCore _ descriptor] at decorated
  have sameExpression := Except.ok.inj decorated
  have snapshotted : HasType nativeContext receipt.snapshotted nativeType prepared.layouts.definitions := by
    simpa only [receipt.emitted] using typed
  have renamed : ∃ extended σ, HasType extended (receipt.expression.rename σ) nativeType
      prepared.layouts.definitions := by
    have snapshot := receipt.snapshot
    split at snapshot
    · obtain ⟨extended, copiedTyped⟩ := copyChain_type _ scope 0 0 snapshot snapshotted
      exact ⟨extended, _, copiedTyped⟩
    · have same := Except.ok.inj snapshot
      rw [← same] at snapshotted
      exact ⟨nativeContext, Renaming.id, by rw [Expr.rename_id]; exact snapshotted⟩
  obtain ⟨extended, σ, rawTyped⟩ := renamed
  rw [← sameExpression, emitted] at rawTyped
  have exactType := decorated_snapshot_result_rename descriptor prepared.ancestry.graph.table
    prepared.ancestry.layout.frame origin (SourceCoreCallableIndexedAncestry.creationReferenceIndex compilation scope)
    receipt.parameterCore receipt.resultCore body σ rawTyped
  have checkedType := receipt.checked
  rw [callables] at checkedType
  unfold SourceCoreBasic.ensureType at checkedType
  split at checkedType
  · rename_i reportedType
    change reported = CallableContract.functionType receipt.parameterCore receipt.resultCore at reportedType
    have expected : nativeType = LanguageResult.resultType lowered.type := by
      simpa only [receipt.emitted, reportedType] using exactType
    exact expected ▸ typed
  · cases checkedType

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedLambdaOccurrenceNativeTyping
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeLambdaCompilerReceipts
/-! One actual raw compiler lambda occurrence produces its native-aware body.
The literal accepted Certificate and independently typed Source row are retained.
Raw enclosing native typing is normalized by the emitted callable constructors;
one Site is then built at the actual Named entry prefix. Its static shell builds
one JointBody through the native compiler traversal, with no separately typed
body or assignment supplier. Ordinary and selected-method callers use their
real Named compilation and evidence. Existing broad collected bodies do not
acquire this receipt. The concrete issuer/static shell producer remains open. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeLambdaCompilerReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration CallableIndexedLambdaValues
open CallableIndexedOwnedContextualCompilerPolicyProfiles
open CallableIndexedOwnedContextualLambdaJointStaticReceipts
open CallableIndexedOwnedPreparedNativeCompilerChildren
open CallableIndexedOwnedPreparedCanonicalCaptureReceipts («prefix»)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {named : Named}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : Compilation compiled.indexed named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) named diagnostics namedCode compilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  (expressionSyntax : TypedSource → ExpressionId → Prop)
  {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  {node : ExpressionNode} {parameters : List TypedBinder} {result : TypeSystem.Ty}
  {statements : List StatementId} {reported : Ty} {childFuel : Nat}
  (certificate : CallableIndexedLambdaCertificates.Certificate root.selected.policy root.selected.lowerBody childFuel
    (context compiled.indexed named) (source named) scope id node parameters result statements reported rootReasonAt lowered)

/-- This positive packet contains the actual chosen Site and one native-aware
body under Type. It is produced only from a literal accepted compiler occurrence. -/
structure Receipt where
  site : Site compiled.indexed named parameters result statements sourceContext evidence []
    scope («prefix» (compiled := compiled) named)
  identifier : site.code.id = id
  emitted : site.code.lowered = lowered
  policy : site.code.policy = root.selected.policy
  lowerBody : site.code.lowerBody = root.selected.lowerBody
  fuel : site.code.fuel = childFuel
  view : site.code.view = source named
  reason : site.code.reasonAt = rootReasonAt
  sourceNodeEq : site.code.sourceNode = node
  nodeEq : site.code.node = node
  certificateEq : HEq site.code.receipt certificate
  binderPolicy : CallableIndexedOwnedContextualLambdaProvenance.BinderPolicy named site.code
  shell : SiteShell (compilation := compilation) expressionSyntax site
  body : JointBody compilation site.code (Program.ofChecked compiled.sourceProgram)
    expressionSyntax (certificates root expressionSyntax («prefix» (compiled := compiled) named)) shell.diagnosticPolicy
    shell.issued.invalidOperand shell.issued.invalidUnary shell.issued.invalidProjection shell.issued.missingDefault
  entry : body.toContext = shell.entry
  readFuel : body.readFuel = shell.readFuel
  sourceFacts : CallableIndexedOwnedOrdinaryLambdaSourceFacts.Facts
    (closure named parameters result statements sourceContext evidence []) id node

/-- The real shell and the actual root policy retain the same compilation. -/
theorem Receipt.issued_recipe (receipt : Receipt root expressionSyntax certificate
    (sourceContext := sourceContext) (evidence := evidence)) :
    CallableIndexedOwnedContextualLambdaIssuedRecipes.Retained named receipt.site.code := by
  have policy := root.compilerPolicy
  rw [← receipt.policy] at policy
  exact CallableIndexedOwnedContextualLambdaIssuedRecipes.Retained.of_recipes
    compilation receipt.shell.issuedCompilation
    (receipt.lowerBody.trans root.selected.recipe) policy receipt.site.compilation

/-- The same occurrence builds its literal prefix Site and native JointBody.
The shell callback supplies only actual Source/issuance/policy metadata for the
Site just generated. It cannot supply body typing or any execution theorem. -/
theorem of_certificate
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) sourceContext (source named))
    (covers : evidence.Covers sourceContext)
    (found : (source named).lookupExpression? id = some node)
    (form : node.form = .lambda parameters result statements)
    (sourceTyped : ExpressionHasType (source named) sourceContext id node.type)
    (coercions : node.coercions = [])
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody (childFuel + 1)
      (context compiled.indexed named) (source named) scope id rootReasonAt = .ok lowered)
    {nativeType : Ty}
    (raw : HasType (SourceCoreLocalCell.coreContext scope ++ «prefix» (compiled := compiled) named)
      lowered.expression nativeType compiled.indexed.layouts.definitions)
    (shells : ∀ site : Site compiled.indexed named parameters result statements sourceContext evidence []
        scope («prefix» (compiled := compiled) named),
      site.code.id = id → site.code.lowered = lowered → site.code.policy = root.selected.policy →
      site.code.lowerBody = root.selected.lowerBody → site.code.fuel = childFuel →
      site.code.view = source named → site.code.reasonAt = rootReasonAt →
      Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram)
        (closure named parameters result statements sourceContext evidence []) →
      Nonempty (SiteShell (compilation := compilation) expressionSyntax site)) :
    Nonempty (Receipt root expressionSyntax certificate
      (sourceContext := sourceContext) (evidence := evidence)) := by
  have native := CallableIndexedOwnedPreparedLambdaOccurrenceNativeTyping.certificate_native
    compiled.indexed certificate found root.rawLambdaExpression root.callables raw
  obtain ⟨site, identifier, emitted, policy, lowerBody, fuel, view, reason,
      sourceNode, actualNode, sameCertificate⟩ :=
    CallableIndexedLambdaGeneration.of_certificate compiled.indexed sourceContext evidence [] certificate accepted
      profile (LambdaMetadataViews.MetadataView.refl _) found form found rfl
      root.sourceCells root.rawLambdaBody root.rawLambdaExpression root.callables root.projectType
      (by rw [root.compilerPolicy.snapshotLambda]) native
  have facts := CallableIndexedOwnedOrdinaryLambdaSourceFacts.of_typed
    (function := closure named parameters result statements sourceContext evidence [])
    runtime.graph.nodeOccurrencesUnique found form sourceTyped coercions
  obtain ⟨shell⟩ := shells site identifier emitted policy lowerBody fuel view reason (facts.frame runtime covers)
  obtain ⟨body, entry, readFuel⟩ :=
    SiteShell.joint root expressionSyntax site shell policy lowerBody reason
  have binderPolicy : CallableIndexedOwnedContextualLambdaProvenance.BinderPolicy named site.code :=
    (congrArg SourceCoreFunctions.Policy.lowerBinder policy).trans root.selected.binder
  exact ⟨⟨site, identifier, emitted, policy, lowerBody, fuel, view, reason,
    sourceNode, actualNode, sameCertificate, binderPolicy, shell, body, entry, readFuel, facts⟩⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeLambdaCompilerReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeCollectedQualification
/-! The concrete semantic domain retains the native-aware body generated at
one actual compiler lambda occurrence. The ordinary constructor keeps its real
Header membership; the Principal constructor keeps its actual selected method
and dictionary. Each body contains local raw child witnesses from the original
compiler traversal. Recapture retains that body and its literal Named prefix.
The original unrestricted or broad compiled qualifiers have no inverse here.
Finite raw Trees are constructed from these authentic child actions, while the
shared execution induction and concrete public static inputs remain open. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeCollectedQualification
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedContextualCompilerPolicyProfiles
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedContextualQualification (Facet)
open CallableIndexedOwnedPreparedNativeLambdaCompilerReceipts (Receipt)
open CallableIndexedOwnedPreparedCanonicalCaptureReceipts («prefix»)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}

/-- The only ordinary leaf is the same positive compiler Receipt, body and
recaptured environment. Actual Header membership remains explicit. -/
inductive Ordinary (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))) :
    {function : Dynamic.Closure} → {scope : SourceCoreLocalCell.Scope} → {administrative : Core.Context} →
    (code : Code compiled.indexed function scope administrative) →
    CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Support code → Prop where
  | actual {caller : Header compiled (Program.ofChecked compiled.sourceProgram)}
      (member : caller ∈ headers)
      {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
      {compilation : Compilation compiled.indexed caller.named diagnostics namedCode}
      {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
      {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
      (root : RootPolicyReceipt (compiled := compiled) caller.named diagnostics namedCode compilation
        rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
      (expressionSyntax : TypedSource → ExpressionId → Prop)
      {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
      {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
      {node : ExpressionNode} {parameters : List TypedBinder} {result : TypeSystem.Ty}
      {statements : List StatementId} {reported : Ty} {childFuel : Nat}
      (certificate : CallableIndexedLambdaCertificates.Certificate root.selected.policy root.selected.lowerBody childFuel
        (context compiled.indexed caller.named) (source caller.named) scope id node parameters result statements
        reported rootReasonAt lowered)
      (receipt : Receipt root expressionSyntax certificate (sourceContext := sourceContext) (evidence := evidence))
      (bodyReasons : CallableIndexedOwnedContextualLambdaProvenance.BodyReasons receipt.site.code caller.named)
      (declarations : CompatibleExpressionReads.ScopeDeclarations
        (source caller.named) scope sourceContext)
      (environment : Dynamic.Environment) :
      Ordinary headers
        (RecursiveNamedLambdaFormationHeads.recaptureCode
          (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) receipt.site.code environment)
        ((CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Support.of_site
          caller compilation receipt.site expressionSyntax
          (CallableIndexedOwnedPreparedNativeCompilerChildren.certificates root expressionSyntax
            («prefix» (compiled := compiled) caller.named))
          receipt.shell.issued receipt.shell.diagnosticPolicy receipt.body).recapture environment)

/-- The method leaf retains its full selector and literal dictionary. No
ordinary Header or arbitrary administrative-context equality is constructed. -/
inductive Principal : {function : Dynamic.Closure} → {scope : SourceCoreLocalCell.Scope} →
    {administrative : Core.Context} → (code : Code compiled.indexed function scope administrative) →
    CallableIndexedOwnedPreparedPrincipalLambdaSupport.Support code → Prop where
  | actual {method : ExecutableImplMethods.CheckedMethod}
      (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
      {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
      {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
      (root : RootPolicyReceipt (compiled := compiled) principal.named principal.cached.diagnostics principal.cached.code
        principal.cached.compilation rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
      (expressionSyntax : TypedSource → ExpressionId → Prop)
      {sourceContext : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
      {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
      {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
      {reported : Ty} {childFuel : Nat}
      (certificate : CallableIndexedLambdaCertificates.Certificate root.selected.policy root.selected.lowerBody childFuel
        (context compiled.indexed principal.named) (source principal.named) scope id node parameters result statements
        reported rootReasonAt lowered)
      (receipt : Receipt root expressionSyntax certificate
        (sourceContext := sourceContext) (evidence := principal.dictionary))
      (environment : Dynamic.Environment) :
      Principal
        (RecursiveNamedLambdaFormationHeads.recaptureCode
          (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) receipt.site.code environment)
        ((CallableIndexedOwnedPreparedPrincipalLambdaSupport.Support.of_site principal receipt.site expressionSyntax
          (CallableIndexedOwnedPreparedNativeCompilerChildren.certificates root expressionSyntax
            («prefix» (compiled := compiled) principal.named))
          receipt.shell.issued receipt.shell.diagnosticPolicy receipt.body).recapture environment)

/-- Generic qualified payload and heap APIs use this one static facet. -/
def facet (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))) : Facet compiled where
  ordinary := Ordinary headers
  principal := Principal

theorem ordinary_prepared {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {code : Code compiled.indexed function scope administrative}
    {support : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Support code}
    (qualified : Ordinary headers code support) :
    CallableIndexedOwnedPreparedOrdinaryLambdaSupport.PreparedAt code support := by
  cases qualified with
  | actual member root expressionSyntax certificate receipt bodyReasons declarations environment =>
      exact .recaptured _ _ receipt.site expressionSyntax
        (CallableIndexedOwnedPreparedNativeCompilerChildren.certificates root expressionSyntax («prefix» (compiled := compiled) _))
        receipt.shell.issued receipt.shell.diagnosticPolicy receipt.body receipt.binderPolicy
        (by
          have policy := root.compilerPolicy
          rw [← receipt.policy] at policy
          exact CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained.of_recipes _
            (receipt.lowerBody.trans root.selected.recipe) policy receipt.site.compilation)
        (receipt.issued_recipe root expressionSyntax certificate)
        (CallableIndexedOwnedContextualLambdaProvenance.BodyView.of_eq receipt.view) bodyReasons declarations environment

theorem principal_prepared
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {code : Code compiled.indexed function scope administrative}
    {support : CallableIndexedOwnedPreparedPrincipalLambdaSupport.Support code}
    (qualified : Principal code support) :
    CallableIndexedOwnedPreparedPrincipalLambdaSupport.PreparedAt code support := by
  cases qualified with
  | actual principal root expressionSyntax certificate receipt environment =>
      exact .recaptured principal receipt.site expressionSyntax
        (CallableIndexedOwnedPreparedNativeCompilerChildren.certificates root expressionSyntax («prefix» (compiled := compiled) principal.named))
        receipt.shell.issued receipt.shell.diagnosticPolicy receipt.body receipt.binderPolicy
        (by
          have policy := root.compilerPolicy
          rw [← receipt.policy] at policy
          exact CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained.of_recipes _
            (receipt.lowerBody.trans root.selected.recipe) policy receipt.site.compilation)
        (receipt.issued_recipe root expressionSyntax certificate)
        (CallableIndexedOwnedContextualLambdaProvenance.BodyView.of_eq receipt.view) environment

section Occurrence
variable {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : Compilation compiled.indexed named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) named diagnostics namedCode compilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  (expressionSyntax : TypedSource → ExpressionId → Prop)
  {sourceContext : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {readFuel : Nat}
  (callerEvidence : Option Dynamic.EvidenceEnvironment)
  (headers : RecursiveNamedCatalog.Inventory compiled.indexed.ancestry (.initial compiled.compatible.checked)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions (Program.ofChecked compiled.sourceProgram))

/-- Forget only the local native witness to the original authentic compiler
action. This is a direct constructor projection, not a broad receipt inverse. -/
theorem accepted_action {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : CallableIndexedOwnedPreparedNativeCompilerChildren.AcceptedAt root expressionSyntax
      («prefix» (compiled := compiled) named) readFuel (source named) sourceContext scope id lowered) :
    CallableIndexedOwnedPreparedPrincipalCompilerChildren.AcceptedAt root expressionSyntax
      readFuel (source named) sourceContext scope id lowered := by
  cases accepted with
  | intro found typed allowed declarations closed residual signatures action raw =>
      exact .intro found typed allowed declarations closed residual signatures action

/-- The actual compiler-fuel producer constructs the finite skeleton at this
retained child action. Its local native witness is kept at the exact same output;
unused Entries do not acquire typing. The later E fold consumes used slots only. -/
theorem tree_at_occurrence
    (domain : CallableIndexedOwnedPreparedRawCompilerHeads.Domain root expressionSyntax callerEvidence headers
      (sourceContext := sourceContext) (scope := scope) (readFuel := readFuel))
    (unique : NodeOccurrencesUnique (source named))
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : CallableIndexedOwnedPreparedNativeCompilerChildren.AcceptedAt root expressionSyntax
      («prefix» (compiled := compiled) named) readFuel (source named) sourceContext scope id lowered) :
    RecursiveNamedExpressionCompilerCertificates.RuntimeExpressionsFor
      (CallableIndexedOwnedPreparedRawCompilerHeads.Head root expressionSyntax callerEvidence headers
        (sourceContext := sourceContext) (scope := scope))
      readFuel (.initial compiled.compatible.checked) (source named) sourceContext
      (context compiled.indexed named).solvedRequirements rootReasonAt scope id lowered ∧
      ∃ nativeType, HasType (SourceCoreLocalCell.coreContext scope ++ «prefix» (compiled := compiled) named)
        lowered.expression nativeType compiled.indexed.layouts.definitions := by
  have tree := CallableIndexedOwnedPreparedRawCompilerHeads.tree_of_accepted root expressionSyntax
    callerEvidence headers domain unique (accepted_action root expressionSyntax accepted)
  refine ⟨tree, ?_⟩
  cases accepted with
  | intro found typed allowed declarations closed residual signatures action raw => exact ⟨_, raw⟩

end Occurrence
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeCollectedQualification
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeFamilyStaticQualification
/-! Intermediate static qualification for the one collected family. Each
retained compiler occurrence supplies the original finite raw Domain at its
actual context/scope/read fuel. The original finite producer constructs the
same Tree; its own raw native witness is paired with that Tree.

No field stores a Tree, an expression meaning or a body execution law. The
actual compiler must still manufacture these static Domain packets for every
supported evidence/coercion/generalized alternative. Existing broad native
qualification has only a forward projection from this stronger domain. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeFamilyStaticQualification
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedContextualCompilerPolicyProfiles
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedContextualQualification (Facet)
open CallableIndexedOwnedPreparedNativeLambdaCompilerReceipts (Receipt)
open CallableIndexedOwnedPreparedCanonicalCaptureReceipts («prefix»)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}

section Factory
variable {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : Compilation compiled.indexed named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) named diagnostics namedCode compilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  (expressionSyntax : TypedSource → ExpressionId → Prop)
  (callerEvidence : Option Dynamic.EvidenceEnvironment)
  (headers : RecursiveNamedCatalog.Inventory compiled.indexed.ancestry (.initial compiled.compatible.checked)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions (Program.ofChecked compiled.sourceProgram))
  (readFuel : Nat)

/-- The input is the literal retained AcceptedAt, including its independent
Source facts and raw native witness. Domain carries only finite compiler facts;
its empty/coercion restrictions are not conclusions of ProgramWellFormed. -/
structure OccurrenceFactory : Prop where
  domain : ∀ {currentContext currentScope id lowered},
    CallableIndexedOwnedPreparedNativeCompilerChildren.AcceptedAt root expressionSyntax
      («prefix» (compiled := compiled) named) readFuel (source named) currentContext currentScope id lowered →
    CallableIndexedOwnedPreparedRawCompilerHeads.Domain root expressionSyntax callerEvidence headers
      (sourceContext := currentContext) (scope := currentScope) (readFuel := readFuel)

/-- One genuine finite compiler-fuel construction at the SAME accepted child.
The native witness is its own retained witness; unused child slots gain none. -/
theorem OccurrenceFactory.runtime_tree
    (factory : OccurrenceFactory root expressionSyntax callerEvidence headers readFuel)
    (unique : NodeOccurrencesUnique (source named))
    {currentContext currentScope id lowered}
    (accepted : CallableIndexedOwnedPreparedNativeCompilerChildren.AcceptedAt root expressionSyntax
      («prefix» (compiled := compiled) named) readFuel (source named) currentContext currentScope id lowered) :
    CallableIndexedOwnedPreparedReachedNativeExpressionTreeBounds.RuntimeTree
      (sourceContext := currentContext) (compilerScope := currentScope) (fuel := readFuel)
      (solved := (context compiled.indexed named).solvedRequirements)
      root expressionSyntax callerEvidence headers («prefix» (compiled := compiled) named)
      currentScope id lowered := by
  obtain ⟨tree, raw⟩ := CallableIndexedOwnedPreparedNativeCollectedQualification.tree_at_occurrence
    root expressionSyntax callerEvidence headers (factory.domain accepted) unique accepted
  exact ⟨tree, raw⟩
end Factory

/-- The only ordinary leaf is the same positive compiler Receipt, body and
recaptured environment. Actual Header membership remains explicit. -/
inductive Ordinary (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))) :
    {function : Dynamic.Closure} → {scope : SourceCoreLocalCell.Scope} → {administrative : Core.Context} →
    (code : Code compiled.indexed function scope administrative) →
    CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Support code → Prop where
  | actual {caller : Header compiled (Program.ofChecked compiled.sourceProgram)}
      (member : caller ∈ headers)
      {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
      {compilation : Compilation compiled.indexed caller.named diagnostics namedCode}
      {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
      {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
      (root : RootPolicyReceipt (compiled := compiled) caller.named diagnostics namedCode compilation
        rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
      (expressionSyntax : TypedSource → ExpressionId → Prop)
      {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
      {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
      {node : ExpressionNode} {parameters : List TypedBinder} {result : TypeSystem.Ty}
      {statements : List StatementId} {reported : Ty} {childFuel : Nat}
      (certificate : CallableIndexedLambdaCertificates.Certificate root.selected.policy root.selected.lowerBody childFuel
        (context compiled.indexed caller.named) (source caller.named) scope id node parameters result statements
        reported rootReasonAt lowered)
      (receipt : Receipt root expressionSyntax certificate (sourceContext := sourceContext) (evidence := evidence))
      (bodyReasons : CallableIndexedOwnedContextualLambdaProvenance.BodyReasons receipt.site.code caller.named)
      (declarations : CompatibleExpressionReads.ScopeDeclarations
        (source caller.named) scope sourceContext)
      (factory : OccurrenceFactory root expressionSyntax (some evidence) headers receipt.body.readFuel)
      (environment : Dynamic.Environment) :
      Ordinary headers
        (RecursiveNamedLambdaFormationHeads.recaptureCode
          (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) receipt.site.code environment)
        ((CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Support.of_site
          caller compilation receipt.site expressionSyntax
          (CallableIndexedOwnedPreparedNativeCompilerChildren.certificates root expressionSyntax
            («prefix» (compiled := compiled) caller.named))
          receipt.shell.issued receipt.shell.diagnosticPolicy receipt.body).recapture environment)

/-- The method leaf retains its full selector and literal dictionary. No
ordinary Header or arbitrary administrative-context equality is constructed. -/
inductive Principal (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))) : {function : Dynamic.Closure} → {scope : SourceCoreLocalCell.Scope} →
    {administrative : Core.Context} → (code : Code compiled.indexed function scope administrative) →
    CallableIndexedOwnedPreparedPrincipalLambdaSupport.Support code → Prop where
  | actual {method : ExecutableImplMethods.CheckedMethod}
      (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
      {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
      {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
      (root : RootPolicyReceipt (compiled := compiled) principal.named principal.cached.diagnostics principal.cached.code
        principal.cached.compilation rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
      (expressionSyntax : TypedSource → ExpressionId → Prop)
      {sourceContext : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
      {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
      {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
      {reported : Ty} {childFuel : Nat}
      (certificate : CallableIndexedLambdaCertificates.Certificate root.selected.policy root.selected.lowerBody childFuel
        (context compiled.indexed principal.named) (source principal.named) scope id node parameters result statements
        reported rootReasonAt lowered)
      (receipt : Receipt root expressionSyntax certificate
        (sourceContext := sourceContext) (evidence := principal.dictionary))
      (factory : OccurrenceFactory root expressionSyntax (some principal.dictionary) headers receipt.body.readFuel)
      (environment : Dynamic.Environment) :
      Principal headers
        (RecursiveNamedLambdaFormationHeads.recaptureCode
          (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) receipt.site.code environment)
        ((CallableIndexedOwnedPreparedPrincipalLambdaSupport.Support.of_site principal receipt.site expressionSyntax
          (CallableIndexedOwnedPreparedNativeCompilerChildren.certificates root expressionSyntax
            («prefix» (compiled := compiled) principal.named))
          receipt.shell.issued receipt.shell.diagnosticPolicy receipt.body).recapture environment)

/-- Generic qualified payload and heap APIs use this one static facet. -/
def facet (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))) : Facet compiled where
  ordinary := Ordinary headers
  principal := Principal headers

theorem ordinary_prepared {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {code : Code compiled.indexed function scope administrative}
    {support : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Support code}
    (qualified : Ordinary headers code support) :
    CallableIndexedOwnedPreparedOrdinaryLambdaSupport.PreparedAt code support := by
  cases qualified with
  | actual member root expressionSyntax certificate receipt bodyReasons declarations factory environment =>
      exact .recaptured _ _ receipt.site expressionSyntax
        (CallableIndexedOwnedPreparedNativeCompilerChildren.certificates root expressionSyntax («prefix» (compiled := compiled) _))
        receipt.shell.issued receipt.shell.diagnosticPolicy receipt.body receipt.binderPolicy
        (by
          have policy := root.compilerPolicy
          rw [← receipt.policy] at policy
          exact CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained.of_recipes _
            (receipt.lowerBody.trans root.selected.recipe) policy receipt.site.compilation)
        (receipt.issued_recipe root expressionSyntax certificate)
        (CallableIndexedOwnedContextualLambdaProvenance.BodyView.of_eq receipt.view) bodyReasons declarations environment

theorem principal_prepared {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {code : Code compiled.indexed function scope administrative}
    {support : CallableIndexedOwnedPreparedPrincipalLambdaSupport.Support code}
    (qualified : Principal headers code support) :
    CallableIndexedOwnedPreparedPrincipalLambdaSupport.PreparedAt code support := by
  cases qualified with
  | actual principal root expressionSyntax certificate receipt factory environment =>
      exact .recaptured principal receipt.site expressionSyntax
        (CallableIndexedOwnedPreparedNativeCompilerChildren.certificates root expressionSyntax («prefix» (compiled := compiled) principal.named))
        receipt.shell.issued receipt.shell.diagnosticPolicy receipt.body receipt.binderPolicy
        (by
          have policy := root.compilerPolicy
          rw [← receipt.policy] at policy
          exact CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained.of_recipes _
            (receipt.lowerBody.trans root.selected.recipe) policy receipt.site.compilation)
        (receipt.issued_recipe root expressionSyntax certificate)
        (CallableIndexedOwnedContextualLambdaProvenance.BodyView.of_eq receipt.view) environment

/-- Forward compiler qualification preserves exactly the same Code/body.
There is no projection back from the broad native facet. -/
theorem ordinary_native {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {code : Code compiled.indexed function scope administrative}
    {support : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Support code}
    (qualified : Ordinary headers code support) :
    CallableIndexedOwnedPreparedNativeCollectedQualification.Ordinary headers code support := by
  cases qualified with
  | actual member root expressionSyntax certificate receipt bodyReasons declarations factory environment =>
      exact .actual member root expressionSyntax certificate receipt bodyReasons declarations environment

theorem principal_native {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {code : Code compiled.indexed function scope administrative}
    {support : CallableIndexedOwnedPreparedPrincipalLambdaSupport.Support code}
    (qualified : Principal headers code support) :
    CallableIndexedOwnedPreparedNativeCollectedQualification.Principal code support := by
  cases qualified with
  | actual principal root expressionSyntax certificate receipt factory environment =>
      exact .actual principal root expressionSyntax certificate receipt environment

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeFamilyStaticQualification
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeSitePolicies
/-! Static policies for the exact lambda Site under a real Named compilation.
The same producer applies to an ordinary caller and a selected method. The
original assignment table and issued place providers remain explicit compiler
identities. No Source syntax, body typing, or execution law is inferred here. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeSitePolicies
open Core Frontend SourceInference
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration CallableIndexedLambdaValues
open CallableIndexedOwnedContextualCompilerPolicyProfiles
open CallableIndexedOwnedContextualLambdaJointStaticReceipts
open CallableIndexedOwnedContextualLambdaSourceDiagnostics
open CallableIndexedOwnedLiteralPlaceDiagnosticShells (PlaceReasonsEq)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {named : Named}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  (compilation : Compilation compiled.indexed named diagnostics namedCode)
  {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
  {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (site : Site compiled.indexed named parameters result statements sourceContext evidence [] scope administrative)

/-- Keep the actual body callback's allocator and solved requirement ledger. -/
def baseMatch : SourceCoreCompatibleDataMatches.Context :=
  ⟨.initial compiled.compatible.checked, (context compiled.indexed named).solvedRequirements,
    (bodyPolicy compilation site.code).sourceCells, none⟩

/-- Only the definition environment changes when matching under the indexed program. -/
def ambientMatch : SourceCoreCompatibleDataMatches.Context :=
  CompatibleMatchAmbientLowering.withDefinitions (baseMatch compilation site) compiled.indexed.layouts.definitions

theorem match_policy : CompatibleMatchAmbientLowering.PolicySuccess
    (bodyPolicy compilation site.code) (ambientMatch compilation site) := by
  apply CompatibleMatchAmbientLowering.PolicySuccess.extend
    (compilation := baseMatch compilation site)
  · rfl
  · exact ⟨_, CallableIndexedAmbient.definitions_exact compiled.indexed⟩

theorem match_values : (ambientMatch compilation site).values = .initial compiled.compatible.checked := rfl

theorem match_definitions : (ambientMatch compilation site).definitions = compiled.indexed.layouts.definitions := rfl

theorem read_policy : (bodyPolicy compilation site.code).readStatement =
    SourceCoreCompatibleDataExpressions.readStatement compiled.compatible.checked := rfl

theorem binder_policy (binder : TypedBinder) (childScope : SourceCoreLocalCell.Scope)
    (monomorphic : binder.scheme.quantified = []) :
    (bodyPolicy compilation site.code).lowerBinder site.code.view childScope binder =
      SourceCoreCompatibleDataExpressions.lowerBinder compiled.compatible.checked site.code.view childScope binder := by
  change SourceCoreGeneralFunctions.contextualBinder _ _ _ _ _ _ _ = _
  simp only [SourceCoreGeneralFunctions.contextualBinder, monomorphic, List.isEmpty_nil, ↓reduceIte]
  rfl

/-- The actual Site layout fixes the hidden physical frame slot. -/
theorem reference_index : site.code.referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length := by
  unfold Code.referenceIndex
  rw [site.compilation]
  rfl

section Allocation
variable {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) named diagnostics namedCode compilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered)

/-- The original root callback and same Site receipt select one allocator. -/
theorem allocation_policy (samePolicy : site.code.policy = root.selected.policy) :
    (bodyPolicy compilation site.code).sourceCells = some
      (SourceCoreCallableIndexedAllocationFrames.allocator compiled.indexed.ancestry.layout.frame
        compiled.indexed.base.globals.length
        (compiled.indexed.layouts.allocatorAt site.code.compilation.owner site.code.active site.code.allocationError)) := by
  have actual : (bodyPolicy compilation site.code).sourceCells = root.selected.policy.sourceCells := by
    rw [root.sourceCells]
    rfl
  exact actual.trans ((congrArg SourceCoreFunctions.Policy.sourceCells samePolicy).symm.trans
    site.code.allocationProfile)

theorem match_allocator (samePolicy : site.code.policy = root.selected.policy) :
    (ambientMatch compilation site).sourceCells = some
      (SourceCoreCallableIndexedAllocationFrames.allocator compiled.indexed.ancestry.layout.frame
        compiled.indexed.base.globals.length
        (compiled.indexed.layouts.allocatorAt site.code.compilation.owner site.code.active site.code.allocationError)) :=
  allocation_policy compilation site root samePolicy
end Allocation

section Diagnostics
variable (issued : IssuedSource compiled site.code.compilation.owner (source named))

private theorem missing_policy
    (samePlaces : PlaceReasonsEq issued.diagnostics.program diagnostics) :
    issued.missingDefault = fun childSite root type =>
      diagnostics.placeReason (context compiled.indexed named).owner childSite root (some type) := by
  funext childSite root type
  change issued.diagnostics.program.placeReason site.code.compilation.owner childSite root (some type) = _
  rw [samePlaces.function_eq, site.compilation]

/-- The exact selected assignment row and place providers construct the body policy. -/
theorem assignment_policy
    (sameAssignments : issued.assignments = compilation.own.assignments)
    (samePlaces : PlaceReasonsEq issued.diagnostics.program diagnostics) :
    CompatibleAssignmentStatements.AssignmentPolicy (bodyPolicy compilation site.code)
      (.initial compiled.compatible.checked) issued.invalidProjection issued.invalidOperand issued.missingDefault := by
  have missing := missing_policy site issued samePlaces
  refine ⟨read_policy compilation site, ?_, ?_⟩
  · rw [missing]
    dsimp only [IssuedSource.invalidProjection, IssuedSource.invalidOperand]
    simp only [sameAssignments, samePlaces.function_eq, site.compilation]
    rfl
  · rw [missing]
    dsimp only [IssuedSource.invalidProjection, IssuedSource.invalidOperand]
    simp only [sameAssignments, samePlaces.function_eq, site.compilation]
    change some _ = some _
    apply congrArg some
    funext expression fuel childSource childScope childSite assignment operator rhs output next reasonAt
    cases operator <;> rfl

/-- Unary assignment keeps those same genuine issued tokens and preparation. -/
theorem unary_policy
    (sameAssignments : issued.assignments = compilation.own.assignments)
    (samePlaces : PlaceReasonsEq issued.diagnostics.program diagnostics) :
    CompatibleBitNotStatements.Policy (bodyPolicy compilation site.code)
      (.initial compiled.compatible.checked) issued.invalidProjection issued.invalidUnary issued.missingDefault := by
  have missing := missing_policy site issued samePlaces
  unfold CompatibleBitNotStatements.Policy
  rw [missing]
  dsimp only [IssuedSource.invalidProjection, IssuedSource.invalidUnary]
  simp only [sameAssignments, samePlaces.function_eq, site.compilation]
  rfl
end Diagnostics
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeSitePolicies
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeSiteShellReceipts
/-! One selected compilation, its positive issuer, and the actual lambda Site
construct the native child collector's static shell. Finite Source body receipts,
parent declarations, and the same solved requirement ledger remain explicit.
Entry, frame, freshness, policy, projection, and diagnostic providers are built
internally. There is no body execution premise or completed JointBody input. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeSiteShellReceipts
open Core Frontend SourceInference
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration CallableIndexedLambdaValues
open CallableIndexedOwnedContextualCompilerPolicyProfiles
open CallableIndexedOwnedContextualLambdaJointStaticReceipts
open CallableIndexedOwnedContextualLambdaSourceDiagnostics
open CallableIndexedOwnedSelectedDiagnosticIssuerReceipts
open RecursiveNamedStatementSyntaxFacts

/-- A finite receipt retains the genuine Source parameter fold and its body
judgment. It authorizes only these parameters and statements at this context;
the original syntax factory still performs the finite body induction. -/
inductive FiniteBodyReceipts (source : TypedSource) (expressionSyntax : ExpressionId → Prop)
    (context : SourceSemantics.Context) (parameters : List TypedBinder)
    (result : TypeSystem.Ty) (statements : List StatementId) : Prop where
  | intro {entryContext finalContext : SourceSemantics.Context}
      {parameterTypes : List TypeSystem.Ty} {facts : BodyFacts} {ready : Bool}
      (extended : MonoBindersExtend source.owner context parameters parameterTypes entryContext)
      (typed : StatementsHaveType source {returnType := result} entryContext statements finalContext facts)
      (receipt : BodyReceipts source expressionSyntax typed ready)
      (annotation : facts.type = result) :
      FiniteBodyReceipts source expressionSyntax context parameters result statements

section Selected
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {named : Named} {index : Nat}
  (selected : SelectedReceipt compiled named index)
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) named (lowered compiled selected.diagnostics)
    selected.code selected.compilation rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  (expressionSyntax : TypedSource → ExpressionId → Prop)
  {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
  {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (site : Site compiled.indexed named parameters result statements sourceContext evidence [] scope administrative)

/-- This issuer is transported only along the actual Site's owning compilation.
Its first token, table, selected assignment row, and full Source are unchanged. -/
def issued_at_site : IssuedSource compiled site.code.compilation.owner (source named) := by
  refine {
    first := selected.issued.first
    assignments := selected.issued.assignments
    assignmentsPrepared := selected.issued.assignmentsPrepared
    typing := selected.issued.typing
    plan := selected.issued.plan
    root := selected.issued.root
    extra := selected.issued.extra
    diagnostics := selected.issued.diagnostics
    prepared := selected.issued.prepared
    collected := ?_ }
  rw [site.compilation]
  exact selected.issued.collected

/-- Every shell field is derived at the literal Site and selected compilation.
An ordinary Header or selected Principal may supply this same genuine Named;
no ordinary Header is manufactured for a method. -/
theorem of_selected
    (samePolicy : site.code.policy = root.selected.policy)
    (canonical : site.code.view = source named)
    (typed : ExpressionHasType (source named) sourceContext site.code.id site.code.sourceNode.type)
    (coercions : site.code.sourceNode.coercions = [])
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
      sourceContext (source named))
    (covers : evidence.Covers sourceContext)
    (ownership : LocalIdentityOwnership (source named))
    (parentDeclarations : CompatibleExpressionReads.ScopeDeclarations (source named) scope sourceContext)
    (sameLedger : sourceContext.solvedRequirements = (context compiled.indexed named).solvedRequirements)
    (finite : FiniteBodyReceipts (source named) (expressionSyntax (source named))
      sourceContext parameters result statements)
    (readFuel : Nat) :
    Nonempty (CallableIndexedOwnedPreparedNativeCompilerChildren.SiteShell
      (compilation := selected.compilation) expressionSyntax site) := by
  let code := site.code
  have unique := runtime.graph.nodeOccurrencesUnique
  have facts := CallableIndexedOwnedOrdinaryLambdaSourceFacts.of_typed
    (function := closure named parameters result statements sourceContext evidence [])
    unique code.sourceFound code.sourceForm typed coercions
  have frame := facts.frame runtime covers
  have kinds := CallableIndexedOwnedLocalIdentityFreshness.lowered_parameter_kinds
    (values := .initial compiled.compatible.checked) code ownership facts.contains facts.form
  have referenceIndex := CallableIndexedOwnedPreparedNativeSitePolicies.reference_index site
  cases finite with
  | @intro entryContext finalContext parameterTypes bodyFacts ready extended bodyTyped bodyReceipt annotation =>
    let entry : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code :=
      ⟨entryContext, parameterTypes, extended, kinds, referenceIndex⟩
    have fields := (CallableIndexedOwnedLiteralReturnLambdaStaticFacts.entry_runtime
      (values := .initial compiled.compatible.checked) entry frame).1
    have declarations := CallableIndexedOwnedLiteralReturnLambdaStaticFacts.entry_declarations
      (values := .initial compiled.compatible.checked) code entry facts parentDeclarations
    have syntaxTree := RecursiveNamedImperativeMatchSyntaxFactory.syntax_of_typed unique bodyReceipt annotation
    have projected := code.receipt.resultProjected
    rw (occs := .pos [1]) [samePolicy] at projected
    rw (occs := .pos [1]) [root.projectType] at projected
    have projection := CompatibleExpressionReads.projectType_of_accepted projected
    let issued := issued_at_site selected site
    have assignments : issued.assignments = selected.compilation.own.assignments := by
      dsimp only [issued, issued_at_site]
      exact selected.assignments
    have places : CallableIndexedOwnedLiteralPlaceDiagnosticShells.PlaceReasonsEq
        issued.diagnostics.program (lowered compiled selected.diagnostics) := by
      dsimp only [issued, issued_at_site]
      exact selected.places
    refine ⟨{
      issuedCompilation := ⟨selected.diagnostics, selected.found, by
        unfold lowered
        cases compiled.indexed.base.callableContext <;> exact ⟨rfl, rfl⟩⟩
      issued := issued
      diagnosticPolicy := .reachable
      entry := entry
      frame := frame
      readFuel := readFuel
      canonical := canonical
      unique := unique
      sameLedger := ?_
      syntaxTree := syntaxTree
      projection := projection
      residualMode := true
      static := {
        matchCompilation := CallableIndexedOwnedPreparedNativeSitePolicies.ambientMatch selected.compilation site
        matchPolicy := CallableIndexedOwnedPreparedNativeSitePolicies.match_policy selected.compilation site
        matchValues := CallableIndexedOwnedPreparedNativeSitePolicies.match_values selected.compilation site
        matchDefinitions := CallableIndexedOwnedPreparedNativeSitePolicies.match_definitions selected.compilation site
        matchAllocator := CallableIndexedOwnedPreparedNativeSitePolicies.match_allocator selected.compilation site root samePolicy
        hidden := ?_
        readPolicy := CallableIndexedOwnedPreparedNativeSitePolicies.read_policy selected.compilation site
        binderPolicy := ?_
        allocationPolicy := CallableIndexedOwnedPreparedNativeSitePolicies.allocation_policy selected.compilation site root samePolicy
        assignments := CallableIndexedOwnedPreparedNativeSitePolicies.assignment_policy selected.compilation site issued assignments places
        unaries := CallableIndexedOwnedPreparedNativeSitePolicies.unary_policy selected.compilation site issued assignments places
        closed := fields.typeVariables.trans frame.code.variables_closed
        residual := fields.residualTypeVariables.trans frame.code.residual_variables_open
        sourceSignatures := fields.signatures.trans (runtime.signatures.trans
          (CallableIndexedOwnedPublicSignatureCatalog.signatures compiled).symm)
        declarations := ?_
        ledger := ?_ } }⟩
    · rw [site.compilation]
      exact sameLedger
    · rw [canonical]
      exact CallableIndexedOwnedLocalIdentityFreshness.match_hidden_fresh ownership
    · intro childScope binder monomorphic
      exact CallableIndexedOwnedPreparedNativeSitePolicies.binder_policy selected.compilation site binder childScope monomorphic
    · change CompatibleExpressionReads.ScopeDeclarations code.view
        (code.receipt.loweredParameters.reverse.map (fun binding : TypedBinder × Ty => (binding.1.id, binding.2)) ++ scope)
        entry.context
      change CompatibleExpressionReads.ScopeDeclarations site.code.view _ _
      rw (occs := .pos [1]) [canonical]
      exact declarations
    · exact fields.solvedRequirements.trans sameLedger

end Selected
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeSiteShellReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedSelectedNativeFamilyQualification
/-! The final positive lambda qualification retains the actual selected
compiler issuance, the same selected shell issuer, and its literal receipt and occurrence factory. Ordinary
and method packets keep the same Site, body, dictionary and captured environment.
All adapters below are forward projections. A generic older compilation or
qualification supplies no selected issuer, receiving diagnostic identity, or
completed expression/body law. The finite occurrence and receiving factories
remain genuine static construction obligations. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedSelectedNativeFamilyQualification
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedContextualCompilerPolicyProfiles
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedContextualQualification (Facet)
open CallableIndexedOwnedPreparedNativeLambdaCompilerReceipts (Receipt)
open CallableIndexedOwnedSelectedDiagnosticIssuerReceipts (SelectedReceipt lowered)
open CallableIndexedOwnedPreparedNativeFamilyStaticQualification (OccurrenceFactory)
open CallableIndexedOwnedPreparedCanonicalCaptureReceipts («prefix»)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}

/-- The ordinary constructor keeps the literal selected second-pass slot.
Its receipt and occurrence factory have that same compiler root. -/
inductive Ordinary (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))) :
    {function : Dynamic.Closure} → {scope : SourceCoreLocalCell.Scope} → {administrative : Core.Context} →
    (code : Code compiled.indexed function scope administrative) →
    CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Support code → Prop where
  | actual {caller : Header compiled (Program.ofChecked compiled.sourceProgram)}
      (member : caller ∈ headers) {index : Nat}
      (selected : SelectedReceipt compiled caller.named index)
      {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
      {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
      (root : RootPolicyReceipt (compiled := compiled) caller.named (lowered compiled selected.diagnostics)
        selected.code selected.compilation rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
      (expressionSyntax : TypedSource → ExpressionId → Prop)
      {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
      {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
      {node : ExpressionNode} {parameters : List TypedBinder} {result : TypeSystem.Ty}
      {statements : List StatementId} {reported : Ty} {childFuel : Nat}
      (certificate : CallableIndexedLambdaCertificates.Certificate root.selected.policy root.selected.lowerBody childFuel
        (context compiled.indexed caller.named) (source caller.named) scope id node parameters result statements
        reported rootReasonAt lowered)
      (receipt : Receipt root expressionSyntax certificate (sourceContext := sourceContext) (evidence := evidence))
      (bodyReasons : CallableIndexedOwnedContextualLambdaProvenance.BodyReasons receipt.site.code caller.named)
      (declarations : CompatibleExpressionReads.ScopeDeclarations (source caller.named) scope sourceContext)
      (sameIssuer : receipt.shell.issued =
        CallableIndexedOwnedPreparedNativeSiteShellReceipts.issued_at_site selected receipt.site)
      (factory : OccurrenceFactory root expressionSyntax (some evidence) headers receipt.body.readFuel)
      (environment : Dynamic.Environment) :
      Ordinary headers
        (RecursiveNamedLambdaFormationHeads.recaptureCode
          (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) receipt.site.code environment)
        ((CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Support.of_site
          caller selected.compilation receipt.site expressionSyntax
          (CallableIndexedOwnedPreparedNativeCompilerChildren.certificates root expressionSyntax
            («prefix» (compiled := compiled) caller.named))
          receipt.shell.issued receipt.shell.diagnosticPolicy receipt.body).recapture environment)

/-- The method constructor retains the actual selector and selected receipt.
The support uses the positively reissued principal, with its full dictionary. -/
inductive Principal (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))) :
    {function : Dynamic.Closure} → {scope : SourceCoreLocalCell.Scope} → {administrative : Core.Context} →
    (code : Code compiled.indexed function scope administrative) →
    CallableIndexedOwnedPreparedPrincipalLambdaSupport.Support code → Prop where
  | actual {method : ExecutableImplMethods.CheckedMethod}
      (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
      (selected : SelectedReceipt compiled principal.named principal.cached.index)
      {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
      {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
      (root : RootPolicyReceipt (compiled := compiled) principal.named (lowered compiled selected.diagnostics)
        selected.code selected.compilation rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
      (expressionSyntax : TypedSource → ExpressionId → Prop)
      {sourceContext : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
      {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
      {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
      {reported : Ty} {childFuel : Nat}
      (certificate : CallableIndexedLambdaCertificates.Certificate root.selected.policy root.selected.lowerBody childFuel
        (context compiled.indexed principal.named) (source principal.named) scope id node parameters result statements
        reported rootReasonAt lowered)
      (receipt : Receipt root expressionSyntax certificate
        (sourceContext := sourceContext) (evidence := principal.dictionary))
      (sameIssuer : receipt.shell.issued =
        CallableIndexedOwnedPreparedNativeSiteShellReceipts.issued_at_site selected receipt.site)
      (factory : OccurrenceFactory root expressionSyntax (some principal.dictionary) headers receipt.body.readFuel)
      (environment : Dynamic.Environment) :
      Principal headers
        (RecursiveNamedLambdaFormationHeads.recaptureCode
          (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) receipt.site.code environment)
        ((CallableIndexedOwnedPreparedPrincipalLambdaSupport.Support.of_site
          (SelectedReceipt.principal principal selected) receipt.site expressionSyntax
          (CallableIndexedOwnedPreparedNativeCompilerChildren.certificates root expressionSyntax
            («prefix» (compiled := compiled) principal.named))
          receipt.shell.issued receipt.shell.diagnosticPolicy receipt.body).recapture environment)

def facet (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))) : Facet compiled where
  ordinary := Ordinary headers
  principal := Principal headers

theorem ordinary_family {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {code : Code compiled.indexed function scope administrative}
    {support : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Support code}
    (qualified : Ordinary headers code support) :
    CallableIndexedOwnedPreparedNativeFamilyStaticQualification.Ordinary headers code support := by
  cases qualified with
  | actual member selected root expressionSyntax certificate receipt bodyReasons declarations sameIssuer factory environment =>
      exact .actual member root expressionSyntax certificate receipt bodyReasons declarations factory environment

theorem principal_family {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {code : Code compiled.indexed function scope administrative}
    {support : CallableIndexedOwnedPreparedPrincipalLambdaSupport.Support code}
    (qualified : Principal headers code support) :
    CallableIndexedOwnedPreparedNativeFamilyStaticQualification.Principal headers code support := by
  cases qualified with
  | actual principal selected root expressionSyntax certificate receipt sameIssuer factory environment =>
      exact .actual (SelectedReceipt.principal principal selected) root expressionSyntax certificate receipt factory environment

theorem ordinary_prepared {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {code : Code compiled.indexed function scope administrative}
    {support : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Support code}
    (qualified : Ordinary headers code support) :
    CallableIndexedOwnedPreparedOrdinaryLambdaSupport.PreparedAt code support :=
  CallableIndexedOwnedPreparedNativeFamilyStaticQualification.ordinary_prepared (ordinary_family qualified)

theorem principal_prepared {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {code : Code compiled.indexed function scope administrative}
    {support : CallableIndexedOwnedPreparedPrincipalLambdaSupport.Support code}
    (qualified : Principal headers code support) :
    CallableIndexedOwnedPreparedPrincipalLambdaSupport.PreparedAt code support :=
  CallableIndexedOwnedPreparedNativeFamilyStaticQualification.principal_prepared (principal_family qualified)

theorem ordinary_native {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {code : Code compiled.indexed function scope administrative}
    {support : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Support code}
    (qualified : Ordinary headers code support) :
    CallableIndexedOwnedPreparedNativeCollectedQualification.Ordinary headers code support :=
  CallableIndexedOwnedPreparedNativeFamilyStaticQualification.ordinary_native (ordinary_family qualified)

theorem principal_native {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {code : Code compiled.indexed function scope administrative}
    {support : CallableIndexedOwnedPreparedPrincipalLambdaSupport.Support code}
    (qualified : Principal headers code support) :
    CallableIndexedOwnedPreparedNativeCollectedQualification.Principal code support :=
  CallableIndexedOwnedPreparedNativeFamilyStaticQualification.principal_native (principal_family qualified)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedSelectedNativeFamilyQualification
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeFamilyFlowStep
/-! The F step uses the literal retained AcceptedAt and one finite RuntimeTree
construction. Its E inputs are the mutually graded induction hypotheses at
that same Tree. The original JointBody prepared producer runs once per
direction. No static field stores an expression or body execution law.

This is the intermediate step of the mixed family. The final induction must
manufacture E call branches and the static Domain packets, and supply the
actual selected receiving diagnostic issuance. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeFamilyFlowStep
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedContextualCompilerPolicyProfiles
open CallableIndexedOwnedPreparedCanonicalCaptureReceipts («prefix»)
open CallableIndexedOwnedPreparedNativeFamilyStaticQualification (OccurrenceFactory)
open CallableIndexedOwnedPreparedCanonicalFlowBounds (Origin)
open CallableIndexedOwnedTypedLambdaBodyContinuations (Validity)
open CallableIndexedOwnedTypedLambdaProtocolContinuations (FlowPreserves FlowReflects)
open CallableIndexedOwnedContextualLambdaSourceDiagnostics
open CallableIndexedOwnedContextualLambdaJointStaticReceipts (JointBody trackedFactory)
open RecursiveNamedCatalogInvocationBounds (Below)

universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {named : Named}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  (namedCompilation : Compilation compiled.indexed named diagnostics namedCode)
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) named diagnostics namedCode namedCompilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  (expressionSyntax : TypedSource → ExpressionId → Prop)
  (callerEvidence : Option Dynamic.EvidenceEnvironment)
  {headers : RecursiveNamedCatalog.Inventory compiled.indexed.ancestry (.initial compiled.compatible.checked)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions (Program.ofChecked compiled.sourceProgram)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}

private abbrev Trees (readFuel : Nat) (currentContext : SourceSemantics.Context)
    (compilerScope : SourceCoreLocalCell.Scope) : GenericExpressionMeaning.Certificate :=
  CallableIndexedOwnedPreparedReachedNativeExpressionTreeBounds.RuntimeTree
    (sourceContext := currentContext) (compilerScope := compilerScope) (fuel := readFuel)
    (solved := (context compiled.indexed named).solvedRequirements)
    root expressionSyntax callerEvidence headers («prefix» (compiled := compiled) named)

section Select
variable {readFuel : Nat} {currentContext : SourceSemantics.Context}
  (factory : OccurrenceFactory root expressionSyntax callerEvidence headers readFuel)
  (unique : NodeOccurrencesUnique (source named))
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (CallableIndexedOwnedFunctionState.Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (evidence : Dynamic.EvidenceEnvironment)

/-- Pointwise selection consumes the retained action itself. The Tree is
manufactured internally; the E hypothesis is the same graded child family. -/
private theorem preserves_accepted
    (factory : OccurrenceFactory root expressionSyntax callerEvidence headers readFuel)
    (unique : NodeOccurrencesUnique (source named)) {sourceAt : TypedSource}
    (sameSource : sourceAt = source named) (size : Nat)
    (induction : ∀ compilerScope, CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      currentContext evidence (source named)
      (Trees (headers := headers) namedCompilation root expressionSyntax callerEvidence readFuel currentContext compilerScope) faults size) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      currentContext evidence sourceAt
      (CallableIndexedOwnedPreparedNativeCompilerChildren.certificates root expressionSyntax
        («prefix» (compiled := compiled) named) readFuel sourceAt currentContext) faults size := by
  cases sameSource
  intro scope id lowered accepted
  exact induction scope (OccurrenceFactory.runtime_tree root expressionSyntax callerEvidence headers readFuel factory unique accepted)

private theorem reflects_accepted
    (factory : OccurrenceFactory root expressionSyntax callerEvidence headers readFuel)
    (unique : NodeOccurrencesUnique (source named)) {sourceAt : TypedSource}
    (sameSource : sourceAt = source named) (size : Nat)
    (induction : ∀ compilerScope, CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      currentContext evidence (source named)
      (Trees (headers := headers) namedCompilation root expressionSyntax callerEvidence readFuel currentContext compilerScope) faults size) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      currentContext evidence sourceAt
      (CallableIndexedOwnedPreparedNativeCompilerChildren.certificates root expressionSyntax
        («prefix» (compiled := compiled) named) readFuel sourceAt currentContext) faults size := by
  cases sameSource
  intro scope id lowered accepted
  exact induction scope (OccurrenceFactory.runtime_tree root expressionSyntax callerEvidence headers readFuel factory unique accepted)
end Select

variable {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {capturedActual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured capturedActual)
  (code : Code compiled.indexed function scope captured.administrative)
  (sameSource : function.source = source named)
  (issued : IssuedSource compiled code.compilation.owner function.source)
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (body : JointBody namedCompilation code (Program.ofChecked compiled.sourceProgram) expressionSyntax
    (CallableIndexedOwnedPreparedNativeCompilerChildren.certificates root expressionSyntax
      («prefix» (compiled := compiled) named))
    diagnosticPolicy issued.invalidOperand issued.invalidUnary issued.invalidProjection issued.missingDefault)
  (factory : OccurrenceFactory root expressionSyntax callerEvidence headers body.readFuel)
  (origin : Origin compiled) (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  {table : SourceCoreFaultSites.Table}
  (rebuilt : issued.diagnostics.tableForRegistry registry extension = .ok table)
  (operandIncluded : ∀ reason token, GenericAssignmentDiagnostics.OperandRep issued.assignments reason token → faults reason token)
  (unaryIncluded : ∀ reason token, EmittedDiagnosticTokenPlan.UnaryRep issued.assignments reason token → faults reason token)
  (interprets : ∀ currentContext, Validity (program := Program.ofChecked compiled.sourceProgram) captured code currentContext →
    CallableIndexedOwnedContextualLambdaAssignmentReadiness.ReachedInterpretations
      (context := currentContext)
      (certificates := CallableIndexedOwnedPreparedNativeCompilerChildren.certificates root expressionSyntax
        («prefix» (compiled := compiled) named) body.readFuel function.source)
      (administrative := captured.administrative)
      (factory := trackedFactory diagnosticPolicy function.source issued.invalidOperand)
      (faults := faults) (registry := registry) issued
      (Origin.bridge (headers := headers) origin owner) functions table)

include sameSource factory extension faithful observations wellFormed rebuilt operandIncluded unaryIncluded interprets in
/-- E at sizes at most n constructs F at n using the same actual body recipe.
All E premises here are induction hypotheses; none is stored in qualification. -/
theorem preserves_flow (budget : Nat)
    (expressionIH : ∀ currentContext, Validity (program := Program.ofChecked compiled.sourceProgram) captured code currentContext →
      RecursiveNamedHeaderContracts.AtMost budget (fun size => ∀ compilerScope,
        CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
          (Origin.bridge (headers := headers) origin owner)
          (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
          currentContext function.evidence (source named)
          (Trees (headers := headers) namedCompilation root expressionSyntax callerEvidence body.readFuel currentContext compilerScope) faults size)) :
    RecursiveNamedHeaderContracts.AtMost budget
      (FlowPreserves captured code body.toBody functions (Origin.bridge (headers := headers) origin owner)
        (registry := registry) (faults := faults)) := by
  apply CallableIndexedOwnedPreparedCanonicalFlowBounds.preserves_flow namedCompilation captured code issued body origin owner
    functions extension faithful observations wellFormed rebuilt operandIncluded unaryIncluded interprets budget
  intro currentContext valid size within
  have unique : NodeOccurrencesUnique (source named) := by simpa only [sameSource] using body.unique
  exact @preserves_accepted (namedCompilation := namedCompilation) (root := root)
    (expressionSyntax := expressionSyntax) (callerEvidence := callerEvidence) (factory := factory) (unique := unique)
    (bridge := Origin.bridge (headers := headers) origin owner) (functions := functions)
    (evidence := function.evidence) (sourceAt := function.source) (sameSource := sameSource) (size := size) (induction := expressionIH currentContext valid size within)

include sameSource factory extension faithful observations wellFormed rebuilt operandIncluded unaryIncluded interprets in
/-- The native strict E family constructs F reflection with its independently
measured Source grade. The original prepared flow executes only once. -/
theorem reflects_flow (budget : Nat) (functionTypes : FunctionRuntimeViews functions)
    (expressionIH : ∀ currentContext, Validity (program := Program.ofChecked compiled.sourceProgram) captured code currentContext →
      Below budget (fun size => ∀ compilerScope,
        CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
          (Origin.bridge (headers := headers) origin owner)
          (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
          currentContext function.evidence (source named)
          (Trees (headers := headers) namedCompilation root expressionSyntax callerEvidence body.readFuel currentContext compilerScope) faults size)) :
    Below budget
      (FlowReflects captured code body.toBody functions (Origin.bridge (headers := headers) origin owner)
        (registry := registry) (faults := faults)) := by
  apply CallableIndexedOwnedPreparedCanonicalFlowBounds.reflects_flow namedCompilation captured code issued body origin owner
    functions extension faithful observations wellFormed rebuilt operandIncluded unaryIncluded interprets budget functionTypes
  intro currentContext valid size within
  have unique : NodeOccurrencesUnique (source named) := by simpa only [sameSource] using body.unique
  exact @reflects_accepted (namedCompilation := namedCompilation) (root := root)
    (expressionSyntax := expressionSyntax) (callerEvidence := callerEvidence) (factory := factory) (unique := unique)
    (bridge := Origin.bridge (headers := headers) origin owner) (functions := functions)
    (evidence := function.evidence) (sourceAt := function.source) (sameSource := sameSource) (size := size) (induction := expressionIH currentContext valid size within)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeFamilyFlowStep
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeTaggedSiteShellReceipts
/-! The selected shell retains its exact diagnostic issuer. All shell fields
are built by the original literal construction at the same Site. This adds the
constructive issuer identity; it does not recover it from an arbitrary shell
or from equality of owning compilations. No runtime or body law is supplied. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeTaggedSiteShellReceipts
open Core Frontend SourceInference
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration CallableIndexedLambdaValues
open CallableIndexedOwnedContextualCompilerPolicyProfiles
open CallableIndexedOwnedContextualLambdaJointStaticReceipts
open CallableIndexedOwnedContextualLambdaSourceDiagnostics
open CallableIndexedOwnedSelectedDiagnosticIssuerReceipts
open RecursiveNamedStatementSyntaxFacts

open CallableIndexedOwnedPreparedNativeSiteShellReceipts (FiniteBodyReceipts issued_at_site)

section Selected
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {named : Named} {index : Nat}
  (selected : SelectedReceipt compiled named index)
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) named (lowered compiled selected.diagnostics)
    selected.code selected.compilation rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  (expressionSyntax : TypedSource → ExpressionId → Prop)
  {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
  {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (site : Site compiled.indexed named parameters result statements sourceContext evidence [] scope administrative)

/-- Every shell field is derived at the literal Site and selected compilation.
An ordinary Header or selected Principal may supply this same genuine Named;
no ordinary Header is manufactured for a method. -/
theorem of_selected_with_issuer
    (samePolicy : site.code.policy = root.selected.policy)
    (canonical : site.code.view = source named)
    (typed : ExpressionHasType (source named) sourceContext site.code.id site.code.sourceNode.type)
    (coercions : site.code.sourceNode.coercions = [])
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
      sourceContext (source named))
    (covers : evidence.Covers sourceContext)
    (ownership : LocalIdentityOwnership (source named))
    (parentDeclarations : CompatibleExpressionReads.ScopeDeclarations (source named) scope sourceContext)
    (sameLedger : sourceContext.solvedRequirements = (context compiled.indexed named).solvedRequirements)
    (finite : FiniteBodyReceipts (source named) (expressionSyntax (source named))
      sourceContext parameters result statements)
    (readFuel : Nat) :
    ∃ shell : CallableIndexedOwnedPreparedNativeCompilerChildren.SiteShell
        (compilation := selected.compilation) expressionSyntax site,
      shell.issued = issued_at_site selected site := by
  let code := site.code
  have unique := runtime.graph.nodeOccurrencesUnique
  have facts := CallableIndexedOwnedOrdinaryLambdaSourceFacts.of_typed
    (function := closure named parameters result statements sourceContext evidence [])
    unique code.sourceFound code.sourceForm typed coercions
  have frame := facts.frame runtime covers
  have kinds := CallableIndexedOwnedLocalIdentityFreshness.lowered_parameter_kinds
    (values := .initial compiled.compatible.checked) code ownership facts.contains facts.form
  have referenceIndex := CallableIndexedOwnedPreparedNativeSitePolicies.reference_index site
  cases finite with
  | @intro entryContext finalContext parameterTypes bodyFacts ready extended bodyTyped bodyReceipt annotation =>
    let entry : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code :=
      ⟨entryContext, parameterTypes, extended, kinds, referenceIndex⟩
    have fields := (CallableIndexedOwnedLiteralReturnLambdaStaticFacts.entry_runtime
      (values := .initial compiled.compatible.checked) entry frame).1
    have declarations := CallableIndexedOwnedLiteralReturnLambdaStaticFacts.entry_declarations
      (values := .initial compiled.compatible.checked) code entry facts parentDeclarations
    have syntaxTree := RecursiveNamedImperativeMatchSyntaxFactory.syntax_of_typed unique bodyReceipt annotation
    have projected := code.receipt.resultProjected
    rw (occs := .pos [1]) [samePolicy] at projected
    rw (occs := .pos [1]) [root.projectType] at projected
    have projection := CompatibleExpressionReads.projectType_of_accepted projected
    let issued := issued_at_site selected site
    have assignments : issued.assignments = selected.compilation.own.assignments := by
      dsimp only [issued, issued_at_site]
      exact selected.assignments
    have places : CallableIndexedOwnedLiteralPlaceDiagnosticShells.PlaceReasonsEq
        issued.diagnostics.program (lowered compiled selected.diagnostics) := by
      dsimp only [issued, issued_at_site]
      exact selected.places
    refine ⟨{
      issuedCompilation := ⟨selected.diagnostics, selected.found, by
        unfold lowered
        cases compiled.indexed.base.callableContext <;> exact ⟨rfl, rfl⟩⟩
      issued := issued
      diagnosticPolicy := .reachable
      entry := entry
      frame := frame
      readFuel := readFuel
      canonical := canonical
      unique := unique
      sameLedger := ?_
      syntaxTree := syntaxTree
      projection := projection
      residualMode := true
      static := {
        matchCompilation := CallableIndexedOwnedPreparedNativeSitePolicies.ambientMatch selected.compilation site
        matchPolicy := CallableIndexedOwnedPreparedNativeSitePolicies.match_policy selected.compilation site
        matchValues := CallableIndexedOwnedPreparedNativeSitePolicies.match_values selected.compilation site
        matchDefinitions := CallableIndexedOwnedPreparedNativeSitePolicies.match_definitions selected.compilation site
        matchAllocator := CallableIndexedOwnedPreparedNativeSitePolicies.match_allocator selected.compilation site root samePolicy
        hidden := ?_
        readPolicy := CallableIndexedOwnedPreparedNativeSitePolicies.read_policy selected.compilation site
        binderPolicy := ?_
        allocationPolicy := CallableIndexedOwnedPreparedNativeSitePolicies.allocation_policy selected.compilation site root samePolicy
        assignments := CallableIndexedOwnedPreparedNativeSitePolicies.assignment_policy selected.compilation site issued assignments places
        unaries := CallableIndexedOwnedPreparedNativeSitePolicies.unary_policy selected.compilation site issued assignments places
        closed := fields.typeVariables.trans frame.code.variables_closed
        residual := fields.residualTypeVariables.trans frame.code.residual_variables_open
        sourceSignatures := fields.signatures.trans (runtime.signatures.trans
          (CallableIndexedOwnedPublicSignatureCatalog.signatures compiled).symm)
        declarations := ?_
        ledger := ?_ } }, rfl⟩
    · rw [site.compilation]
      exact sameLedger
    · rw [canonical]
      exact CallableIndexedOwnedLocalIdentityFreshness.match_hidden_fresh ownership
    · intro childScope binder monomorphic
      exact CallableIndexedOwnedPreparedNativeSitePolicies.binder_policy selected.compilation site binder childScope monomorphic
    · change CompatibleExpressionReads.ScopeDeclarations code.view
        (code.receipt.loweredParameters.reverse.map (fun binding : TypedBinder × Ty => (binding.1.id, binding.2)) ++ scope)
        entry.context
      change CompatibleExpressionReads.ScopeDeclarations site.code.view _ _
      rw (occs := .pos [1]) [canonical]
      exact declarations
    · exact fields.solvedRequirements.trans sameLedger

end Selected
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeTaggedSiteShellReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeTaggedLambdaCompilerReceipts
/-! A pointwise property of the actual static shell is retained in the native
compiler receipt. The original Site producer and JointBody factory each run
once. The property is carried unchanged and is not used to derive native body
typing or execution. The concrete consumer records the selected issuer. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeTaggedLambdaCompilerReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration CallableIndexedLambdaValues
open CallableIndexedOwnedContextualCompilerPolicyProfiles
open CallableIndexedOwnedContextualLambdaJointStaticReceipts
open CallableIndexedOwnedPreparedNativeCompilerChildren
open CallableIndexedOwnedPreparedCanonicalCaptureReceipts («prefix»)

open CallableIndexedOwnedPreparedNativeLambdaCompilerReceipts (Receipt)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {named : Named}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : Compilation compiled.indexed named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) named diagnostics namedCode compilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  (expressionSyntax : TypedSource → ExpressionId → Prop)
  {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  {node : ExpressionNode} {parameters : List TypedBinder} {result : TypeSystem.Ty}
  {statements : List StatementId} {reported : Ty} {childFuel : Nat}
  (certificate : CallableIndexedLambdaCertificates.Certificate root.selected.policy root.selected.lowerBody childFuel
    (context compiled.indexed named) (source named) scope id node parameters result statements reported rootReasonAt lowered)


variable (Tag : ∀ site : Site compiled.indexed named parameters result statements
    sourceContext evidence [] scope («prefix» (compiled := compiled) named),
  SiteShell (compilation := compilation) expressionSyntax site → Prop)

/-- The same occurrence builds its literal prefix Site and native JointBody.
The shell callback supplies only actual Source/issuance/policy metadata for the
Site just generated. It cannot supply body typing or any execution theorem. -/
theorem of_certificate_with_shell_property
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) sourceContext (source named))
    (covers : evidence.Covers sourceContext)
    (found : (source named).lookupExpression? id = some node)
    (form : node.form = .lambda parameters result statements)
    (sourceTyped : ExpressionHasType (source named) sourceContext id node.type)
    (coercions : node.coercions = [])
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody (childFuel + 1)
      (context compiled.indexed named) (source named) scope id rootReasonAt = .ok lowered)
    {nativeType : Ty}
    (raw : HasType (SourceCoreLocalCell.coreContext scope ++ «prefix» (compiled := compiled) named)
      lowered.expression nativeType compiled.indexed.layouts.definitions)
    (shells : ∀ site : Site compiled.indexed named parameters result statements sourceContext evidence []
        scope («prefix» (compiled := compiled) named),
      site.code.id = id → site.code.lowered = lowered → site.code.policy = root.selected.policy →
      site.code.lowerBody = root.selected.lowerBody → site.code.fuel = childFuel →
      site.code.view = source named → site.code.reasonAt = rootReasonAt →
      Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram)
        (closure named parameters result statements sourceContext evidence []) →
      ∃ shell : SiteShell (compilation := compilation) expressionSyntax site,
        Tag site shell) :
    ∃ receipt : Receipt root expressionSyntax certificate
        (sourceContext := sourceContext) (evidence := evidence),
      Tag receipt.site receipt.shell := by
  have native := CallableIndexedOwnedPreparedLambdaOccurrenceNativeTyping.certificate_native
    compiled.indexed certificate found root.rawLambdaExpression root.callables raw
  obtain ⟨site, identifier, emitted, policy, lowerBody, fuel, view, reason,
      sourceNode, actualNode, sameCertificate⟩ :=
    CallableIndexedLambdaGeneration.of_certificate compiled.indexed sourceContext evidence [] certificate accepted
      profile (LambdaMetadataViews.MetadataView.refl _) found form found rfl
      root.sourceCells root.rawLambdaBody root.rawLambdaExpression root.callables root.projectType
      (by rw [root.compilerPolicy.snapshotLambda]) native
  have facts := CallableIndexedOwnedOrdinaryLambdaSourceFacts.of_typed
    (function := closure named parameters result statements sourceContext evidence [])
    runtime.graph.nodeOccurrencesUnique found form sourceTyped coercions
  obtain ⟨shell, tagged⟩ := shells site identifier emitted policy lowerBody fuel view reason (facts.frame runtime covers)
  obtain ⟨body, entry, readFuel⟩ :=
    SiteShell.joint root expressionSyntax site shell policy lowerBody reason
  have binderPolicy : CallableIndexedOwnedContextualLambdaProvenance.BinderPolicy named site.code :=
    (congrArg SourceCoreFunctions.Policy.lowerBinder policy).trans root.selected.binder
  exact ⟨⟨site, identifier, emitted, policy, lowerBody, fuel, view, reason,
    sourceNode, actualNode, sameCertificate, binderPolicy, shell, body, entry, readFuel, facts⟩, tagged⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeTaggedLambdaCompilerReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedSelectedPositiveOrdinaryLambdaHeads
/-! One literal raw compiler lambda retains its actual compiler Receipt and
OccurrenceFactory at that same receipt's body read fuel. The static receipt is
manufactured by the selected issuer and same-Site shell producer below; the
finite occurrence factory remains an authentic static construction obligation.

The semantic leaf consumes that retained packet, captures from the original
caller pool and forms one positive closure under the selected family facet. The constructor
retains the exact selected issuer and bootstrap owner at the same pool.
No field contains a completed Tree, execution or body law. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedSelectedPositiveOrdinaryLambdaHeads
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedContextualCompilerPolicyProfiles
open CallableIndexedOwnedPreparedNativeSiteShellReceipts (FiniteBodyReceipts)
open CallableIndexedOwnedSelectedDiagnosticIssuerReceipts (SelectedReceipt lowered)
open CallableIndexedOwnedPreparedNativeLambdaCompilerReceipts (Receipt)
open CallableIndexedOwnedSourceAdmission

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {caller : Header compiled (Program.ofChecked compiled.sourceProgram)} {index : Nat}
  (selected : SelectedReceipt compiled caller.named index)
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) caller.named (lowered compiled selected.diagnostics)
    selected.code selected.compilation rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  (expressionSyntax : TypedSource → ExpressionId → Prop)
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {scope : SourceCoreLocalCell.Scope}
  (headers : RecursiveNamedCatalog.Inventory compiled.indexed.ancestry (.initial compiled.compatible.checked)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions (Program.ofChecked compiled.sourceProgram))

/-- This positive constructor preserves exactly the raw compiler lambda
branch and its own native witness. Finite body receipts are Source authority,
not a result of native typing. The exact constructed Receipt and its static
occurrence factory are retained together before runtime formation. -/
inductive Lambdas (children : GenericExpressionMeaning.Certificate) : GenericExpressionMeaning.Certificate where
  | actual {childFuel id lowered node parameters result statements reported nativeType}
      (allowed : expressionSyntax (source caller.named) id)
      (found : (source caller.named).lookupExpression? id = some node)
      (form : node.form = .lambda parameters result statements)
      (certificate : CallableIndexedLambdaCertificates.Certificate root.selected.policy root.selected.lowerBody childFuel
        (CallableIndexedNamedGeneration.context compiled.indexed caller.named) (source caller.named) scope
        id node parameters result statements reported rootReasonAt lowered)
      (accepted : SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody (childFuel + 1)
        (CallableIndexedNamedGeneration.context compiled.indexed caller.named) (source caller.named) scope id rootReasonAt = .ok lowered)
      (sourceTyped : ExpressionHasType (source caller.named) context id node.type)
      (metadata : CompatibleExpressionReads.Metadata compiled.compatible.checked (source caller.named) id node lowered.type)
      (raw : HasType (SourceCoreLocalCell.coreContext scope ++ CallableIndexedOwnedPreparedCanonicalCaptureReceipts.«prefix»
          (compiled := compiled) caller.named) lowered.expression nativeType compiled.indexed.layouts.definitions)
      (finite : FiniteBodyReceipts (source caller.named) (expressionSyntax (source caller.named))
        context parameters result statements)
      (receipt : Receipt root expressionSyntax certificate (sourceContext := context) (evidence := evidence))
      (bodyReasons : CallableIndexedOwnedContextualLambdaProvenance.BodyReasons receipt.site.code caller.named)
      (declarations : CompatibleExpressionReads.ScopeDeclarations (source caller.named) scope context)
      (sameIssuer : receipt.shell.issued =
        CallableIndexedOwnedPreparedNativeSiteShellReceipts.issued_at_site selected receipt.site)
      (factory : CallableIndexedOwnedPreparedNativeFamilyStaticQualification.OccurrenceFactory
        root expressionSyntax (some evidence) headers receipt.body.readFuel) :
      Lambdas children scope id lowered

/-- The same positive compiler lambda is included into the original raw
head. Only its own native witness is retained, with no used child slots. -/
theorem Lambdas.to_native_heads
    (callerEvidence : Option Dynamic.EvidenceEnvironment)
    {children : GenericExpressionMeaning.Certificate} {childScope id lowered}
    (head : Lambdas selected root expressionSyntax headers (context := context) (evidence := evidence) (scope := scope) children childScope id lowered) :
    CallableIndexedOwnedPreparedRawCompilerHeads.Head root expressionSyntax callerEvidence headers
      (sourceContext := context) (scope := scope) children childScope id lowered ∧
      CallableIndexedOwnedPreparedNativeAssignmentChildren.RawTyped
        (SourceCoreLocalCell.coreContext childScope ++ CallableIndexedOwnedPreparedCanonicalCaptureReceipts.«prefix»
          (compiled := compiled) caller.named) lowered.expression compiled.indexed.layouts.definitions := by
  cases head with
  | actual allowed found form certificate accepted typed metadata raw finite receipt bodyReasons sourceDeclarations sameIssuer factory =>
      exact ⟨.lambda allowed found form certificate accepted typed metadata, ⟨_, raw⟩⟩

variable
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context (source caller.named))
  (covers : evidence.Covers context)
  (ownership : LocalIdentityOwnership (source caller.named))
  (declarations : CompatibleExpressionReads.ScopeDeclarations (source caller.named) scope context)
  (sameLedger : context.solvedRequirements = (CallableIndexedNamedGeneration.context compiled.indexed caller.named).solvedRequirements)

include profile runtime covers ownership declarations sameLedger in
/-- The only shell callback is manufactured by the actual selected static
producer. It preserves the Site generated once by the original compiler. -/
theorem compiler_receipt
    {childFuel id lowered node parameters result statements reported nativeType}
    (certificate : CallableIndexedLambdaCertificates.Certificate root.selected.policy root.selected.lowerBody childFuel
      (CallableIndexedNamedGeneration.context compiled.indexed caller.named) (source caller.named) scope
      id node parameters result statements reported rootReasonAt lowered)
    (found : (source caller.named).lookupExpression? id = some node)
    (form : node.form = .lambda parameters result statements)
    (sourceTyped : ExpressionHasType (source caller.named) context id node.type)
    (coercions : node.coercions = [])
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody (childFuel + 1)
      (CallableIndexedNamedGeneration.context compiled.indexed caller.named) (source caller.named) scope id rootReasonAt = .ok lowered)
    (raw : HasType (SourceCoreLocalCell.coreContext scope ++ CallableIndexedOwnedPreparedCanonicalCaptureReceipts.«prefix»
      (compiled := compiled) caller.named) lowered.expression nativeType compiled.indexed.layouts.definitions)
    (finite : FiniteBodyReceipts (source caller.named) (expressionSyntax (source caller.named))
      context parameters result statements) :
    ∃ receipt : Receipt root expressionSyntax certificate (sourceContext := context) (evidence := evidence),
      receipt.shell.issued = CallableIndexedOwnedPreparedNativeSiteShellReceipts.issued_at_site selected receipt.site := by
  apply CallableIndexedOwnedPreparedNativeTaggedLambdaCompilerReceipts.of_certificate_with_shell_property
    root expressionSyntax certificate
    (fun site shell => shell.issued = CallableIndexedOwnedPreparedNativeSiteShellReceipts.issued_at_site selected site)
    profile runtime covers found form sourceTyped coercions accepted raw
  intro site identifier emitted policy body fuel view reason frame
  have sourceFound : (source caller.named).lookupExpression? id = some site.code.sourceNode := by
    simpa only [CallableIndexedLambdaGeneration.closure, identifier] using site.code.sourceFound
  have sameNode := Option.some.inj (sourceFound.symm.trans found)
  have typedAt : ExpressionHasType (source caller.named) context site.code.id site.code.sourceNode.type := by
    rw [identifier, sameNode]
    exact sourceTyped
  have coercionsAt : site.code.sourceNode.coercions = [] := by
    rw [sameNode]
    exact coercions
  exact CallableIndexedOwnedPreparedNativeTaggedSiteShellReceipts.of_selected_with_issuer selected root expressionSyntax site
    policy view typedAt coercionsAt runtime covers ownership declarations sameLedger finite 0

section Semantics
variable
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (owner : OwnedKey keys)
  (member : caller ∈ headers)
  (complete : RecursiveNamedCatalogNativeContexts.Complete
    (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (program := Program.ofChecked compiled.sourceProgram)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  {children : GenericExpressionMeaning.Certificate}

variable (owners : CallableIndexedOwnedPreparedPositiveFunctionOrigins.OwnerCover headers keys bodyRegistry profile)

local notation "nativeFacet" => CallableIndexedOwnedPreparedSelectedNativeFamilyQualification.facet (compiled := compiled) headers
local notation "bridge" => CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
  (CallableIndexedOwnedPreparedPositiveFunctionOrigins.functions nativeFacet headers keys bodyRegistry faults profile)

include profile owners member complete wellFormed runtime covers in
/-- Actual admitted caller capture and one original formation prove the
ordinary native-qualified lambda leaf at its canonical packet, transported to
the formed state that holds the copies of the captured cells. -/
theorem preserves_at (size : Nat) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge model context evidence (source caller.named)
      (Lambdas selected root expressionSyntax headers (context := context) (evidence := evidence) (scope := scope) children) faults size := by
  intro childScope id lowered certified node found sourceTyped mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees typed initial admitted trace
  cases certified with
  | @actual childFuel id lowered actualNode parameters sourceResult statements reported nativeType allowed actualFound form certificate accepted parentTyped metadata raw finite receipt bodyReasons sourceDeclarations sameIssuer factory =>
    let captured := CallableIndexedOwnedPreparedCanonicalCaptureReceipts.Ordinary.captured
      owner complete environments agrees typed caller initial.1 initial.2
    have sameEmbedding : captured.embedding = ξ := rfl
    let code := RecursiveNamedLambdaFormationHeads.recaptureCode
      (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) receipt.site.code environment
    let support := (CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Support.of_site caller selected.compilation receipt.site
      expressionSyntax (CallableIndexedOwnedPreparedNativeCompilerChildren.certificates root expressionSyntax
        (CallableIndexedOwnedPreparedCanonicalCaptureReceipts.«prefix» (compiled := compiled) caller.named))
      receipt.shell.issued receipt.shell.diagnosticPolicy receipt.body).recapture environment
    have qualified : ∀ copies, (nativeFacet).ordinary (code.recapture copies) (support.recapture copies) :=
      fun copies => CallableIndexedOwnedPreparedSelectedNativeFamilyQualification.Ordinary.actual (compiled := compiled)
        member selected root expressionSyntax certificate receipt bodyReasons sourceDeclarations sameIssuer factory copies
    have identifier : code.id = id := receipt.identifier
    have emitted : code.lowered = lowered := receipt.emitted
    have sameNode : code.sourceNode = node :=
      receipt.sourceNodeEq.trans (Option.some.inj (actualFound.symm.trans found))
    have codeTyped : ExpressionHasType (source caller.named) context code.id code.sourceNode.type := by
      rw [identifier, sameNode]
      exact sourceTyped
    have sourceType := receipt.sourceFacts.sourceType
    rw [← receipt.sourceNodeEq] at sourceType
    have ordinary := receipt.sourceFacts.ordinary
    rw [← receipt.sourceNodeEq] at ordinary
    have coercions := receipt.sourceFacts.coercions
    rw [← receipt.sourceNodeEq] at coercions
    have codeTrace : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) size
        context evidence (source caller.named) environment before code.id outcome after := by
      rw [identifier]
      exact trace
    obtain ⟨result, finalStore, evaluated, finalMap, finalWorld, represented, finalHeaps, maps, worlds, frame, metadata,
        reached, related, post, _member⟩ :=
      CallableIndexedOwnedPreparedFunctionModelFormationBounds.Ordinary.preserves_at
        (compiled := compiled) (headers := headers) (keys := keys)
        (function := closure caller.named parameters sourceResult statements context evidence environment)
        (scope := scope) (actual := actual) (mapping := mapping) (world := world) (heap := before) (store := store)
        (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
        (captured := captured) (code := code) (owner := owner)
        (qualification := nativeFacet) (profile := profile)
        (models := CallableIndexedOwnedPreparedPositiveFunctionOrigins.functions
          (compiled := compiled) nativeFacet headers keys bodyRegistry faults profile)
        (lift := fun member => .closure
          (CallableIndexedOwnedPreparedPositiveFunctionOrigins.closure_of_direct owners member))
        (support := support) (qualified := qualified)
        (prepared := CallableIndexedOwnedPreparedSelectedNativeFamilyQualification.ordinary_prepared (compiled := compiled) (headers := headers) (code := code) (support := support) (qualified environment))
        (initial := initial.1) (packet := initial.2)
        (prefixContext := CallableIndexedOwnedPreparedCanonicalCaptureReceipts.Ordinary.captured_prefix
          owner complete environments agrees typed caller initial.1 initial.2)
        (observed := CallableIndexedOwnedPreparedCanonicalCaptureReceipts.capture_globals caller.named owner complete
          initial.2.observed initial.2.bundle environments agrees typed)
        (cells := heaps) (wellFormed := wellFormed) (runtime := runtime) (covers := covers) (locals := locals)
        (typed := codeTyped) (sourceType := sourceType) (ordinary := ordinary) (coercions := coercions)
        (admitted := admitted) codeTrace
    refine ⟨result, finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps, maps, worlds, frame, metadata,
      reached, related, ?_⟩
    · simpa only [emitted, sameEmbedding] using evaluated
    · simpa only [sameNode, emitted] using represented
    · refine ⟨post.admission.rows, ?_⟩
      intro value same
      simpa only [sameNode, closure] using post.admission.successful value same

include profile owners member complete wellFormed runtime covers in
/-- Independent native completion uses one actual formation and its own
Source grade. The same qualified post stays in the caller's reached packet. -/
theorem reflects_at (size : Nat) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge model context evidence (source caller.named)
      (Lambdas selected root expressionSyntax headers (context := context) (evidence := evidence) (scope := scope) children) faults size := by
  intro childScope id lowered certified node found sourceTyped mapping world administrative environment canonical actual actualContext
    before store ξ result finalStore environments heaps locals agrees typed initial admitted completed
  cases certified with
  | @actual childFuel id lowered actualNode parameters sourceResult statements reported nativeType allowed actualFound form certificate accepted parentTyped metadata raw finite receipt bodyReasons sourceDeclarations sameIssuer factory =>
    let captured := CallableIndexedOwnedPreparedCanonicalCaptureReceipts.Ordinary.captured
      owner complete environments agrees typed caller initial.1 initial.2
    have sameEmbedding : captured.embedding = ξ := rfl
    let code := RecursiveNamedLambdaFormationHeads.recaptureCode
      (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) receipt.site.code environment
    let support := (CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Support.of_site caller selected.compilation receipt.site
      expressionSyntax (CallableIndexedOwnedPreparedNativeCompilerChildren.certificates root expressionSyntax
        (CallableIndexedOwnedPreparedCanonicalCaptureReceipts.«prefix» (compiled := compiled) caller.named))
      receipt.shell.issued receipt.shell.diagnosticPolicy receipt.body).recapture environment
    have qualified : ∀ copies, (nativeFacet).ordinary (code.recapture copies) (support.recapture copies) :=
      fun copies => CallableIndexedOwnedPreparedSelectedNativeFamilyQualification.Ordinary.actual (compiled := compiled)
        member selected root expressionSyntax certificate receipt bodyReasons sourceDeclarations sameIssuer factory copies
    have identifier : code.id = id := receipt.identifier
    have emitted : code.lowered = lowered := receipt.emitted
    have sameNode : code.sourceNode = node :=
      receipt.sourceNodeEq.trans (Option.some.inj (actualFound.symm.trans found))
    have codeTyped : ExpressionHasType (source caller.named) context code.id code.sourceNode.type := by
      rw [identifier, sameNode]
      exact sourceTyped
    have sourceType := receipt.sourceFacts.sourceType
    rw [← receipt.sourceNodeEq] at sourceType
    have ordinary := receipt.sourceFacts.ordinary
    rw [← receipt.sourceNodeEq] at ordinary
    have coercions := receipt.sourceFacts.coercions
    rw [← receipt.sourceNodeEq] at coercions
    have codeCompleted : EvaluationSize size actual store (code.lowered.expression.rename captured.embedding) result finalStore := by
      simpa only [emitted, sameEmbedding] using completed
    obtain ⟨sourceSize, outcome, after, sourceTrace, evaluated, finalMap, finalWorld, represented, finalHeaps, maps,
        worlds, frame, metadata, reached, related, post, _member⟩ :=
      CallableIndexedOwnedPreparedFunctionModelFormationBounds.Ordinary.reflects_at
        (compiled := compiled) (headers := headers) (keys := keys)
        (function := closure caller.named parameters sourceResult statements context evidence environment)
        (scope := scope) (actual := actual) (mapping := mapping) (world := world) (heap := before) (store := store)
        (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
        (captured := captured) (code := code) (owner := owner)
        (qualification := nativeFacet) (profile := profile)
        (models := CallableIndexedOwnedPreparedPositiveFunctionOrigins.functions
          (compiled := compiled) nativeFacet headers keys bodyRegistry faults profile)
        (lift := fun member => .closure
          (CallableIndexedOwnedPreparedPositiveFunctionOrigins.closure_of_direct owners member))
        (support := support) (qualified := qualified)
        (prepared := CallableIndexedOwnedPreparedSelectedNativeFamilyQualification.ordinary_prepared (compiled := compiled) (headers := headers) (code := code) (support := support) (qualified environment))
        (initial := initial.1) (packet := initial.2)
        (prefixContext := CallableIndexedOwnedPreparedCanonicalCaptureReceipts.Ordinary.captured_prefix
          owner complete environments agrees typed caller initial.1 initial.2)
        (observed := CallableIndexedOwnedPreparedCanonicalCaptureReceipts.capture_globals caller.named owner complete
          initial.2.observed initial.2.bundle environments agrees typed)
        (cells := heaps) (wellFormed := wellFormed) (runtime := runtime) (covers := covers) (locals := locals)
        (typed := codeTyped) (sourceType := sourceType) (ordinary := ordinary) (coercions := coercions)
        (admitted := admitted) codeCompleted
    refine ⟨sourceSize, outcome, after, finalMap, finalWorld, ?_, ?_, finalHeaps, maps, worlds, frame, metadata,
      reached, related, ?_⟩
    · simpa only [identifier, closure] using sourceTrace
    · simpa only [sameNode, emitted] using represented
    · refine ⟨post.admission.rows, ?_⟩
      intro value same
      simpa only [sameNode, closure] using post.admission.successful value same

end Semantics
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedSelectedPositiveOrdinaryLambdaHeads
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedSelectedPositivePrincipalLambdaHeads
/-! One literal raw compiler lambda retains its actual compiler Receipt and
OccurrenceFactory at that same receipt's body read fuel. The static receipt is
manufactured by the selected issuer and same-Site shell producer below; the
finite occurrence factory remains an authentic static construction obligation.

The semantic leaf consumes that retained packet, captures from the original
caller pool and forms one positive closure under the selected family facet. The constructor
retains the exact selected issuer and bootstrap owner at the same pool.
No field contains a completed Tree, execution or body law. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedSelectedPositivePrincipalLambdaHeads
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedContextualCompilerPolicyProfiles
open CallableIndexedOwnedPreparedNativeSiteShellReceipts (FiniteBodyReceipts)
open CallableIndexedOwnedSelectedDiagnosticIssuerReceipts (SelectedReceipt lowered)
open CallableIndexedOwnedPreparedNativeLambdaCompilerReceipts (Receipt)
open CallableIndexedOwnedSourceAdmission

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {method : ExecutableImplMethods.CheckedMethod}
  (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
  (selected : SelectedReceipt compiled principal.named principal.cached.index)
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) principal.named (lowered compiled selected.diagnostics)
    selected.code selected.compilation rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  (expressionSyntax : TypedSource → ExpressionId → Prop)
  {context : SourceSemantics.Context}
  {scope : SourceCoreLocalCell.Scope}
  (headers : RecursiveNamedCatalog.Inventory compiled.indexed.ancestry (.initial compiled.compatible.checked)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions (Program.ofChecked compiled.sourceProgram))

/-- This positive constructor preserves exactly the raw compiler lambda
branch and its own native witness. Finite body receipts are Source authority,
not a result of native typing. The exact constructed Receipt and its static
occurrence factory are retained together before runtime formation. -/
inductive Lambdas (children : GenericExpressionMeaning.Certificate) : GenericExpressionMeaning.Certificate where
  | actual {childFuel id lowered node parameters result statements reported nativeType}
      (allowed : expressionSyntax (source principal.named) id)
      (found : (source principal.named).lookupExpression? id = some node)
      (form : node.form = .lambda parameters result statements)
      (certificate : CallableIndexedLambdaCertificates.Certificate root.selected.policy root.selected.lowerBody childFuel
        (CallableIndexedNamedGeneration.context compiled.indexed principal.named) (source principal.named) scope
        id node parameters result statements reported rootReasonAt lowered)
      (accepted : SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody (childFuel + 1)
        (CallableIndexedNamedGeneration.context compiled.indexed principal.named) (source principal.named) scope id rootReasonAt = .ok lowered)
      (sourceTyped : ExpressionHasType (source principal.named) context id node.type)
      (metadata : CompatibleExpressionReads.Metadata compiled.compatible.checked (source principal.named) id node lowered.type)
      (raw : HasType (SourceCoreLocalCell.coreContext scope ++ CallableIndexedOwnedPreparedCanonicalCaptureReceipts.«prefix»
          (compiled := compiled) principal.named) lowered.expression nativeType compiled.indexed.layouts.definitions)
      (finite : FiniteBodyReceipts (source principal.named) (expressionSyntax (source principal.named))
        context parameters result statements)
      (receipt : Receipt root expressionSyntax certificate (sourceContext := context) (evidence := principal.dictionary))
      (sameIssuer : receipt.shell.issued =
        CallableIndexedOwnedPreparedNativeSiteShellReceipts.issued_at_site selected receipt.site)
      (factory : CallableIndexedOwnedPreparedNativeFamilyStaticQualification.OccurrenceFactory
        root expressionSyntax (some principal.dictionary) headers receipt.body.readFuel) :
      Lambdas children scope id lowered

/-- The same positive compiler lambda is included into the original raw
head. Only its own native witness is retained, with no used child slots. -/
theorem Lambdas.to_native_heads
    (callerEvidence : Option Dynamic.EvidenceEnvironment)
    {children : GenericExpressionMeaning.Certificate} {childScope id lowered}
    (head : Lambdas principal selected root expressionSyntax headers (context := context) (scope := scope) children childScope id lowered) :
    CallableIndexedOwnedPreparedRawCompilerHeads.Head root expressionSyntax callerEvidence headers
      (sourceContext := context) (scope := scope) children childScope id lowered ∧
      CallableIndexedOwnedPreparedNativeAssignmentChildren.RawTyped
        (SourceCoreLocalCell.coreContext childScope ++ CallableIndexedOwnedPreparedCanonicalCaptureReceipts.«prefix»
          (compiled := compiled) principal.named) lowered.expression compiled.indexed.layouts.definitions := by
  cases head with
  | actual allowed found form certificate accepted typed metadata raw finite receipt sameIssuer factory =>
      exact ⟨.lambda allowed found form certificate accepted typed metadata, ⟨_, raw⟩⟩

variable
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context (source principal.named))
  (covers : principal.dictionary.Covers context)
  (ownership : LocalIdentityOwnership (source principal.named))
  (declarations : CompatibleExpressionReads.ScopeDeclarations (source principal.named) scope context)
  (sameLedger : context.solvedRequirements = (CallableIndexedNamedGeneration.context compiled.indexed principal.named).solvedRequirements)

include profile runtime covers ownership declarations sameLedger in
/-- The only shell callback is manufactured by the actual selected static
producer. It preserves the Site generated once by the original compiler. -/
theorem compiler_receipt
    {childFuel id lowered node parameters result statements reported nativeType}
    (certificate : CallableIndexedLambdaCertificates.Certificate root.selected.policy root.selected.lowerBody childFuel
      (CallableIndexedNamedGeneration.context compiled.indexed principal.named) (source principal.named) scope
      id node parameters result statements reported rootReasonAt lowered)
    (found : (source principal.named).lookupExpression? id = some node)
    (form : node.form = .lambda parameters result statements)
    (sourceTyped : ExpressionHasType (source principal.named) context id node.type)
    (coercions : node.coercions = [])
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody (childFuel + 1)
      (CallableIndexedNamedGeneration.context compiled.indexed principal.named) (source principal.named) scope id rootReasonAt = .ok lowered)
    (raw : HasType (SourceCoreLocalCell.coreContext scope ++ CallableIndexedOwnedPreparedCanonicalCaptureReceipts.«prefix»
      (compiled := compiled) principal.named) lowered.expression nativeType compiled.indexed.layouts.definitions)
    (finite : FiniteBodyReceipts (source principal.named) (expressionSyntax (source principal.named))
      context parameters result statements) :
    ∃ receipt : Receipt root expressionSyntax certificate (sourceContext := context) (evidence := principal.dictionary),
      receipt.shell.issued = CallableIndexedOwnedPreparedNativeSiteShellReceipts.issued_at_site selected receipt.site := by
  apply CallableIndexedOwnedPreparedNativeTaggedLambdaCompilerReceipts.of_certificate_with_shell_property
    root expressionSyntax certificate
    (fun site shell => shell.issued = CallableIndexedOwnedPreparedNativeSiteShellReceipts.issued_at_site selected site)
    profile runtime covers found form sourceTyped coercions accepted raw
  intro site identifier emitted policy body fuel view reason frame
  have sourceFound : (source principal.named).lookupExpression? id = some site.code.sourceNode := by
    simpa only [CallableIndexedLambdaGeneration.closure, identifier] using site.code.sourceFound
  have sameNode := Option.some.inj (sourceFound.symm.trans found)
  have typedAt : ExpressionHasType (source principal.named) context site.code.id site.code.sourceNode.type := by
    rw [identifier, sameNode]
    exact sourceTyped
  have coercionsAt : site.code.sourceNode.coercions = [] := by
    rw [sameNode]
    exact coercions
  exact CallableIndexedOwnedPreparedNativeTaggedSiteShellReceipts.of_selected_with_issuer selected root expressionSyntax site
    policy view typedAt coercionsAt runtime covers ownership declarations sameLedger finite 0

section Semantics
variable
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (owner : OwnedKey keys)
  (complete : RecursiveNamedCatalogNativeContexts.Complete
    (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (program := Program.ofChecked compiled.sourceProgram)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  {children : GenericExpressionMeaning.Certificate}

variable (owners : CallableIndexedOwnedPreparedPositiveFunctionOrigins.OwnerCover headers keys bodyRegistry profile)

local notation "nativeFacet" => CallableIndexedOwnedPreparedSelectedNativeFamilyQualification.facet (compiled := compiled) headers
local notation "bridge" => CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner principal.named
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
  (CallableIndexedOwnedPreparedPositiveFunctionOrigins.functions nativeFacet headers keys bodyRegistry faults profile)

include profile owners complete wellFormed runtime covers in
/-- Actual admitted caller capture and one original formation prove the
selected Principal lambda leaf at its canonical packet, transported to the
formed state that holds the copies of the captured cells. -/
theorem preserves_at (size : Nat) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge model context principal.dictionary (source principal.named)
      (Lambdas principal selected root expressionSyntax headers (context := context) (scope := scope) children) faults size := by
  intro childScope id lowered certified node found sourceTyped mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees typed initial admitted trace
  cases certified with
  | @actual childFuel id lowered actualNode parameters sourceResult statements reported nativeType allowed actualFound form certificate accepted parentTyped metadata raw finite receipt sameIssuer factory =>
    let captured := CallableIndexedOwnedPreparedCanonicalCaptureReceipts.Principal.captured
      principal.named owner complete environments agrees typed initial.1 initial.2
    have sameEmbedding : captured.embedding = ξ := rfl
    let code := RecursiveNamedLambdaFormationHeads.recaptureCode
      (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) receipt.site.code environment
    let support := (CallableIndexedOwnedPreparedPrincipalLambdaSupport.Support.of_site
      (SelectedReceipt.principal principal selected) receipt.site
      expressionSyntax (CallableIndexedOwnedPreparedNativeCompilerChildren.certificates root expressionSyntax
        (CallableIndexedOwnedPreparedCanonicalCaptureReceipts.«prefix» (compiled := compiled) principal.named))
      receipt.shell.issued receipt.shell.diagnosticPolicy receipt.body).recapture environment
    have qualified : ∀ copies, (nativeFacet).principal (code.recapture copies) (support.recapture copies) :=
      fun copies => CallableIndexedOwnedPreparedSelectedNativeFamilyQualification.Principal.actual
        principal selected root expressionSyntax certificate receipt sameIssuer factory copies
    have identifier : code.id = id := receipt.identifier
    have emitted : code.lowered = lowered := receipt.emitted
    have sameNode : code.sourceNode = node :=
      receipt.sourceNodeEq.trans (Option.some.inj (actualFound.symm.trans found))
    have codeTyped : ExpressionHasType (source principal.named) context code.id code.sourceNode.type := by
      rw [identifier, sameNode]
      exact sourceTyped
    have sourceType := receipt.sourceFacts.sourceType
    rw [← receipt.sourceNodeEq] at sourceType
    have ordinary := receipt.sourceFacts.ordinary
    rw [← receipt.sourceNodeEq] at ordinary
    have coercions := receipt.sourceFacts.coercions
    rw [← receipt.sourceNodeEq] at coercions
    cases trace.sound with
    | value valueTrace =>
      rename_i actualValue
      have codeTrace : Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram)
          context principal.dictionary (source principal.named) environment before code.id actualValue after := by
        simpa only [identifier, closure] using valueTrace
      obtain ⟨copies, rfl, copy⟩ := RecursiveNamedLambdaFormationHeads.source_value_of_code
        (values := .initial compiled.compatible.checked) (indexed := compiled.indexed)
        (program := Program.ofChecked compiled.sourceProgram) code support.body.unique coercions codeTrace
      let packet := CallableIndexedOwnedPreparedCanonicalCaptureReceipts.Principal.packet_at_capture
        principal.named owner complete environments agrees typed initial.1 initial.2
      have admittedCapture := CallableIndexedOwnedPreparedCanonicalCaptureReceipts.Principal.admission_at_capture
        principal.named owner complete environments agrees typed initial.1 initial.2 context admitted
      obtain ⟨formed, _sourceTrace, nativeTrace, _member, ⟨_reachedCapture, _relatedCapture, post⟩, _determined⟩ :=
        CallableIndexedOwnedPreparedFunctionModelPrincipalFormationPosts.formation_post
          (compiled := compiled) (headers := headers) (keys := keys)
          (function := closure principal.named parameters sourceResult statements context principal.dictionary environment)
          (scope := scope) (actual := actual) (mapping := mapping) (world := world) (heap := before) (store := store)
          (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
          (captured := captured) (code := code) (owner := owner)
          (qualification := nativeFacet) (profile := profile)
          (models := CallableIndexedOwnedPreparedPositiveFunctionOrigins.functions
            (compiled := compiled) nativeFacet headers keys bodyRegistry faults profile)
          (lift := fun member => .closure
            (CallableIndexedOwnedPreparedPositiveFunctionOrigins.closure_of_direct owners member))
          (support := support) (qualified := qualified)
          (prepared := CallableIndexedOwnedPreparedSelectedNativeFamilyQualification.principal_prepared (qualified environment))
          (initial := initial.1) (packet := packet)
          (cells := heaps) (wellFormed := wellFormed) (runtime := runtime) (covers := covers) (locals := locals)
          (typed := codeTyped) (sourceType := sourceType) (admitted := admittedCapture) ordinary coercions
      obtain ⟨rfl, rfl⟩ := Dynamic.EnvironmentCopies.functional copy formed.copy
      let formedValue := CallableIndexedLambdaValues.value (prepared := compiled.indexed)
        (function := closure principal.named parameters sourceResult statements context principal.dictionary environment)
        (scope := scope) (administrative := captured.administrative) code formed.embedding
        (initial.1.rows owner.position).authority.current formed.closureActual
      let reached := (CallableIndexedOwnedOriginCanonicalState.administrativeTransport (headers := headers) owner principal.named).extend initial
        formed.maps formed.worlds formed.frame formed.copy.metadata_extends
      have related := (CallableIndexedOwnedOriginCanonicalState.administrativeTransport (headers := headers) owner principal.named).related initial
        formed.maps formed.worlds formed.frame formed.copy.metadata_extends
      refine ⟨.inRight .word formedValue, formed.finalStore, formed.finalMap, formed.finalWorld, ?_, ?_, post.cells,
        formed.maps, formed.worlds, formed.frame, formed.copy.metadata_extends, reached, related, ?_⟩
      · simpa only [emitted, sameEmbedding, formedValue,
          CallableIndexedOwnedPreparedDirectFormationReceipts.Principal.history_at, History.native] using nativeTrace
      · simpa only [sameNode, emitted, closure, formedValue,
          CallableIndexedOwnedPreparedDirectFormationReceipts.Principal.history_at, History.native] using post.result
      · refine ⟨CallableIndexedOwnedIndirectExpressionHeads.StableRows.after_administrative ((bridge).pool initial)
          ((bridge).pool reached) admitted.rows formed.frame, ?_⟩
        intro value same
        simpa only [sameNode, closure] using post.admission.successful value same
    | fault failed =>
      rename_i actualReason
      have codeFailed : Dynamic.ExpressionFaults (Program.ofChecked compiled.sourceProgram)
          context principal.dictionary (source principal.named) environment before code.id actualReason after := by
        simpa only [identifier, closure] using failed
      exact False.elim (RecursiveNamedLambdaFormationHeads.excludes_fault_of_code
        (values := .initial compiled.compatible.checked) (indexed := compiled.indexed)
        (program := Program.ofChecked compiled.sourceProgram) code support.body.unique coercions codeFailed)

include profile owners complete wellFormed runtime covers in
/-- Independent native completion uses one actual formation and its own
Source grade. The same qualified post stays in the caller's reached packet. -/
theorem reflects_at (size : Nat) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge model context principal.dictionary (source principal.named)
      (Lambdas principal selected root expressionSyntax headers (context := context) (scope := scope) children) faults size := by
  intro childScope id lowered certified node found sourceTyped mapping world administrative environment canonical actual actualContext
    before store ξ result finalStore environments heaps locals agrees typed initial admitted completed
  cases certified with
  | @actual childFuel id lowered actualNode parameters sourceResult statements reported nativeType allowed actualFound form certificate accepted parentTyped metadata raw finite receipt sameIssuer factory =>
    let captured := CallableIndexedOwnedPreparedCanonicalCaptureReceipts.Principal.captured
      principal.named owner complete environments agrees typed initial.1 initial.2
    have sameEmbedding : captured.embedding = ξ := rfl
    let code := RecursiveNamedLambdaFormationHeads.recaptureCode
      (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) receipt.site.code environment
    let support := (CallableIndexedOwnedPreparedPrincipalLambdaSupport.Support.of_site
      (SelectedReceipt.principal principal selected) receipt.site
      expressionSyntax (CallableIndexedOwnedPreparedNativeCompilerChildren.certificates root expressionSyntax
        (CallableIndexedOwnedPreparedCanonicalCaptureReceipts.«prefix» (compiled := compiled) principal.named))
      receipt.shell.issued receipt.shell.diagnosticPolicy receipt.body).recapture environment
    have qualified : ∀ copies, (nativeFacet).principal (code.recapture copies) (support.recapture copies) :=
      fun copies => CallableIndexedOwnedPreparedSelectedNativeFamilyQualification.Principal.actual
        principal selected root expressionSyntax certificate receipt sameIssuer factory copies
    have identifier : code.id = id := receipt.identifier
    have emitted : code.lowered = lowered := receipt.emitted
    have sameNode : code.sourceNode = node :=
      receipt.sourceNodeEq.trans (Option.some.inj (actualFound.symm.trans found))
    have codeTyped : ExpressionHasType (source principal.named) context code.id code.sourceNode.type := by
      rw [identifier, sameNode]
      exact sourceTyped
    have sourceType := receipt.sourceFacts.sourceType
    rw [← receipt.sourceNodeEq] at sourceType
    have ordinary := receipt.sourceFacts.ordinary
    rw [← receipt.sourceNodeEq] at ordinary
    have coercions := receipt.sourceFacts.coercions
    rw [← receipt.sourceNodeEq] at coercions
    let packet := CallableIndexedOwnedPreparedCanonicalCaptureReceipts.Principal.packet_at_capture
      principal.named owner complete environments agrees typed initial.1 initial.2
    have admittedCapture := CallableIndexedOwnedPreparedCanonicalCaptureReceipts.Principal.admission_at_capture
      principal.named owner complete environments agrees typed initial.1 initial.2 context admitted
    obtain ⟨formed, sourceTrace, _nativeTrace, _member, ⟨_reachedCapture, _relatedCapture, post⟩, determined⟩ :=
      CallableIndexedOwnedPreparedFunctionModelPrincipalFormationPosts.formation_post
        (compiled := compiled) (headers := headers) (keys := keys)
        (function := closure principal.named parameters sourceResult statements context principal.dictionary environment)
        (scope := scope) (actual := actual) (mapping := mapping) (world := world) (heap := before) (store := store)
        (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
        (captured := captured) (code := code) (owner := owner)
        (qualification := nativeFacet) (profile := profile)
          (models := CallableIndexedOwnedPreparedPositiveFunctionOrigins.functions
            (compiled := compiled) nativeFacet headers keys bodyRegistry faults profile)
          (lift := fun member => .closure
            (CallableIndexedOwnedPreparedPositiveFunctionOrigins.closure_of_direct owners member))
          (support := support) (qualified := qualified)
        (prepared := CallableIndexedOwnedPreparedSelectedNativeFamilyQualification.principal_prepared (qualified environment))
        (initial := initial.1) (packet := packet)
        (cells := heaps) (wellFormed := wellFormed) (runtime := runtime) (covers := covers) (locals := locals)
        (typed := codeTyped) (sourceType := sourceType) (admitted := admittedCapture) ordinary coercions
    have codeCompleted : Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore := by
      simpa only [emitted, sameEmbedding] using completed.sound
    obtain ⟨rfl, rfl⟩ := determined result finalStore codeCompleted
    obtain ⟨sourceSize, sized⟩ := RecursiveNamedCallBounds.ExpressionOutcome.has_size
      (Dynamic.ExpressionEvaluatesOutcome.value sourceTrace)
    let reached := (CallableIndexedOwnedOriginCanonicalState.administrativeTransport (headers := headers) owner principal.named).extend initial
      formed.maps formed.worlds formed.frame formed.copy.metadata_extends
    have related := (CallableIndexedOwnedOriginCanonicalState.administrativeTransport (headers := headers) owner principal.named).related initial
      formed.maps formed.worlds formed.frame formed.copy.metadata_extends
    refine ⟨sourceSize, .value (.closure formed.closure), formed.finalHeap, formed.finalMap, formed.finalWorld, ?_, ?_,
      post.cells,
      formed.maps, formed.worlds, formed.frame, formed.copy.metadata_extends, reached, related, ?_⟩
    · simpa only [identifier, closure] using sized
    · simpa only [sameNode, emitted] using post.result
    · refine ⟨CallableIndexedOwnedIndirectExpressionHeads.StableRows.after_administrative ((bridge).pool initial)
        ((bridge).pool reached) admitted.rows formed.frame, ?_⟩
      intro value same
      simpa only [sameNode, closure] using post.admission.successful value same

end Semantics
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedSelectedPositivePrincipalLambdaHeads
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedSelectedPositiveLambdaPackets
/-! Each actual raw lambda branch and its genuine fixed-prefix native witness
construct one tagged compiler Receipt, then retain the occurrence factory for
THAT receipt's body read fuel. The same accepted Certificate/action/Source row
is forwarded to the positive runtime lambda leaf. Ordinary and Principal roots
keep their actual caller identity and full dictionary.

The Source body receipt and finite compiler occurrence factory are static
inputs. No Tree, expression execution, application, or body law is accepted. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedSelectedPositiveLambdaPackets
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration CallableIndexedLambdaValues
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedContextualCompilerPolicyProfiles
open CallableIndexedOwnedSelectedDiagnosticIssuerReceipts (SelectedReceipt lowered)
open CallableIndexedOwnedPreparedNativeSiteShellReceipts (FiniteBodyReceipts)
open CallableIndexedOwnedPreparedNativeLambdaCompilerReceipts (Receipt)
open CallableIndexedOwnedPreparedCanonicalCaptureReceipts («prefix»)
open CallableIndexedOwnedPreparedNativeFamilyStaticQualification (OccurrenceFactory)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}

namespace Ordinary
variable {caller : Header compiled (Program.ofChecked compiled.sourceProgram)} {index : Nat}
  (selected : SelectedReceipt compiled caller.named index)
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) caller.named (lowered compiled selected.diagnostics)
    selected.code selected.compilation rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  (expressionSyntax : TypedSource → ExpressionId → Prop)
  (headers : RecursiveNamedCatalog.Inventory compiled.indexed.ancestry (.initial compiled.compatible.checked)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions (Program.ofChecked compiled.sourceProgram))
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {scope : SourceCoreLocalCell.Scope}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context (source caller.named))
  (covers : evidence.Covers context)
  (ownership : LocalIdentityOwnership (source caller.named))
  (declarations : CompatibleExpressionReads.ScopeDeclarations (source caller.named) scope context)
  (sameReason : rootReasonAt = selected.diagnostics.program.reasonAt caller.named.signature.key)
  (sameLedger : context.solvedRequirements = (CallableIndexedNamedGeneration.context compiled.indexed caller.named).solvedRequirements)

include profile runtime covers ownership declarations sameReason sameLedger in
/-- The compiler creates the Receipt once. The static factory is selected only
at that literal generated Receipt and exact selected issuer identity. -/
theorem of_compiler {children : GenericExpressionMeaning.Certificate}
    {childFuel id lowered node parameters result statements reported nativeType}
    (allowed : expressionSyntax (source caller.named) id)
    (found : (source caller.named).lookupExpression? id = some node)
    (form : node.form = .lambda parameters result statements)
    (certificate : CallableIndexedLambdaCertificates.Certificate root.selected.policy root.selected.lowerBody childFuel
      (CallableIndexedNamedGeneration.context compiled.indexed caller.named) (source caller.named) scope
      id node parameters result statements reported rootReasonAt lowered)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody (childFuel + 1)
      (CallableIndexedNamedGeneration.context compiled.indexed caller.named) (source caller.named) scope id rootReasonAt = .ok lowered)
    (sourceTyped : ExpressionHasType (source caller.named) context id node.type)
    (metadata : CompatibleExpressionReads.Metadata compiled.compatible.checked (source caller.named) id node lowered.type)
    (coercions : node.coercions = [])
    (raw : HasType (SourceCoreLocalCell.coreContext scope ++ «prefix» (compiled := compiled) caller.named)
      lowered.expression nativeType compiled.indexed.layouts.definitions)
    (finite : FiniteBodyReceipts (source caller.named) (expressionSyntax (source caller.named)) context parameters result statements)
    (occurrences : ∀ receipt : Receipt root expressionSyntax certificate (sourceContext := context) (evidence := evidence),
      receipt.shell.issued = CallableIndexedOwnedPreparedNativeSiteShellReceipts.issued_at_site selected receipt.site →
      OccurrenceFactory root expressionSyntax (some evidence) headers receipt.body.readFuel) :
    CallableIndexedOwnedPreparedSelectedPositiveOrdinaryLambdaHeads.Lambdas selected root expressionSyntax headers
      (context := context) (evidence := evidence) (scope := scope) children scope id lowered := by
  obtain ⟨receipt, sameIssuer⟩ := CallableIndexedOwnedPreparedSelectedPositiveOrdinaryLambdaHeads.compiler_receipt
    selected root expressionSyntax profile runtime covers ownership declarations sameLedger
    certificate found form sourceTyped coercions accepted raw finite
  exact .actual allowed found form certificate accepted sourceTyped metadata raw finite
    receipt (CallableIndexedOwnedContextualLambdaProvenance.BodyReasons.of_issued selected.found
      (receipt.reason.trans sameReason)) declarations sameIssuer (occurrences receipt sameIssuer)
end Ordinary

namespace Principal
variable {method : ExecutableImplMethods.CheckedMethod}
  (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
  (selected : SelectedReceipt compiled principal.named principal.cached.index)
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) principal.named (lowered compiled selected.diagnostics)
    selected.code selected.compilation rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  (expressionSyntax : TypedSource → ExpressionId → Prop)
  (headers : RecursiveNamedCatalog.Inventory compiled.indexed.ancestry (.initial compiled.compatible.checked)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions (Program.ofChecked compiled.sourceProgram))
  {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context (source principal.named))
  (covers : principal.dictionary.Covers context)
  (ownership : LocalIdentityOwnership (source principal.named))
  (declarations : CompatibleExpressionReads.ScopeDeclarations (source principal.named) scope context)
  (sameLedger : context.solvedRequirements = (CallableIndexedNamedGeneration.context compiled.indexed principal.named).solvedRequirements)

include profile runtime covers ownership declarations sameLedger in
/-- The compiler creates the Receipt once. The static factory is selected only
at that literal generated Receipt and exact selected issuer identity. -/
theorem of_compiler {children : GenericExpressionMeaning.Certificate}
    {childFuel id lowered node parameters result statements reported nativeType}
    (allowed : expressionSyntax (source principal.named) id)
    (found : (source principal.named).lookupExpression? id = some node)
    (form : node.form = .lambda parameters result statements)
    (certificate : CallableIndexedLambdaCertificates.Certificate root.selected.policy root.selected.lowerBody childFuel
      (CallableIndexedNamedGeneration.context compiled.indexed principal.named) (source principal.named) scope
      id node parameters result statements reported rootReasonAt lowered)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody (childFuel + 1)
      (CallableIndexedNamedGeneration.context compiled.indexed principal.named) (source principal.named) scope id rootReasonAt = .ok lowered)
    (sourceTyped : ExpressionHasType (source principal.named) context id node.type)
    (metadata : CompatibleExpressionReads.Metadata compiled.compatible.checked (source principal.named) id node lowered.type)
    (coercions : node.coercions = [])
    (raw : HasType (SourceCoreLocalCell.coreContext scope ++ «prefix» (compiled := compiled) principal.named)
      lowered.expression nativeType compiled.indexed.layouts.definitions)
    (finite : FiniteBodyReceipts (source principal.named) (expressionSyntax (source principal.named)) context parameters result statements)
    (occurrences : ∀ receipt : Receipt root expressionSyntax certificate (sourceContext := context) (evidence := principal.dictionary),
      receipt.shell.issued = CallableIndexedOwnedPreparedNativeSiteShellReceipts.issued_at_site selected receipt.site →
      OccurrenceFactory root expressionSyntax (some principal.dictionary) headers receipt.body.readFuel) :
    CallableIndexedOwnedPreparedSelectedPositivePrincipalLambdaHeads.Lambdas principal selected root expressionSyntax headers
      (context := context) (scope := scope) children scope id lowered := by
  obtain ⟨receipt, sameIssuer⟩ := CallableIndexedOwnedPreparedSelectedPositivePrincipalLambdaHeads.compiler_receipt
    principal selected root expressionSyntax profile runtime covers ownership declarations sameLedger
    certificate found form sourceTyped coercions accepted raw finite
  exact .actual allowed found form certificate accepted sourceTyped metadata raw finite
    receipt sameIssuer (occurrences receipt sameIssuer)
end Principal

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedSelectedPositiveLambdaPackets
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedSelectedTerminalLambdaCompilerReceipts
/-! A literal selected lambda receipt retains the accepted body action and
its compiler recipe. A supported terminal form therefore constructs its
terminal compiler receipt internally, before any body evaluation is used. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedSelectedTerminalLambdaCompilerReceipts
open Core Frontend SourceInference
open CallableIndexedNamedGeneration CallableIndexedLambdaValues
open CallableIndexedOwnedContextualCompilerPolicyProfiles
open CallableIndexedOwnedContextualLambdaJointStaticReceipts
open CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {named : Named}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : Compilation compiled.indexed named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) named diagnostics namedCode compilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  (expressionSyntax : TypedSource → ExpressionId → Prop)
  {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  {node : ExpressionNode} {parameters : List TypedBinder} {result : TypeSystem.Ty}
  {statements : List StatementId} {reported : Ty} {childFuel : Nat}
  (certificate : CallableIndexedLambdaCertificates.Certificate root.selected.policy root.selected.lowerBody childFuel
    (context compiled.indexed named) (source named) scope id node parameters result statements reported rootReasonAt lowered)
  (actual : CallableIndexedOwnedPreparedNativeLambdaCompilerReceipts.Receipt root expressionSyntax certificate
    (sourceContext := sourceContext) (evidence := evidence))

/-- Only the supported actual terminal shape is a static input. The body
compiler equation, policy, parameter scope, used child and footer are obtained
from the same retained compiler receipt; no output equality is requested. -/
theorem of_receipt {expression : ExpressionId}
    (terminal : Terminal actual.site.code.view expression statements) :
    Nonempty (Receipt (bodyPolicy compilation actual.site.code) actual.site.code.fuel actual.site.code.view
      (actual.site.code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      expression statements actual.site.code.receipt.resultCore actual.site.code.reasonAt
      actual.site.code.compilation.internalReason actual.site.code.compilation.internalReason
      actual.site.code.receipt.body) := by
  have accepted := actual.site.code.receipt.bodyCompiled
  rw [callback_of_recipe compilation actual.body.recipe] at accepted
  have parameterScope := FunctionCode.Parameters.scope
    (FunctionCode.Parameters.of_accepted actual.site.code.receipt.parametersCompiled)
  have sameScope : actual.site.code.receipt.bodyScope =
      actual.site.code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope := by
    simpa only [List.map_reverse] using parameterScope
  rw [sameScope] at accepted
  exact CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.of_accepted
    actual.shell.static.readPolicy terminal accepted

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedSelectedTerminalLambdaCompilerReceipts
end
