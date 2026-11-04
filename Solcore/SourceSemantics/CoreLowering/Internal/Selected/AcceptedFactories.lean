import Solcore.SourceSemantics.CoreLowering.Internal.Accepted.ProgramCompletion
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.NamedAdmission
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.ExpressionBounds
import Solcore.SourceSemantics.CoreLowering.Internal.Accepted.NamedExpressions
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPrimitiveMethodAdmission
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedClosedCoercionAdmission
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.CatalogOrigins
import Solcore.SourceSemantics.CoreLowering.Internal.Accepted.PreparedLambdaBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Accepted.CompilerProfiles
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedScopedFactoryAdmission
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedScopedClosureAdmission
import Solcore.SourceSemantics.CoreLowering.Internal.Generalized.AcceptedPrefixes
import Solcore.SourceSemantics.CoreLowering.Internal.Generalized.LambdaCompilation
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.Coercions
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.MethodRoots
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredArgumentAlignment
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedIndirectExpressionHeads
import Solcore.SourceSemantics.CoreLowering.CallableCoercionSpineEvaluation
import Solcore.SourceSemantics.Staging.RecursiveErasure
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.IndirectCalls
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.PhysicalCalls
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedDirectNamedProfileExtraction
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.NamedBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.MethodBodies
import Solcore.SourceSemantics.CoreLowering.CallableMethodBodyCoherence
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.ExpressionBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicSignatureCatalog
import Solcore.SourceSemantics.CoreLowering.RecursiveMethodDictionaryIdentity
import Solcore.SourceSemantics.CoreLowering.CallableMethodOriginSource
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.MethodScopedRoots
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.MethodSelection
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.CallerMethodSelection
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedScopedMethodAdmission
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryCatalogPublicAdmission
import Solcore.SourceSemantics.SelectedOperatorTypingCertificates

/-!
# Selected compilations: accepted factories and method issuance

Accepted factories, primitive methods, method selection issuance and coercion issuance of a selected compilation, with the catalog front door that recovers a start entry.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationAcceptedFactories
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationAcceptedFactories
open Core Frontend SourceInference
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedNamedGeneration (context)
open CallableIndexedOwnedPreparedStagedDirectCallCertificates (Child Supported)
open AcceptedNamedFactoryAdmission (Produced ReturningAt ExpressionAt)

private theorem returning_typed {source : TypedSource} {control : ControlContext}
    {lexical final : SourceSemantics.Context} {id : StatementId} {facts : StatementFacts}
    {node : StatementNode} {expression : ExpressionId}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (form : node.form = .returnStmt (some expression))
    (typed : StatementHasType source control lexical id final facts) :
    ExpressionHasType source lexical expression control.returnType ∧ node.type = control.returnType := by
  have shape : ∀ other, ContainsStatement source id other → other = node := by
    intro other present
    exact Option.some.inj ((lookupStatement?_complete unique present).symm.trans found)
  cases typed <;> have actual := shape _ (by assumption) <;> cases actual <;> simp_all

private theorem head_typed {source : TypedSource} {control : ControlContext}
    {lexical final : SourceSemantics.Context} {id : StatementId} {rest : List StatementId} {facts : BodyFacts}
    (typed : StatementsHaveType source control lexical (id :: rest) final facts) :
    ∃ middle headFacts, StatementHasType source control lexical id middle headFacts := by
  cases typed with
  | singleton head => exact ⟨_, _, head⟩
  | cons head _tail => exact ⟨_, _, head⟩

private theorem lambda_return_type {source : TypedSource} {lexical : SourceSemantics.Context}
    {id : ExpressionId} {node : ExpressionNode} {parameters : List TypedBinder} {result : TypeSystem.Ty}
    {statement : StatementId} {returnNode : StatementNode} {expression : ExpressionId}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
    (form : node.form = .lambda parameters result [statement])
    (typed : ExpressionHasType source lexical id node.type)
    (returnFound : source.lookupStatement? statement = some returnNode)
    (returnForm : returnNode.form = .returnStmt (some expression)) : returnNode.type = result := by
  generalize sameType : node.type = reported at typed
  cases typed with
  | @intro _ _ actual raw plan contains original rawType rawValid finalValid requirements =>
    have same : actual = node := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
    subst actual
    rw [form] at original
    cases original with
    | lambda _ _ body _ =>
      obtain ⟨_, _, head⟩ := head_typed body
      exact (returning_typed unique returnFound returnForm head).2

private theorem lambda_typed {source : TypedSource} {lexical : SourceSemantics.Context}
    {id : ExpressionId} {node : ExpressionNode} {parameters : List TypedBinder} {result : TypeSystem.Ty}
    {statements : List StatementId} {reported : TypeSystem.Ty}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
    (form : node.form = .lambda parameters result statements)
    (typed : ExpressionHasType source lexical id reported) :
    ∃ inner final facts, StatementsHaveType source {returnType := result} inner statements final facts := by
  cases typed with
  | @intro _ _ actual raw plan contains original rawType rawValid finalValid requirements =>
    have same : actual = node := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
    subst actual
    rw [form] at original
    cases original with
    | lambda _ _ body _ => exact ⟨_, _, _, body⟩

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {row : SourceSpecialization.SpecializedFunction}
  (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
  {instantiation : DeclarationInstantiation}
  {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
  (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)

/-- Full original typing supplies the lambda's declared inner result, independent
of its native representation. -/
theorem return_type {outer : StatementId} {rest : List StatementId} {outerNode : StatementNode}
    {id : ExpressionId} {node : ExpressionNode} {parameters : List TypedBinder} {result : TypeSystem.Ty}
    {statement : StatementId} {returnNode : StatementNode} {expression : ExpressionId}
    (roots : header.function.body = outer :: rest)
    (outerFound : header.function.source.lookupStatement? outer = some outerNode)
    (outerForm : outerNode.form = .returnStmt (some id))
    (found : header.function.source.lookupExpression? id = some node)
    (form : node.form = .lambda parameters result [statement])
    (returnFound : header.function.source.lookupStatement? statement = some returnNode)
    (returnForm : returnNode.form = .returnStmt (some expression))
    (certified : SelectedCompilationNamedSourceTyping.Certified header) : returnNode.type = result := by
  obtain ⟨_, _, typed, _complete⟩ := certified.statements
  rw [roots] at typed
  obtain ⟨_, _, first⟩ := head_typed typed
  have lambdaTyped := (returning_typed header.unique outerFound outerForm first).1
  obtain ⟨actual, present, sameType⟩ := lambdaTyped.stored_type
  have same : actual = node := Option.some.inj ((lookupExpression?_complete header.unique present).symm.trans found)
  subst actual
  exact lambda_return_type header.unique found form (sameType ▸ lambdaTyped) returnFound returnForm

/-- The inner typing derivation belongs to the original lambda in this Header. -/
theorem inner_typing {outer : StatementId} {rest : List StatementId} {outerNode : StatementNode}
    {id : ExpressionId} {node : ExpressionNode} {parameters : List TypedBinder} {result : TypeSystem.Ty}
    {statements : List StatementId}
    (roots : header.function.body = outer :: rest)
    (outerFound : header.function.source.lookupStatement? outer = some outerNode)
    (outerForm : outerNode.form = .returnStmt (some id))
    (found : header.function.source.lookupExpression? id = some node)
    (form : node.form = .lambda parameters result statements)
    (certified : SelectedCompilationNamedSourceTyping.Certified header) :
    ∃ inner final facts, StatementsHaveType header.function.source {returnType := result}
      inner statements final facts := by
  obtain ⟨_, _, typed, _complete⟩ := certified.statements
  rw [roots] at typed
  obtain ⟨_, _, first⟩ := head_typed typed
  exact lambda_typed header.unique found form (returning_typed header.unique outerFound outerForm first).1

include aligned in
/-- Original finite return facts identify the produced lambda and inner action.
The compiler supplies the native read, captured scope, allocation and body. -/
theorem produced_of_returning {outer : StatementId} {rest : List StatementId} {outerNode : StatementNode}
    {id : ExpressionId} {node : ExpressionNode} {parameters : List TypedBinder} {result : TypeSystem.Ty}
    {statement : StatementId} {returnNode : StatementNode} {expression : ExpressionId}
    (roots : header.function.body = outer :: rest)
    (outerFound : header.function.source.lookupStatement? outer = some outerNode)
    (outerForm : outerNode.form = .returnStmt (some id))
    (found : header.function.source.lookupExpression? id = some node)
    (form : node.form = .lambda parameters result [statement])
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context compiled.indexed prepared.named).owner ∧ binding.initializer = id)) = none)
    (returnFound : header.function.source.lookupStatement? statement = some returnNode)
    (returnForm : returnNode.form = .returnStmt (some expression))
    (certified : SelectedCompilationNamedSourceTyping.Certified header) :
    ∃ produced : Produced prepared header,
      produced.certificate.returnStatement = statement ∧ produced.certificate.returnExpression = expression := by
  have terminal : CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Terminal
      header.function.source id header.function.body := by
    rw [roots]
    exact .returning rest outerFound outerForm
  obtain ⟨receipt⟩ := CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.of_accepted
    (RecursiveNamedPreparedHeaderPolicies.Prepared.header_read prepared aligned) terminal aligned.accepted
  let actual : ReturningAt header := ⟨outer, rest, outerNode, id, roots, outerFound, outerForm, receipt⟩
  obtain ⟨fuel, predecessor, root, ⟨head⟩⟩ := AcceptedNamedExpressionFlow.of_header prepared aligned receipt.generated
  let action : ExpressionAt prepared actual := ⟨fuel, predecessor, root, head⟩
  have same : action.head.node = node := Option.some.inj (action.head.found.symm.trans found)
  have actualForm : action.head.node.form = .lambda parameters result [statement] := same ▸ form
  have profile := CallableIndexedOwnedContextualCompilerPolicyProfiles.lambda_policy action.root
    (scope := header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
    (reasonAt := header.reasonAt) action.head.found actualForm (same ▸ requirements) (same ▸ coercions) ordinary
  have plain : action.head.special = none := by
    have noSpecial := profile.special
      (Child action.root.selected.policy action.root.selected.lowerBody action.fuel
        (context compiled.indexed prepared.named)) (action.fuel + 1)
    exact Except.ok.inj (action.head.selected.symm.trans noSpecial)
  obtain ⟨reported, read, actualRequirements, actualCoercions, actualOrdinary, ⟨compiler⟩⟩ :=
    AcceptedContextualLambdaReceipt.of_head action.root action.head plain actualForm
  have returnType := return_type roots outerFound outerForm
    action.head.found actualForm returnFound returnForm certified
  let certificate : CallableIndexedOwnedPreparedNamedFactoryAdmission.SourceCertificate
      compiled prepared.named header.function.source header.function.body :=
    ⟨id, terminal, action.head.node, parameters, result, statement, returnNode, expression, reported,
      action.head.found, actualForm, action.head.owner, actualRequirements, actualCoercions, actualOrdinary,
      read, returnFound, returnForm, returnType⟩
  obtain ⟨inner⟩ := AcceptedContextualLambdaReceipt.inner_returning action.root compiler
    (CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Terminal.returning [] returnFound returnForm)
  exact ⟨⟨certificate, actual, action, rfl, rfl, compiler, inner⟩, rfl, rfl⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationAcceptedFactories
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationAcceptedCoercedFactories
/-! The same returned-lambda compiler receipt exposes the inner constrained
direct call. Its full evidence suffix and accepted argument actions are used
before issuing the existing coerced closure certificate. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3200000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationAcceptedCoercedFactories
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (context)
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedNamedSyntaxAdmission (DirectSite)
open CallableIndexedOwnedPreparedStagedDirectCallCertificates (Supported)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)
open AcceptedNamedFactoryAdmission (Produced)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {row : SourceSpecialization.SpecializedFunction}
  (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
  {instantiation : DeclarationInstantiation}
  {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
  (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
  {rows : List SourceSpecialization.SpecializedFunction}

private theorem origin_owner : ∃ signature ∈ compiled.sourceProgram.signatures.functions,
    prepared.named.specialized.function.typedBody.owner = signature.id := by
  obtain ⟨request, signature, generic, member, _genericMember, _resolved, accepted⟩ := prepared.origin
  have identities := RecursiveNamedSpecializationBodyFacts.identities accepted
  have fields := CallableCoercionBodyProvenance.specialization_fields accepted
  refine ⟨signature, member, ?_⟩
  rw [prepared.same, fields.1, SourceSpecialization.applyCheckedFunction_bodyOwner,
    identities.2.1, identities.1]

include aligned in
theorem of_produced (produced : Produced prepared header)
    (profile : CompilerCoercedExpressionProfile.Profile compiled prepared.named
      header.function.source rows produced.certificate.returnExpression)
    (supported : ∀ instantiation, DirectSite rows instantiation → Supported compiled.indexed.base.plan instantiation) :
    Nonempty (CallableIndexedOwnedPreparedCoercedClosureAdmission.BodyCertificate compiled
      prepared.named rows [produced.certificate.returnStatement]) := by
  have generated := produced.inner.generated
  change SourceCoreFunctions.lowerExpressionWithPolicy produced.action.root.selected.policy
    produced.action.root.selected.lowerBody (min produced.inner.childFuel produced.action.fuel)
    (context compiled.indexed prepared.named) header.function.source produced.compiler.bodyScope
    produced.certificate.returnExpression header.reasonAt = .ok produced.inner.child at generated
  generalize fuelEq : min produced.inner.childFuel produced.action.fuel = fuel at generated
  cases fuel with
  | zero => simp only [SourceCoreFunctions.lowerExpressionWithPolicy] at generated; cases generated
  | succ predecessor =>
    obtain ⟨head⟩ := AcceptedNamedExpressionFlow.Head.of_accepted generated
    have same : head.node = profile.node := Option.some.inj (head.found.symm.trans profile.found)
    obtain ⟨receipt⟩ := AcceptedCoercedDirectExpressionReceipt.of_head produced.action.root head
      (same ▸ profile.form) (supported _ profile.direct) (same ▸ profile.coercions) profile.initializer
    have children : ∀ argument ∈ profile.arguments,
        GeneralSyntax header.function.source argument (fun _ => False) :=
      AcceptedCoercedDirectExpressionReceipt.children produced.action.root receipt profile.children
    have terminal := produced.inner.terminal
    have metadata := profile.metadata
    have source := (CallableIndexedOwnedPreparedNamedSourceAdmissionTransport.header_data prepared aligned).1
    obtain ⟨signature, member, owner⟩ := origin_owner prepared
    exact ⟨{
      expression := produced.certificate.returnExpression
      node := profile.node
      callee := profile.callee
      arguments := profile.arguments
      instantiation := profile.instantiation
      terminal := Eq.mp (congrArg (fun source =>
        CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Terminal source
          produced.certificate.returnExpression [produced.certificate.returnStatement]) source) terminal
      found := Eq.mp (congrArg (fun source => source.lookupExpression?
        produced.certificate.returnExpression = some profile.node) source) profile.found
      form := profile.form
      coercions := profile.coercions
      requirements := profile.requirements
      children := fun argument member => Eq.mp (congrArg (fun source =>
        GeneralSyntax source argument (fun _ => False)) source) (children argument member)
      initializer := profile.initializer
      direct := profile.direct
      metadata := Eq.mp (congrArg (fun source =>
        CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles.NativeMetadataFor
          compiled.indexed prepared.named source (fun _ => False)) source) metadata
      signature := signature
      signatureMember := member
      sourceOwner := owner }⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationAcceptedCoercedFactories
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationAcceptedPrimitiveMethods
/-! Terminal primitive method certificates follow the retained compiler action.
The finite conditions describe original forms and metadata; no expression
syntax recognizer or method execution is supplied. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationAcceptedPrimitiveMethods
open Core Frontend SourceInference
open AcceptedNamedExpressionFlow
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)
open CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles (MetadataFor)
open CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles (SupportedForm)
open CallableIndexedOwnedPreparedNamedSyntaxAdmission (metadata?)
open CallableIndexedOwnedPreparedNamedSourceAdmissionTransport (statements)
open CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts (Terminal)
open CallableIndexedOwnedPreparedPrimitiveMethodAdmission (SourceCertificate)

inductive Form : ExpressionForm → Prop where
  | localRead (name : String) (binder : Resolved.LocalId) : Form (.reference name (.local binder))
  | boolean (name : String) (value : Bool) : Form (.reference name (.builtinBoolean value))
  | integer (literal : Solcore.Syntax.CoreLiteralValue) (resolution : IntegerLiteralResolution) : Form (.integerLiteral literal resolution)
  | conditional (test yes no : ExpressionId) : Form (.conditional test yes no)

def Forms (source : TypedSource) : Prop :=
  ∀ id node, source.lookupExpression? id = some node → Form node.form

/-- Inspect only the original node form, without following expression edges. -/
def form? : (form : ExpressionForm) → Option (PLift (Form form))
  | .reference name (.local binder) => some ⟨.localRead name binder⟩
  | .reference name (.builtinBoolean value) => some ⟨.boolean name value⟩
  | .integerLiteral literal resolution => some ⟨.integer literal resolution⟩
  | .conditional test yes no => some ⟨.conditional test yes no⟩
  | _ => none

private def nodeForm? : (node : Node) →
    Option (PLift (∀ expression, node = .expression expression → Form expression.form))
  | .statement _ => some ⟨by intro expression impossible; cases impossible⟩
  | .expression expression => do
    let ⟨form⟩ ← form? expression.form
    pure ⟨by intro actual same; cases same; exact form⟩

private def nodeForms? : (nodes : List Node) →
    Option (PLift (∀ node ∈ nodes, ∀ expression, node = .expression expression → Form expression.form))
  | [] => some ⟨by intro node impossible; cases impossible⟩
  | first :: rest => do
    let ⟨head⟩ ← nodeForm? first
    let ⟨tail⟩ ← nodeForms? rest
    pure ⟨by
      intro node member expression same
      rcases List.mem_cons.mp member with first | member
      · cases first; exact head expression same
      · exact tail node member expression same⟩

/-- Every lookupable node receives its original flat form fact. -/
def forms? (source : TypedSource) : Option (PLift (Forms source)) := do
  let ⟨nodes⟩ ← nodeForms? source.nodes
  pure ⟨by
    intro id node found
    exact nodes (.expression node) (lookupExpression?_sound found).1 node rfl⟩

theorem Form.supported {form : ExpressionForm} (allowed : Form form) : SupportedForm form := by
  cases allowed with
  | localRead name binder => exact .read name binder
  | boolean name value => exact .literal (.bool name value)
  | integer literal resolution => exact .literal (.integer literal resolution)
  | conditional test yes no => exact .conditional test yes no

theorem Forms.primitive {source : TypedSource} (forms : Forms source) :
    CallableIndexedOwnedPreparedStagedPrimitiveMethodTerminalSupport.PrimitiveSource source := by
  intro id node found
  have allowed := forms id node found
  generalize shape : node.form = form at allowed
  cases allowed
  · exact .inl ⟨_, _, rfl⟩
  · exact .inl ⟨_, _, rfl⟩
  · exact .inr (.inl ⟨_, _, rfl⟩)
  · exact .inr (.inr ⟨_, _, _, rfl⟩)

private theorem Form.not_method {form : ExpressionForm} (allowed : Form form) : ¬ MethodForm form := by
  cases allowed <;> simp [MethodForm, AcceptedContextualOperatorReceipt.Form]

private theorem Form.no_direct {form : ExpressionForm} (allowed : Form form)
    {callee : ExpressionId} {args : List ExpressionId} {instantiation : DeclarationInstantiation} :
    form ≠ .call callee args (.declaration instantiation) := by cases allowed <;> simp

section Trace
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program}
  {namedCode : Expr} {compilation : CallableIndexedNamedGeneration.Compilation compiled.indexed named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  {root : CallableIndexedOwnedContextualCompilerPolicyProfiles.RootPolicyReceipt
    (compiled := compiled) named diagnostics namedCode compilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered}
  {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Word}
  {fuel : Nat} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  {receipt : PLift (MetadataFor compiled.indexed named source (fun _ => False))}
  (metadata : metadata? compiled.indexed named source (fun _ => False) = some receipt)
  (forms : Forms source)

include metadata forms

private theorem no_boundary_cause
    {head : Head root.selected.policy root.selected.lowerBody fuel
      (CallableIndexedNamedGeneration.context compiled.indexed named) source scope id reasonAt lowered}
    (cause : Cause root head) : False := by
  have allowed := forms id head.node head.found
  have clean := AcceptedNamedExpressionMetadata.at_of_accepted metadata head.found allowed.supported
  cases cause with
  | form _ notLeaf _ _ _ _ _ notComposite _ =>
    generalize eq : head.node.form = shape at allowed
    cases allowed with
    | localRead name binder => exact notLeaf (eq.symm ▸ .read name binder)
    | boolean name value => exact notLeaf (eq.symm ▸ .literal (.bool name value))
    | integer literal resolution => exact notLeaf (eq.symm ▸ .literal (.integer literal resolution))
    | conditional test yes no => exact notComposite (eq.symm ▸ .conditional test yes no)
  | initializer _ actual =>
    have absent := clean.2.1
    rw [(lookupExpression?_sound head.found).2] at absent
    have found := actual.found
    rw [absent] at found
    cases found
  | operatorCoercions _ method _ => exact allowed.not_method method
  | indexOperands _ eq _ =>
    generalize shape : head.node.form = form at allowed
    cases allowed <;> simp_all
  | constructorRange _ eq _ =>
    generalize shape : head.node.form = form at allowed
    cases allowed <;> simp_all
  | special selected _ _ =>
    have plain : specialAction root.selected.policy root.selected.lowerBody fuel
        (CallableIndexedNamedGeneration.context compiled.indexed named) source scope id reasonAt = .ok none := by
      generalize eq : head.node.form = shape at allowed
      cases allowed with
      | localRead name binder =>
        exact (AcceptedNamedExpressionPolicy.leaf_profile root.compilerPolicy receipt.down
          head.found (.inr ⟨name, binder, eq⟩) _ _ scope reasonAt).2.2
      | boolean name value =>
        exact (AcceptedNamedExpressionPolicy.leaf_profile root.compilerPolicy receipt.down
          head.found (.inl (eq.symm ▸ .bool name value)) _ _ scope reasonAt).2.2
      | integer literal resolution =>
        exact (AcceptedNamedExpressionPolicy.leaf_profile root.compilerPolicy receipt.down
          head.found (.inl (eq.symm ▸ .integer literal resolution)) _ _ scope reasonAt).2.2
      | conditional test yes no =>
        exact AcceptedCompositeExpressionReceipt.special_none root head.found
          (eq.symm ▸ .conditional test yes no) clean _ _
    have same := head.selected.symm.trans plain
    rw [selected] at same
    cases same

private theorem no_boundary {trace : Trace root source scope reasonAt fuel id lowered}
    (boundary : Boundary trace) : False := by
  induction boundary with
  | here head cause children => exact no_boundary_cause metadata forms cause
  | child step children entry member next ih => exact ih

/-- The accepted recursive compiler trace supplies the complete original
expression grammar under flat method-form and metadata observations. -/
theorem expression_of_accepted
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody
      fuel (CallableIndexedNamedGeneration.context compiled.indexed named)
      source scope id reasonAt = .ok lowered) : GeneralSyntax source id (fun _ => False) := by
  have covered : ∀ child node, source.lookupExpression? child = some node →
      ∀ callee args instantiation, node.form = .call callee args (.declaration instantiation) → False := by
    intro child node found callee args instantiation form
    exact (forms child node found).no_direct form
  obtain ⟨trace⟩ := Trace.of_accepted (root := root) receipt.down (fun _ impossible => False.elim impossible)
    covered accepted
  cases trace.syntax_or_boundary covered with
  | inl tree => exact tree
  | inr residual =>
    obtain ⟨boundary⟩ := residual
    exact False.elim (no_boundary metadata forms boundary)
end Trace

/-- The retained terminal body exposes its actual expression action. Method
semantics still receives original checked typing through the common selected
support family; this producer supplies only its compiler certificate. -/
theorem of_cached {compiled : SourceCoreUnifiedCompilation.Compiled}
    {method : ExecutableImplMethods.CheckedMethod}
    (cached : CallablePreparedMethodSelection.Cached compiled method.specialized)
    {expression : ExpressionId}
    (terminal : Terminal (AcceptedMethodBodyReceipts.source cached) expression
      (statements (AcceptedMethodBodyReceipts.source cached)))
    (forms : Forms (AcceptedMethodBodyReceipts.source cached))
    {metadata : PLift (MetadataFor compiled.indexed cached.named
      (AcceptedMethodBodyReceipts.source cached) (fun _ => False))}
    (acceptedMetadata : metadata? compiled.indexed cached.named
      (AcceptedMethodBodyReceipts.source cached) (fun _ => False) = some metadata) :
    Nonempty (SourceCertificate compiled cached.named) := by
  have actualTerminal := terminal
  rw [AcceptedMethodBodyAdmission.roots cached] at actualTerminal
  obtain ⟨receipt⟩ := CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.of_accepted
    (AcceptedMethodBodyReceipts.read cached) actualTerminal cached.compilation.bodyCompiled
  obtain ⟨predecessor, _same, ⟨root⟩⟩ := AcceptedMethodBodyReceipts.policy_receipt cached receipt.generated
  exact ⟨⟨expression, terminal, forms.primitive, metadata.down,
    expression_of_accepted (root := root) acceptedMetadata forms root.selected.accepted⟩⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationAcceptedPrimitiveMethods
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPrimitiveMethodNodeFacts
/-! Successful flat inspection retains every original node, even before
occurrence uniqueness has been derived from checking. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPrimitiveMethodNodeFacts
open Frontend SourceInference
open SelectedCompilationAcceptedPrimitiveMethods

theorem nodes_of_accepted {source : TypedSource} {receipt : PLift (Forms source)}
    (accepted : forms? source = some receipt) :
    ∀ node ∈ source.nodes, ∀ expression, node = .expression expression → Form expression.form := by
  unfold forms? at accepted
  simp only [bind, Option.bind] at accepted
  split at accepted
  next => contradiction
  next facts selected => exact facts.down

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPrimitiveMethodNodeFacts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompilerCoercedMethodProfile
/-! The closed coercion lane retains flat checks for every actual cached
method and the existing complete selected coercion catalog. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CompilerCoercedMethodProfile
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedNamedSourceAdmissionTransport (statements)
open CallableIndexedOwnedPreparedNamedSyntaxAdmission (metadata?)
open CallableIndexedOwnedPreparedPrimitiveMethodAdmission (Excluded)
open CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts (Terminal)
open SelectedCompilationAcceptedPrimitiveMethods (Forms forms?)

structure Primitive (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) where
  noOrdinary : ∀ signature ∈ compiled.sourceProgram.signatures.functions,
    named.specialized.declaration ≠ signature.id
  range : SourceSemantics.ParameterSubstitution.RangeWellFormed
    (SourceSemantics.Context.ofSignatures compiled.sourceProgram.signatures) named.specialized.parameterSubstitution
  expression : ExpressionId
  terminal : Terminal named.specialized.function.typedBody expression
    (statements named.specialized.function.typedBody)
  forms : Forms named.specialized.function.typedBody
  formsAccepted : ∃ receipt, forms? named.specialized.function.typedBody = some receipt
  metadataAccepted : ∃ receipt,
    metadata? compiled.indexed named named.specialized.function.typedBody (fun _ => False) = some receipt

def primitive? (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) : Option (Primitive compiled named) := do
  if absent : compiled.sourceProgram.signatures.functions.all (fun signature =>
      decide (named.specialized.declaration ≠ signature.id)) = true then
   let ⟨range⟩ ← CallableIndexedOwnedPreparedOrdinarySyntaxTable.range?
     compiled.sourceProgram.signatures (max 1 compiled.indexed.fuel) named.specialized.parameterSubstitution
   let source := named.specialized.function.typedBody
   match formsAccepted : forms? source with
   | none => none
   | some ⟨forms⟩ =>
     match metadataAccepted : metadata? compiled.indexed named source (fun _ => False) with
     | none => none
     | some receipt =>
       match roots : statements source with
       | [] => none
       | first :: rest =>
         match found : source.lookupStatement? first with
         | none => none
         | some node =>
           match form : node.form with
           | .returnStmt (some expression) =>
             pure ⟨(fun signature member => of_decide_eq_true (List.all_eq_true.mp absent signature member)),
               range, expression, by rw [roots]; exact .returning rest found form,
               forms, ⟨⟨forms⟩, formsAccepted⟩, ⟨receipt, metadataAccepted⟩⟩
           | _ => none
  else none

structure Closed (compiled : SourceCoreUnifiedCompilation.Compiled) : Type where
  catalog : CallableIndexedOwnedPreparedStagedClosedCoercionSelection.Catalog compiled
  methods : ∀ named ∈ compiled.indexed.base.functions,
    Excluded compiled named ∨ Nonempty (Primitive compiled named)

private def methods? (compiled : SourceCoreUnifiedCompilation.Compiled) :
    (rows : List SourceCoreGeneralFunctions.Function) →
      Option (PLift (∀ named ∈ rows, Excluded compiled named ∨ Nonempty (Primitive compiled named)))
  | [] => some ⟨by intro named member; cases member⟩
  | first :: rest => do
    let ⟨head⟩ ← (if excluded : (Program.ofChecked compiled.sourceProgram).methods.all
        (fun definition => decide (first.specialized.function.typedBody.owner ≠ definition.body.source.owner)) = true then
      some ⟨Or.inl (by
        intro definition member
        exact of_decide_eq_true (List.all_eq_true.mp excluded definition member))⟩
      else do
        let profile ← primitive? compiled first
        pure ⟨Or.inr ⟨profile⟩⟩ : Option (PLift (Excluded compiled first ∨ Nonempty (Primitive compiled first))))
    let ⟨tail⟩ ← methods? compiled rest
    pure ⟨by
      intro named member
      rcases List.mem_cons.mp member with same | member
      · exact same ▸ head
      · exact tail named member⟩

def certify (compiled : SourceCoreUnifiedCompilation.Compiled) : Option (Closed compiled) := do
  let ⟨catalog⟩ ← CallableIndexedOwnedPreparedClosedCoercionAdmission.certify compiled
  let ⟨methods⟩ ← methods? compiled compiled.indexed.base.functions
  pure ⟨catalog, methods⟩

end Solcore.SourceSemantics.CoreLowering.CompilerCoercedMethodProfile
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationAcceptedMethods
/-! A genuine method instantiation supplies original Source typing for the
actual cached body. Its accepted statement and expression actions construct
the existing method certificate, preserving its full synthetic specialization. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationAcceptedMethods
open Core Frontend SourceInference
open AcceptedMethodBodyReceipts
open AcceptedNamedBodyFlow AcceptedNamedExpressionFlow
open CallablePreparedMethodSelection (Cached)
open CallableIndexedOwnedPreparedNamedSyntaxAdmission (DirectSite)
open CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles (MetadataFor)
open CallableIndexedOwnedPreparedStagedMethodEvidenceScopedRoots (DirectSource)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)
open CallableIndexedOwnedPreparedScopedMethodAdmission (SourceCertificate)
open CallableIndexedOwnedPreparedNamedSourceAdmissionTransport (statements)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {method : ExecutableImplMethods.CheckedMethod}
  (cached : Cached compiled method.specialized)

theorem child_syntax
    (table : CallableIndexedOwnedPreparedOrdinarySyntaxTable.Table compiled)
    (bodies : SelectedCompilationBodyTyping.Bodies compiled)
    (metadata : MetadataFor compiled.indexed cached.named (source cached) (DirectSite table.rows))
    (covered : ∀ id node, (source cached).lookupExpression? id = some node →
      ∀ callee arguments instantiation, node.form = .call callee arguments (.declaration instantiation) →
        DirectSite table.rows instantiation)
    {reached : ExpressionId → Prop}
    (forms : ReachedForms (source cached) reached)
    (arguments : ReachedArguments (source cached) reached)
    (initializers : ∀ id, reached id → ¬ Nonempty (AcceptedContextualDirectReceipt.InitializerAt
      compiled.indexed (CallableIndexedNamedGeneration.context compiled.indexed cached.named) id))
    {scope : SourceCoreLocalCell.Scope} {fuel : Nat} {id : ExpressionId}
    {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : (policy cached).lowerExpression fuel (source cached) scope id
      (reasonAt cached) = .ok lowered) (present : reached id) :
    GeneralSyntax (source cached) id (DirectSite table.rows) := by
  obtain ⟨catalog⟩ := SelectedCompilationCatalog.of_compiled compiled bodies
  obtain ⟨predecessor, _same, ⟨root⟩⟩ := policy_receipt cached accepted
  obtain ⟨trace⟩ := Trace.of_accepted (root := root) metadata
    (fun _ site => site.supported (table.aligned catalog)) covered root.selected.accepted
  cases trace.syntax_or_boundary covered with
  | inl grammar => exact grammar
  | inr residual =>
    obtain ⟨boundary⟩ := residual
    exact False.elim (boundary.impossible metadata forms initializers arguments present)


theorem source_typing
    (certified : ∃ types context facts,
      Dynamic.BodyInstanceTypingCertificate (Program.ofChecked compiled.sourceProgram)
        (CallableCoercionMethodInstantiation.bodyInstance compiled.sourceProgram method)
        types context facts) :
    ∃ context final facts,
      StatementsHaveType (source cached) {returnType := cached.named.specialized.function.inferredBodyType}
        context cached.compilation.statements final facts ∧
      NodeOccurrencesUnique (source cached) ∧ LocalIdentityOwnership (source cached) := by
  obtain ⟨types, context, facts, typed⟩ := certified
  have sameSource : (CallableCoercionMethodInstantiation.bodyInstance compiled.sourceProgram method).source =
      source cached := by
    simp only [source, CallableIndexedNamedGeneration.source, cached.same,
      CallableCoercionMethodInstantiation.bodyInstance]
  have sameResult : (CallableCoercionMethodInstantiation.bodyInstance compiled.sourceProgram method).resultType =
      cached.named.specialized.function.inferredBodyType := by
    rw [cached.same]
    rfl
  have body := typed.typing.body_typed
  rw [sameSource, sameResult] at body
  obtain ⟨final, body, _roots, _complete⟩ := body
  change StatementsHaveType (source cached)
    {returnType := cached.named.specialized.function.inferredBodyType}
    context (statements (source cached)) final facts at body
  rw [AcceptedMethodBodyAdmission.roots cached] at body
  exact ⟨context, final, facts, body,
    sameSource ▸ typed.graph_closed.wellFormed.nodeOccurrencesUnique,
    sameSource ▸ typed.local_identity_ownership⟩

theorem of_certificate
    (certified : ∃ types context facts,
      Dynamic.BodyInstanceTypingCertificate (Program.ofChecked compiled.sourceProgram)
        (CallableCoercionMethodInstantiation.bodyInstance compiled.sourceProgram method)
        types context facts)
    (bodies : SelectedCompilationBodyTyping.Bodies compiled)
    (table : CallableIndexedOwnedPreparedOrdinarySyntaxTable.Table compiled)
    (receipt : BodyAt cached)
    (forms : DirectSource (source cached))
    (metadata : MetadataFor compiled.indexed cached.named (source cached) (DirectSite table.rows))
    (covered : ∀ id node, (source cached).lookupExpression? id = some node →
      ∀ callee arguments instantiation, node.form = .call callee arguments (.declaration instantiation) →
        DirectSite table.rows instantiation)
    {reached : ExpressionId → Prop}
    (reachedForms : ReachedForms (source cached) reached)
    (arguments : ReachedArguments (source cached) reached)
    (initializers : ∀ id, reached id → ¬ Nonempty (AcceptedContextualDirectReceipt.InitializerAt
      compiled.indexed (CallableIndexedNamedGeneration.context compiled.indexed cached.named) id))
    (children : ∀ child ∈ receipt.tree.children, reached child.expression)
    (complete : receipt.tree.complete cached.named.specialized.function.inferredBodyType = true)
    (monomorphic : ∀ binding ∈ receipt.tree.bindings, binding.binder.scheme.quantified = []) :
    Nonempty (SourceCertificate compiled cached.named table.rows) := by
  obtain ⟨context, final, facts, typed, unique, ownership⟩ := source_typing cached certified
  have binders := AcceptedNamedBodyBindings.of_monomorphic receipt.tree (read cached)
    unique ownership typed monomorphic
  have grammar : ∀ child ∈ receipt.tree.children,
      GeneralSyntax (source cached) child.expression (DirectSite table.rows) := by
    intro child member
    exact child_syntax cached table bodies metadata covered reachedForms arguments initializers
      child.accepted (children child member)
  have body := receipt.tree.scan_complete (read cached) complete unique ownership grammar binders typed
  rw [← AcceptedMethodBodyAdmission.roots cached] at body
  exact ⟨⟨forms, ⟨metadata, body⟩⟩⟩

theorem of_selection
    (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
    (selected : CallableCoercionBodyProvenance.Selection compiled.sourceProgram method)
    (parameters : selected.implementation.parameters.Nodup)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (SourceSemantics.Context.ofSignatures compiled.sourceProgram.signatures)
      method.specialized.parameterSubstitution)
    (bodies : SelectedCompilationBodyTyping.Bodies compiled)
    (table : CallableIndexedOwnedPreparedOrdinarySyntaxTable.Table compiled)
    (receipt : BodyAt cached)
    (forms : DirectSource (source cached))
    (metadata : MetadataFor compiled.indexed cached.named (source cached) (DirectSite table.rows))
    (covered : ∀ id node, (source cached).lookupExpression? id = some node →
      ∀ callee arguments instantiation, node.form = .call callee arguments (.declaration instantiation) →
        DirectSite table.rows instantiation)
    {reached : ExpressionId → Prop}
    (reachedForms : ReachedForms (source cached) reached)
    (arguments : ReachedArguments (source cached) reached)
    (initializers : ∀ id, reached id → ¬ Nonempty (AcceptedContextualDirectReceipt.InitializerAt
      compiled.indexed (CallableIndexedNamedGeneration.context compiled.indexed cached.named) id))
    (children : ∀ child ∈ receipt.tree.children, reached child.expression)
    (complete : receipt.tree.complete cached.named.specialized.function.inferredBodyType = true)
    (monomorphic : ∀ binding ∈ receipt.tree.bindings, binding.binder.scheme.quantified = []) :
    Nonempty (SourceCertificate compiled cached.named table.rows) := by
  obtain ⟨definition, member, identity, instantiated⟩ :=
    AcceptedMethodBodyAdmission.instantiates_of_selection checked selected parameters range
  obtain ⟨retained, retainedMember, retainedId, retainedBody⟩ := selected.retained checked
  have retainedValid := bodies.methods retained
    ⟨cached.index, cached.named, method, cached.selected, cached.same, selected,
      retainedMember, retainedId, retainedBody⟩
  have sameDefinition : definition = MethodDefinition.ofChecked retained :=
    StructuralSubstitution.eq_of_mem_of_mapped_nodup bodies.method_ids member
      (List.mem_map.mpr ⟨retained, retainedMember, rfl⟩)
      (identity.trans (retainedId.trans selected.methodId).symm)
  have valid : MethodDefinition.Valid compiled.sourceProgram.signatures definition :=
    sameDefinition ▸ retainedValid
  obtain ⟨types, context, facts, certificate⟩ := instantiated.certificate_of_valid bodies.signatures valid
  exact of_certificate cached ⟨types, context, facts, certificate.toBodyInstanceTypingCertificate⟩
    bodies table receipt forms metadata covered reachedForms arguments initializers children complete monomorphic

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationAcceptedMethods
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationAcceptedScopedFactories
/-! Flat original profiles close the actual scoped lambda body and its ordered
expression actions. The same derived scan issues both formation and closure
certificates without a caller-provided grammar or body completion premise. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationAcceptedScopedFactories
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (context)
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedNamedSyntaxAdmission (DirectSite)
open CallableIndexedOwnedPreparedStagedDirectCallCertificates (Supported)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)
open AcceptedScopedLambdaBodyReceipts (Produced)
open SelectedCompilationScopedFactorySourceCertificate (SourceCertificate Certificate)
open CallableIndexedOwnedPreparedScopedClosureAdmission (SourceBodyCertificate)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {row : SourceSpecialization.SpecializedFunction}
  (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
  {instantiation : DeclarationInstantiation}
  {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
  (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
  {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
  {directRows : List SourceSpecialization.SpecializedFunction} {directOnly allowIndices allowConstructors : Bool}

/-- Every expression proof comes from an actual child compiler action at its
minimum root budget and original lexical scope. -/
theorem Produced.scan (produced : Produced prepared header parameters result statements)
    (expressions : AcceptedCompilerExpressionProfile.Profile compiled.indexed prepared.named
      header.function.source directRows directOnly allowIndices allowConstructors)
    (bodyProfile : AcceptedCompilerBodySubsetProfile.Profile header.function.source expressions.ids statements result)
    (supported : ∀ instantiation, DirectSite directRows instantiation → Supported compiled.indexed.base.plan instantiation)
    (certified : SelectedCompilationNamedSourceTyping.Certified header) :
    ScopedSourceBodyAdmission.Scan header.function.source
      (fun id => GeneralSyntax header.function.source id (DirectSite directRows)) result true statements := by
  have readPolicy : (AcceptedContextualLambdaReceipt.bodyPolicy produced.action.root produced.action.fuel).readStatement =
      SourceCoreCompatibleDataExpressions.readStatement compiled.compatible.checked := rfl
  obtain ⟨closed, monomorphic, members⟩ := bodyProfile.facts produced.inner.tree readPolicy produced.ready
  have children : ∀ child ∈ produced.inner.tree.children,
      GeneralSyntax header.function.source child.expression (DirectSite directRows) := by
    intro child member
    obtain ⟨trace⟩ := AcceptedNamedExpressionFlow.Trace.of_accepted
      (root := produced.action.root) expressions.metadata supported expressions.covered child.accepted
    cases trace.syntax_or_boundary expressions.covered with
    | inl grammar => exact grammar
    | inr residual =>
      obtain ⟨boundary⟩ := residual
      exact False.elim (boundary.impossible_ordinary expressions.metadata expressions.compositeForms expressions.noInitializer
        expressions.ordinaryArguments expressions.ordinaryMetadata expressions.indexOperands expressions.constructorRanges (members child member))
  obtain ⟨inner, final, facts, typed⟩ := SelectedCompilationAcceptedFactories.inner_typing
    produced.actual.roots produced.actual.found produced.actual.form produced.action.head.found produced.form certified
  obtain ⟨_facts, certificate⟩ := certified
  have ownership : LocalIdentityOwnership header.function.source := by
    rw [header.frame.source]
    exact certificate.local_identity_ownership
  have binders := AcceptedNamedBodyBindings.of_monomorphic produced.inner.tree readPolicy
    header.unique ownership typed monomorphic
  exact produced.inner.tree.scan_complete readPolicy closed header.unique ownership children binders typed

private theorem origin_owner : ∃ signature ∈ compiled.sourceProgram.signatures.functions,
    prepared.named.specialized.function.typedBody.owner = signature.id := by
  obtain ⟨request, signature, generic, member, _genericMember, _resolved, accepted⟩ := prepared.origin
  have identities := RecursiveNamedSpecializationBodyFacts.identities accepted
  have fields := CallableCoercionBodyProvenance.specialization_fields accepted
  refine ⟨signature, member, ?_⟩
  rw [prepared.same, fields.1, SourceSpecialization.applyCheckedFunction_bodyOwner,
    identities.2.1, identities.1]

include aligned in
/-- Formation and later body admission share the same derived original scan. -/
theorem of_produced (produced : Produced prepared header parameters result statements)
    (expressions : AcceptedCompilerExpressionProfile.Profile compiled.indexed prepared.named
      header.function.source directRows directOnly allowIndices allowConstructors)
    (bodyProfile : AcceptedCompilerBodySubsetProfile.Profile header.function.source expressions.ids statements result)
    (supported : ∀ instantiation, DirectSite directRows instantiation → Supported compiled.indexed.base.plan instantiation)
    (certified : SelectedCompilationNamedSourceTyping.Certified header) :
    Nonempty (SourceCertificate compiled prepared.named header.function.source header.function.body) ∧
      Nonempty (SourceBodyCertificate compiled prepared.named directRows statements) := by
  have scan := Produced.scan prepared produced expressions bodyProfile supported certified
  let factory : SourceCertificate compiled prepared.named header.function.source header.function.body := {
    expression := produced.actual.expression
    terminal := produced.actual.terminal.terminal
    node := produced.action.head.node
    parameters := parameters
    result := result
    statements := statements
    reported := produced.reported
    found := produced.action.head.found
    form := produced.form
    owner := produced.action.head.owner
    requirements := produced.requirements
    coercions := produced.coercions
    ordinary := produced.ordinary
    read := produced.read
    scan := scan.map (fun _ _ => True.intro) }
  obtain ⟨signature, member, owner⟩ := origin_owner prepared
  have source := (CallableIndexedOwnedPreparedNamedSourceAdmissionTransport.header_data prepared aligned).1
  have typedScan := scan
  have metadata := expressions.metadata
  rw [source] at typedScan metadata
  exact ⟨⟨factory⟩, ⟨⟨result, typedScan, metadata, signature, member, owner⟩⟩⟩

include aligned in
/-- The accepted outer return identifies the literal lambda. Its actual scoped
body and expression receipts derive both certificate lanes internally. -/
theorem of_returning {outer : StatementId} {rest : List StatementId} {outerNode : StatementNode}
    {id : ExpressionId} {node : ExpressionNode}
    (roots : header.function.body = outer :: rest)
    (outerFound : header.function.source.lookupStatement? outer = some outerNode)
    (outerForm : outerNode.form = .returnStmt (some id))
    (found : header.function.source.lookupExpression? id = some node)
    (form : node.form = .lambda parameters result statements)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context compiled.indexed prepared.named).owner ∧ binding.initializer = id)) = none)
    (expressions : AcceptedCompilerExpressionProfile.Profile compiled.indexed prepared.named
      header.function.source directRows directOnly allowIndices allowConstructors)
    (bodyProfile : AcceptedCompilerBodySubsetProfile.Profile header.function.source expressions.ids statements result)
    (supported : ∀ instantiation, DirectSite directRows instantiation → Supported compiled.indexed.base.plan instantiation)
    (certified : SelectedCompilationNamedSourceTyping.Certified header) :
    Nonempty (SourceCertificate compiled prepared.named header.function.source header.function.body) ∧
      Nonempty (SourceBodyCertificate compiled prepared.named directRows statements) := by
  obtain ⟨produced⟩ := AcceptedScopedLambdaBodyReceipts.of_returning prepared aligned roots outerFound outerForm
    found form requirements coercions ordinary
  exact of_produced prepared aligned produced expressions bodyProfile supported certified

include aligned in
/-- Full cache identity transports the factory certificate to its original row. -/
theorem source_of_header {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : compiled.indexed.base.functions[index]? = some named)
    (same : named.specialized = row)
    (certificate : SourceCertificate compiled prepared.named header.function.source header.function.body) :
    Nonempty (Certificate compiled named) := by
  have namedEq := CallableIndexedOwnedPreparedNamedSourceAdmissionTransport.cached_named prepared selected same
  obtain ⟨source, body, _result⟩ :=
    CallableIndexedOwnedPreparedNamedSourceAdmissionTransport.header_data prepared aligned
  rw [source, body, namedEq] at certificate
  exact ⟨certificate⟩

/-- Full cache identity transports the inner certificate without replacing its source. -/
theorem closure_of_header {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : compiled.indexed.base.functions[index]? = some named)
    (same : named.specialized = row)
    (certificate : SourceBodyCertificate compiled prepared.named directRows statements) :
    Nonempty (SourceBodyCertificate compiled named directRows statements) := by
  have namedEq := CallableIndexedOwnedPreparedNamedSourceAdmissionTransport.cached_named prepared selected same
  rw [namedEq] at certificate
  exact ⟨certificate⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationAcceptedScopedFactories
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationInitializerRows
/-! The real initializer's ordered compiler receipts supply its indexed rows.
Candidate metadata and source origins come from the actual compiled catalog;
no body profile or future execution is required to create the same bundle. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationInitializerRows
open Core Frontend SourceInference TypeSystem SourceCoreLocalPolymorphism
open GeneralizedLocalInstanceCompilation (Inputs)
open DataPatternValues

variable (compiled : SourceCoreUnifiedCompilation.Compiled)
  {inputs : Inputs} {binding : Binding} {active : Substitution}
  {binder : Resolved.LocalId}
  (located : compiled.indexed.base.locals.binding inputs.current.owner binder = .ok binding)
  (initializer : inputs.initializer = binding.initializer)
  (represented : inputs.representation =
    (CallableIndexedNamedGeneration.representation compiled.indexed).atContext inputs.current.owner active)
  (program : inputs.program = compiled.indexed.base.sourceProgram)
  (locals : inputs.locals = compiled.indexed.base.locals)
  (native : inputs.native = compiled.indexed.base.callableContext)
  (plan : inputs.current.plan = compiled.indexed.base.plan)
  (globals : inputs.current.globals = compiled.indexed.base.globals)
  (administrativePrefix : inputs.current.administrativePrefix = 1)

include located initializer represented in
private theorem actual_packet {candidate : Instance} {raw : Core.Expr}
    (member : candidate ∈ binding.atContext active)
    (receipt : GeneralizedLocalInstanceCompilation.Receipt inputs candidate raw) :
    Nonempty (GeneralizedLocalLambdaCompilation.Packet inputs candidate raw) := by
  have metadata := (SelectedCompilationLocalMetadata.at_context compiled located member).2.2
  have origin := SelectedCompilationLocalOrigins.at_context compiled located member
  obtain ⟨_sourceOwner, _binderOwner, _initializerOwner, node, parameters, result, body,
      found, form, _sourceType, _functionType, _closed, _parameterType, _resultType⟩ := metadata
  have initial : candidate.origin.initializer = inputs.initializer := origin.2.2.2.trans initializer.symm
  rw [initial] at found
  have source := GeneralizedLocalLambdaEmissionFacts.Emission.source receipt.emission
  have reader : inputs.representation.expressions.readExpression =
      SourceCoreCompatibleDataExpressions.readExpression compiled.compatible.checked := by
    rw [represented]
    rfl
  exact GeneralizedLocalLambdaMetadata.packet_of_compatible receipt reader (source ▸ found) form

include located initializer represented program locals native plan globals administrativePrefix in
/-- Every actual row retains its own packet and full cumulative native key.
The order is the production mapM order, even for equal native function types. -/
theorem indexed_rows {candidates : List Instance} {closures : List Core.Expr}
    (members : ∀ candidate ∈ candidates, candidate ∈ binding.atContext active)
    (rows : ListRel (fun candidate raw => Nonempty
      (GeneralizedLocalInstanceCompilation.Receipt inputs candidate raw)) candidates closures) :
    GeneralizedLocalAcceptedInitializer.IndexedRows compiled.indexed inputs active candidates closures := by
  induction rows with
  | nil => exact .nil
  | @cons candidate raw rest remaining head tail ih =>
    have member := members candidate (by simp)
    obtain ⟨receipt⟩ := head
    obtain ⟨packet⟩ := actual_packet compiled located initializer represented member receipt
    have caller := (SelectedCompilationLocalOrigins.at_context compiled located member).1.symm
    obtain ⟨indexed⟩ := GeneralizedLocalLambdaGeneration.of_packet compiled.indexed packet active
      represented program locals native plan caller globals administrativePrefix
    let exactIndexed : GeneralizedLocalLambdaGeneration.Indexed compiled.indexed packet :=
      { indexed with lexical := active, represented := represented }
    exact .cons ⟨⟨packet, exactIndexed, rfl⟩⟩
      (ih (fun candidate member => members candidate (List.mem_cons_of_mem _ member)))

include located initializer represented program locals native plan globals administrativePrefix in
/-- A successful actual initializer and its literal compiler input fields
produce the existing full accepted-bundle receipt, including an empty bundle. -/
theorem of_receipt {lowered : SourceCoreBasic.LoweredExpr}
    (original : GeneralizedLocalInitializerCompilation.Receipt inputs binding active lowered) :
    Nonempty (GeneralizedLocalAcceptedInitializer.Receipt compiled.indexed inputs binding active lowered) := by
  refine ⟨⟨original, indexed_rows compiled located initializer represented program locals native plan globals
    administrativePrefix (fun _ member => member) original.rows, ?_, ?_⟩⟩
  · intro candidate member
    exact (SelectedCompilationLocalOrigins.at_context compiled located member).2.1
  · intro candidate member
    exact congrArg TypedBinder.id (SelectedCompilationLocalOrigins.at_context compiled located member).2.2.1

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationInitializerRows
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationCoercionInvocationBounds
/-! Each actual conversion call uses the shared marked method entry engine.
The saved native closure is identified by the reached full physical cache;
independent Source selection supplies its body and complete dictionary. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationCoercionInvocationBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedPreparedStagedCoercionAuthority (Port)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {project : SourceCoreEvidence.Projector} {compilation : SourceCoreFunctions.Context}
  {sourceCaller : SourceSpecialization.SpecializedFunction}
  {available : SourceTypedRuntime.RuntimeEvidenceEnvironment}
  {scope : SourceCoreBasic.Scope} {node : ExpressionNode}
  {policy : SourceCoreFunctions.CallablePolicy}
  {input output : SourceCoreBasic.LoweredExpr} {coercion : SourceInference.CoercionStep}
  {call : CallableCoercionSpine.Call}
  (step : CallableCoercionSpine.Step compiled.sourceProgram project compilation sourceCaller available
    scope node policy input coercion output call)
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {stages : Staging.Recursive.Registry}
  (port : Port step context invocation.evidence stages)
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry} (faults : RecursiveStageMeaning.FaultRep)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions

/-- A strict Source body callback at an authentic reached argument state. -/
def SourceBodies (budget : Nat) : Prop :=
  ∀ {mapping world heap store callerScope canonical administrative arguments payloads}
    (caller : State headers keys ⟨callerScope, mapping, world, heap, store, canonical⟩)
    (installed : CallablePreparedMethodRuntimeMeaning.Installed port.principal.cached.compilation
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (sourceBody := port.principal.sourceBody) (administrative := administrative)
      functions mapping world heap store canonical),
    CallableIndexedParameterMeaning.Arguments model mapping world port.principal.named.inputs arguments payloads →
    Dynamic.HeapWellTyped port.principal.sourceFunction.context heap →
    Dynamic.ValuesHaveTypes port.principal.sourceFunction.context heap arguments port.sourceAt.types →
    CallableIndexedOwnedIndirectExpressionHeads.StableRows caller →
    ∀ {child}, stages.Closure port.principal.sourceFunction child →
    SelectedCompilationMethodInvocationBounds.SourceContinuation
      (program := Program.ofChecked compiled.sourceProgram) (registry := receiving)
      (owner := owner) (caller := caller) (arguments := arguments) (payloads := payloads)
      (stages := stages) (child := child) (faults := faults)
      port.principal.cached.compilation port.sourceAt functions installed budget

/-- The native counterpart uses the same independently typed argument heap. -/
def NativeBodies (budget : Nat) : Prop :=
  ∀ {mapping world heap store callerScope canonical administrative arguments payloads}
    (caller : State headers keys ⟨callerScope, mapping, world, heap, store, canonical⟩)
    (installed : CallablePreparedMethodRuntimeMeaning.Installed port.principal.cached.compilation
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (sourceBody := port.principal.sourceBody) (administrative := administrative)
      functions mapping world heap store canonical),
    CallableIndexedParameterMeaning.Arguments model mapping world port.principal.named.inputs arguments payloads →
    Dynamic.HeapWellTyped port.principal.sourceFunction.context heap →
    Dynamic.ValuesHaveTypes port.principal.sourceFunction.context heap arguments port.sourceAt.types →
    CallableIndexedOwnedIndirectExpressionHeads.StableRows caller →
    ∀ {child}, stages.Closure port.principal.sourceFunction child →
    SelectedCompilationMethodInvocationBounds.NativeContinuation
      (program := Program.ofChecked compiled.sourceProgram) (registry := receiving)
      (owner := owner) (caller := caller) (arguments := arguments) (payloads := payloads)
      (stages := stages) (child := child) (faults := faults)
      port.principal.cached.compilation port.sourceAt functions installed budget

theorem represented_arguments {mapping : LocationMap} {world : StoreTyping}
    {source : Dynamic.Value} {value : Value}
    (represented : ValueRep compiled.compatible.checked receiving functions mapping world
      coercion.source source value call.signature.parameterType) :
    CallableIndexedParameterMeaning.Arguments model mapping world port.principal.named.inputs [source] [value] := by
  have row : DataExpressionSequence.Values model mapping world [coercion.source]
      [call.signature.parameterType] [source] [value] := .cons represented .nil
  apply CallableIndexedOwnedStoredArgumentAlignment.arguments_of_bundles port.principal.named.inputs row
  · have lengths := congrArg List.length port.parameters
    simpa only [List.length_map, List.length_cons, List.length_nil] using lengths.symm
  · rw [port.parameters]
  · change call.signature.parameterType = _
    rw [← port.signature]
    exact port.sourceAt.parameterType

/-- Reached Source input typing is transported by the selected method's genuine
closed body certificate, keeping its complete dictionary and raw singleton row. -/
theorem source_arguments {source : TypedSource}
    (certified : ∃ facts, Dynamic.BodyInstanceTypingCertificate (Program.ofChecked compiled.sourceProgram)
    port.principal.sourceBody port.sourceAt.types port.sourceAt.context facts)
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
    {heap : Dynamic.Heap} {value : Dynamic.Value}
    (heapTyped : Dynamic.HeapWellTyped context heap)
    (valueTyped : Dynamic.ValueHasType context heap value coercion.source) :
    Dynamic.HeapWellTyped port.principal.sourceFunction.context heap ∧
      Dynamic.ValuesHaveTypes port.principal.sourceFunction.context heap [value] port.sourceAt.types := by
  obtain ⟨facts, certificate⟩ := certified
  have signatures := certificate.signatures_eq.trans runtime.signatures.symm
  have bodyHeap := heapTyped.transportClosed signatures runtime.closed certificate.type_parameters_empty
    runtime.variables_closed certificate.residual_type_variables_open
  have bodyValue := valueTyped.transportClosed signatures runtime.closed certificate.type_parameters_empty
    runtime.variables_closed certificate.residual_type_variables_open
  have bodyArguments := Dynamic.ValuesHaveTypes.cons bodyValue Dynamic.ValuesHaveTypes.nil
  have row := port.sourceAt.extended.bodyTypes_eq
  rw [port.sourceAt.parameters, List.map_map] at row
  change port.principal.named.inputs.map (fun binding => binding.1.scheme.body) = port.sourceAt.types at row
  rw [port.parameters] at row
  exact ⟨port.principal.source_frame.context.symm ▸ bodyHeap,
    port.principal.source_frame.context.symm ▸ (row ▸ bodyArguments)⟩

theorem result_at_value {source : TypedSource}
    (certified : ∃ facts, Dynamic.BodyInstanceTypingCertificate (Program.ofChecked compiled.sourceProgram)
      port.principal.sourceBody port.sourceAt.types port.sourceAt.context facts)
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
    {before after : Dynamic.Heap} {value : Dynamic.Value}
    (preserved : Dynamic.ExpressionEvaluationPreserved port.principal.sourceBody.context
      before after value coercion.target) :
    Dynamic.ExpressionEvaluationPreserved context before after value coercion.target := by
  obtain ⟨facts, certificate⟩ := certified
  have signatures := runtime.signatures.trans certificate.signatures_eq.symm
  exact ⟨preserved.value_typed.transportClosed signatures
      certificate.type_parameters_empty runtime.closed
      certificate.type_variables_empty runtime.residual_variables_open,
    preserved.heap_typed.transportClosed signatures
      certificate.type_parameters_empty runtime.closed
      certificate.type_variables_empty runtime.residual_variables_open,
    preserved.heap_extends⟩

private theorem capture_read {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap}
    {store : Store} {canonical : Environment}
    (capture : CallableIndexedOwnedMethodPhysicalCaptures.Capture port.principal.cached port.principal.dictionary
      functions mapping world heap store canonical)
    (authority : CallableIndexedOwnedPhysicalGlobals.Authority compiled mapping store) :
    store.read? (CallableIndexedOwnedPhysicalGlobals.location compiled port.principal.cached.index) = some (.inRight .unit
      (.closure port.principal.named.signature.parameterType (LanguageResult.resultType port.principal.named.signature.resultType)
        (port.principal.cached.compilation.output.rename capture.installed.embedding.lift) capture.installed.captured)) := by
  have cachedCode : compiled.indexed.secondPass.closures[port.principal.cached.index]? = some
      (.lambda port.principal.named.signature.parameterType (LanguageResult.resultType port.principal.named.signature.resultType)
        port.principal.cached.compilation.output) := by
    simpa only [port.principal.cached.compilation.emitted] using port.principal.cached.cached
  simpa only [capture.embedding_eq, capture.captured_eq] using (authority.cached cachedCode).2

variable {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {canonical actual : Environment} {ξ : Renaming}
  (pool : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
  (ownerFrame : owner.key.frameLocation = 0)
  (physical : CallableIndexedOwnedPhysicalGlobals.Authority compiled mapping store)
  (slots : CallableIndexedOwnedPhysicalGlobals.Slots compiled compilation.administrativePrefix scope canonical)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions mapping world before store)
  {source : Dynamic.Value} {value : Value}
  (represented : ValueRep compiled.compatible.checked receiving functions mapping world coercion.source source value call.signature.parameterType)
  (headerHeap : Dynamic.HeapWellTyped port.principal.sourceFunction.context before)
  (headerArguments : Dynamic.ValuesHaveTypes port.principal.sourceFunction.context before [source] port.sourceAt.types)
  (stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows pool)
  (certified : ∃ facts, Dynamic.BodyInstanceTypingCertificate (Program.ofChecked compiled.sourceProgram)
    port.principal.sourceBody port.sourceAt.types port.sourceAt.context facts)

include ownerFrame physical slots agrees heaps represented headerHeap headerArguments stable certified in
theorem preserves (budget : Nat)
    (bodyMeaning : SourceBodies (headers := headers) (receiving := receiving) step port owner functions faults budget)
    (ledger : context.solvedRequirements = sourceCaller.function.solvedRequirements)
    {size : Nat} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.CoercionStep (Program.ofChecked compiled.sourceProgram) stages size
      invocation context before coercion source outcome after)
    (within : size ≤ budget) :
    ∃ result finalStore finalMap finalWorld,
      CallableCoercionSpine.Invoke actual compilation.internalReason (call.rename ξ) store (.inRight .word value) result finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld coercion.target call.signature.resultType faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition (protocol headers keys) pool
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ ∧
      ∀ value, outcome = .value value →
        Dynamic.ExpressionEvaluationPreserved port.principal.sourceBody.context before after value coercion.target := by
  obtain ⟨bodySize, bodyEnvironment, bound, finalContext, bodyOutcome, child, selected, allocated, bodyTrace, matched, strict⟩ :=
    CallableIndexedOwnedPreparedStagedCoercionSourceArguments.body step port ledger trace
  have parameters := represented_arguments step port functions represented
  obtain ⟨capture⟩ := SelectedCompilationMethodPhysicalCaptures.of_certificate
    port.principal.cached port.principal.dictionary functions owner pool ownerFrame
    physical heaps.runtime_hasTypes slots port.selected (by obtain ⟨facts, typed⟩ := certified; exact ⟨_, _, facts, typed⟩)
  have capturedSlots : CallableIndexedOwnedPhysicalGlobals.Slots compiled 0 [] capture.installed.canonical := by
    rw [capture.canonical_eq]
    exact CallableIndexedOwnedPhysicalGlobals.environment_slots compiled
  obtain ⟨result, finalStore, finalMap, finalWorld, evaluated, resultRep, finalHeaps, maps, worlds, frame, metadata, finalState, preserved⟩ :=
    SelectedCompilationMethodInvocationBounds.preserves
      port.principal.cached.compilation port.sourceAt functions capture.installed parameters owner pool
      (capture.frame_eq.trans ownerFrame.symm) heaps physical capturedSlots budget
      (bodyMeaning pool capture.installed parameters headerHeap headerArguments stable selected)
      allocated bodyTrace matched (Nat.lt_of_lt_of_le strict within)
  have reference := agrees (slots _ _ (CallableIndexedPreparedInventories.cached_global_at compiled port.principal.cached.selected))
  have read := capture_read step port functions capture physical
  refine ⟨result, finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps, maps, worlds, frame, metadata, finalState, ?_⟩
  · apply CallableCoercionSpine.Invoke.applied (location := CallableIndexedOwnedPhysicalGlobals.location compiled port.principal.cached.index)
      (body := port.principal.cached.compilation.output.rename capture.installed.embedding.lift)
      (captured := capture.installed.captured)
    · simpa only [CallableCoercionSpine.Call.rename, step.location, ← port.slot] using reference
    · exact read
    · simpa only [DataPatternValues.packValues] using evaluated
  · simpa only [port.result, port.signature] using resultRep
  · intro value same
    simpa only [port.result] using preserved value same

include ownerFrame physical slots agrees heaps represented headerHeap headerArguments stable certified in
theorem reflects (budget : Nat)
    (bodyMeaning : NativeBodies (headers := headers) (receiving := receiving) step port owner functions faults budget)
    {result : Value} {finalStore : Store}
    (completed : CallableCoercionSpine.InvokeSized budget actual compilation.internalReason (call.rename ξ)
      store (.inRight .word value) result finalStore) :
    ∃ size outcome after finalMap finalWorld,
      Staging.Recursive.Size.CoercionStep (Program.ofChecked compiled.sourceProgram) stages size
        invocation context before coercion source outcome after ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld coercion.target call.signature.resultType faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition (protocol headers keys) pool
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ ∧
      ∀ value, outcome = .value value →
        Dynamic.ExpressionEvaluationPreserved port.principal.sourceBody.context before after value coercion.target := by
  have parameters := represented_arguments step port functions represented
  obtain ⟨capture⟩ := SelectedCompilationMethodPhysicalCaptures.of_certificate
    port.principal.cached port.principal.dictionary functions owner pool ownerFrame
    physical heaps.runtime_hasTypes slots port.selected (by obtain ⟨facts, typed⟩ := certified; exact ⟨_, _, facts, typed⟩)
  have capturedSlots : CallableIndexedOwnedPhysicalGlobals.Slots compiled 0 [] capture.installed.canonical := by
    rw [capture.canonical_eq]
    exact CallableIndexedOwnedPhysicalGlobals.environment_slots compiled
  have reference := agrees (slots _ _ (CallableIndexedPreparedInventories.cached_global_at compiled port.principal.cached.selected))
  have referenceAt : actual[(call.rename ξ).index]? = some
      (.cellRef (OptionalCell.cellType port.principal.named.signature.functionType)
        (CallableIndexedOwnedPhysicalGlobals.location compiled port.principal.cached.index)) := by
    simpa only [CallableCoercionSpine.Call.rename, step.location, ← port.slot] using reference
  have read := capture_read step port functions capture physical
  cases completed with
  | absent reference actualRead =>
      cases Option.some.inj (reference.symm.trans referenceAt)
      cases Option.some.inj (actualRead.symm.trans read)
  | applied reference actualRead evaluation smaller =>
      cases Option.some.inj (reference.symm.trans referenceAt)
      cases Option.some.inj (actualRead.symm.trans read)
      obtain ⟨bodySize, bodyEnvironment, bound, finalContext, bodyOutcome, outcome, after, finalMap, finalWorld,
          allocated, bodyTrace, matched, resultRep, finalHeaps, maps, worlds, frame, metadata, finalState, preserved⟩ :=
        SelectedCompilationMethodInvocationBounds.reflects
          port.principal.cached.compilation port.sourceAt functions capture.installed parameters owner pool
          (capture.frame_eq.trans ownerFrame.symm) heaps physical capturedSlots budget
          (bodyMeaning pool capture.installed parameters headerHeap headerArguments stable port.staged)
          (by simpa only [DataPatternValues.packValues] using evaluation) (Nat.le_of_lt smaller)
      obtain ⟨size, trace⟩ := CallableIndexedOwnedPreparedStagedCoercionSourceArguments.applied step port
        port.staged allocated bodyTrace matched
      refine ⟨size, outcome, after, finalMap, finalWorld, trace,
        by simpa only [port.result, port.signature] using resultRep,
        finalHeaps, maps, worlds, frame, metadata, finalState, ?_⟩
      intro value same
      simpa only [port.result] using preserved value same

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationCoercionInvocationBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationCoercionPathBounds
/-! Ordered conversions preserve the exact reached pool, heap and physical
cache between calls. Each method continuation receives the original strict
budget; path recursion only composes already justified single steps. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationCoercionPathBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedPreparedStagedCoercionChain (Chain)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {project : SourceCoreEvidence.Projector} {compilation : SourceCoreFunctions.Context}
  {caller : SourceSpecialization.SpecializedFunction}
  {available : SourceTypedRuntime.RuntimeEvidenceEnvironment}
  {scope : SourceCoreBasic.Scope} {node : ExpressionNode}
  {policy : SourceCoreFunctions.CallablePolicy}
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {stages : Staging.Recursive.Registry}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry} (faults : RecursiveStageMeaning.FaultRep)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions

/-- Body continuations are supplied by the shared numerical induction. -/
def SourceBodies {source target input steps output calls}
    (chain : Chain compiled project compilation caller available scope node policy context invocation stages
      source target input steps output calls) (budget : Nat) : Prop :=
  match chain with
  | .nil => True
  | .cons step port _ tail =>
      ((∃ facts, Dynamic.BodyInstanceTypingCertificate (Program.ofChecked compiled.sourceProgram)
          port.principal.sourceBody port.sourceAt.types port.sourceAt.context facts) ∧
        SelectedCompilationCoercionInvocationBounds.SourceBodies (headers := headers) (receiving := receiving) step port owner functions faults budget) ∧
        SourceBodies tail budget

def NativeBodies {source target input steps output calls}
    (chain : Chain compiled project compilation caller available scope node policy context invocation stages
      source target input steps output calls) (budget : Nat) : Prop :=
  match chain with
  | .nil => True
  | .cons step port _ tail =>
      ((∃ facts, Dynamic.BodyInstanceTypingCertificate (Program.ofChecked compiled.sourceProgram)
          port.principal.sourceBody port.sourceAt.types port.sourceAt.context facts) ∧
        SelectedCompilationCoercionInvocationBounds.NativeBodies (headers := headers) (receiving := receiving) step port owner functions faults budget) ∧
        NativeBodies tail budget

variable {source target : TypeSystem.Ty} {input output : SourceCoreBasic.LoweredExpr}
  {steps : List SourceInference.CoercionStep} {calls : List CallableCoercionSpine.Call}
  (chain : Chain compiled project compilation caller available scope node policy context invocation stages
    source target input steps output calls)
  (ownerFrame : owner.key.frameLocation = 0)
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
  (ledger : context.solvedRequirements = caller.function.solvedRequirements)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {canonical actual : Environment} {ξ : Renaming}
  (pool : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
  (physical : CallableIndexedOwnedPhysicalGlobals.Authority compiled mapping store)
  (slots : CallableIndexedOwnedPhysicalGlobals.Slots compiled compilation.administrativePrefix scope canonical)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions mapping world before store)
  {sourceValue : Dynamic.Value} {nativeValue : Value}
  (represented : ValueRep compiled.compatible.checked receiving functions mapping world source sourceValue nativeValue input.type)
  (heapTyped : Dynamic.HeapWellTyped context before)
  (valueTyped : Dynamic.ValueHasType context before sourceValue source)
  (stable : StableRows pool)

include ownerFrame runtime ledger physical slots agrees heaps represented heapTyped valueTyped stable in
theorem preserves (budget : Nat)
    (bodyMeaning : SourceBodies (headers := headers) (receiving := receiving) owner functions faults chain budget)
    {size : Nat} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.CoercionPath (Program.ofChecked compiled.sourceProgram) stages size
      invocation context before steps sourceValue outcome after)
    (within : size ≤ budget) :
    ∃ result finalStore finalMap finalWorld,
      CallableCoercionSpine.Runs actual compilation.internalReason store (.inRight .word nativeValue)
        (calls.map (CallableCoercionSpine.Call.rename ξ)) result finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld target output.type faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition (protocol headers keys) pool
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ ∧
      ∀ value, outcome = .value value →
        Dynamic.ExpressionEvaluationPreserved context before after value target := by
  induction chain generalizing mapping world before store sourceValue nativeValue size outcome after with
  | nil =>
      cases trace
      refine ⟨_, store, mapping, world, .nil, .value represented, heaps,
        LocationMap.Extends.refl _, WorldExtends.refl _, AdministrativePreserved.refl _ _,
        Dynamic.HeapMetadataExtend.refl _, ⟨pool, Relates.refl pool⟩, ?_⟩
      intro value same
      cases same
      exact ⟨valueTyped, heapTyped, Dynamic.HeapMetadataExtend.refl _⟩
  | @cons coercion target input middle output rest call calls step port valid tail ih =>
      obtain ⟨headerHeap, headerArguments⟩ := SelectedCompilationCoercionInvocationBounds.source_arguments step port bodyMeaning.1.1 runtime heapTyped valueTyped
      have inputRep : ValueRep compiled.compatible.checked receiving functions mapping world coercion.source
          sourceValue nativeValue call.signature.parameterType := step.inputType.symm ▸ represented
      cases trace with
      | coercionsCons head path =>
          obtain ⟨converted, middleStore, middleMap, middleWorld, invoked, resultRep, middleHeaps,
              maps, worlds, frame, metadata, ⟨reached, related⟩, headPreserved⟩ :=
            SelectedCompilationCoercionInvocationBounds.preserves step port owner functions faults pool ownerFrame physical slots agrees heaps
              inputRep headerHeap headerArguments stable bodyMeaning.1.1 budget bodyMeaning.1.2 ledger head
              (Nat.le_trans (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) within)
          cases resultRep with
          | value convertedRep =>
              have converted := SelectedCompilationCoercionInvocationBounds.result_at_value
                step port bodyMeaning.1.1 runtime (headPreserved _ rfl)
              have convertedTyped := converted.value_typed
              have middleTyped := converted.heap_typed
              have middleType : middle.type = call.signature.resultType := by rw [step.emitted]
              have nextRep := convertedRep
              rw [← middleType] at nextRep
              obtain ⟨result, finalStore, finalMap, finalWorld, remaining, resultRep, finalHeaps,
                  tailMaps, tailWorlds, tailFrame, tailMetadata, ⟨returned, tailRelated⟩, tailPreserved⟩ :=
                ih reached (physical.extend frame) middleHeaps nextRep middleTyped convertedTyped
                  (StableRows.after_administrative pool reached stable frame) bodyMeaning.2 path
                  (Nat.le_trans (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) within)
              refine ⟨result, finalStore, finalMap, finalWorld, .cons invoked remaining,
                resultRep, finalHeaps, maps.trans tailMaps, worlds.trans tailWorlds,
                frame.trans tailFrame, metadata.trans tailMetadata, ⟨returned, related.trans tailRelated⟩, ?_⟩
              intro value same
              have preserved := tailPreserved value same
              exact ⟨preserved.value_typed, preserved.heap_typed, metadata.trans preserved.heap_extends⟩
      | coercionsFault head =>
          obtain ⟨converted, finalStore, finalMap, finalWorld, invoked, resultRep, finalHeaps,
              maps, worlds, frame, metadata, ⟨reached, related⟩, headPreserved⟩ :=
            SelectedCompilationCoercionInvocationBounds.preserves step port owner functions faults pool ownerFrame physical slots agrees heaps
              inputRep headerHeap headerArguments stable bodyMeaning.1.1 budget bodyMeaning.1.2 ledger head
              (Nat.le_trans (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) within)
          cases resultRep with
          | fault matched =>
              have finalType : CallableCoercionSpine.finalType call.signature.resultType
                  (calls.map (CallableCoercionSpine.Call.rename ξ)) = output.type := by
                simpa only [step.emitted] using tail.final_type ξ
              refine ⟨_, finalStore, finalMap, finalWorld, .cons invoked ?_, .fault matched,
                finalHeaps, maps, worlds, frame, metadata, ⟨reached, related⟩, ?_⟩
              · simpa only [finalType] using CallableCoercionSpine.Runs.failure actual compilation.internalReason
                  finalStore call.signature.resultType _ (calls.map (CallableCoercionSpine.Call.rename ξ))
              · intro value same
                cases same

private theorem failed_runs {budget : Nat} {environment : Environment} {reason : Word}
    {store finalStore : Store} {tag : Ty} {payload result : Value} {calls : List CallableCoercionSpine.Call}
    (trace : CallableCoercionSpine.RunsFor (CallableCoercionSpine.InvokeSized budget environment reason)
      store (.inLeft tag payload) calls result finalStore) :
    result = .inLeft (CallableCoercionSpine.finalType tag calls) payload ∧ finalStore = store := by
  generalize original : Value.inLeft tag payload = input at trace
  induction trace generalizing tag with
  | nil => cases original; exact ⟨rfl, rfl⟩
  | cons head tail ih =>
      cases original
      cases head with
      | skipped => exact ih rfl

include ownerFrame runtime physical slots agrees heaps represented heapTyped valueTyped stable in
theorem reflects (budget : Nat)
    (bodyMeaning : NativeBodies (headers := headers) (receiving := receiving) owner functions faults chain budget)
    {result : Value} {finalStore : Store}
    (completed : CallableCoercionSpine.RunsFor (CallableCoercionSpine.InvokeSized budget actual compilation.internalReason)
      store (.inRight .word nativeValue) (calls.map (CallableCoercionSpine.Call.rename ξ)) result finalStore) :
    ∃ size outcome after finalMap finalWorld,
      Staging.Recursive.Size.CoercionPath (Program.ofChecked compiled.sourceProgram) stages size
        invocation context before steps sourceValue outcome after ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld target output.type faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition (protocol headers keys) pool
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ ∧
      ∀ value, outcome = .value value →
        Dynamic.ExpressionEvaluationPreserved context before after value target := by
  induction chain generalizing mapping world before store sourceValue nativeValue result finalStore with
  | nil =>
      cases completed
      refine ⟨_, .value sourceValue, before, mapping, world, .coercionsNil, .value represented, heaps,
        LocationMap.Extends.refl _, WorldExtends.refl _, AdministrativePreserved.refl _ _,
        Dynamic.HeapMetadataExtend.refl _, ⟨pool, Relates.refl pool⟩, ?_⟩
      intro value same
      cases same
      exact ⟨valueTyped, heapTyped, Dynamic.HeapMetadataExtend.refl _⟩
  | @cons coercion target input middle output rest call calls step port valid tail ih =>
      obtain ⟨headerHeap, headerArguments⟩ := SelectedCompilationCoercionInvocationBounds.source_arguments
        step port bodyMeaning.1.1 runtime heapTyped valueTyped
      have inputRep : ValueRep compiled.compatible.checked receiving functions mapping world coercion.source
          sourceValue nativeValue call.signature.parameterType := step.inputType.symm ▸ represented
      cases completed with
      | cons head remaining =>
          obtain ⟨sourceSize, outcome, middleHeap, middleMap, middleWorld, trace, resultRep, middleHeaps,
              maps, worlds, frame, metadata, ⟨reached, related⟩, headPreserved⟩ :=
            SelectedCompilationCoercionInvocationBounds.reflects
              step port owner functions faults pool ownerFrame physical slots agrees heaps
              inputRep headerHeap headerArguments stable bodyMeaning.1.1 budget bodyMeaning.1.2 head
          cases resultRep with
          | value convertedRep =>
              have converted := SelectedCompilationCoercionInvocationBounds.result_at_value
                step port bodyMeaning.1.1 runtime (headPreserved _ rfl)
              have convertedTyped := converted.value_typed
              have middleTyped := converted.heap_typed
              have middleType : middle.type = call.signature.resultType := by rw [step.emitted]
              have nextRep := convertedRep
              rw [← middleType] at nextRep
              obtain ⟨tailSize, outcome, after, finalMap, finalWorld, tailTrace, finalRep, finalHeaps,
                  tailMaps, tailWorlds, tailFrame, tailMetadata, ⟨returned, tailRelated⟩, tailPreserved⟩ :=
                ih reached (physical.extend frame) middleHeaps nextRep middleTyped convertedTyped
                  (StableRows.after_administrative pool reached stable frame) bodyMeaning.2 remaining
              refine ⟨_, outcome, after, finalMap, finalWorld, .coercionsCons trace tailTrace,
                finalRep, finalHeaps, maps.trans tailMaps, worlds.trans tailWorlds,
                frame.trans tailFrame, metadata.trans tailMetadata, ⟨returned, related.trans tailRelated⟩, ?_⟩
              intro value same
              have preserved := tailPreserved value same
              exact ⟨preserved.value_typed, preserved.heap_typed, metadata.trans preserved.heap_extends⟩
          | fault matched =>
              have finalType : CallableCoercionSpine.finalType call.signature.resultType
                  (calls.map (CallableCoercionSpine.Call.rename ξ)) = output.type := by
                simpa only [step.emitted] using tail.final_type ξ
              obtain ⟨sameResult, rfl⟩ := failed_runs remaining
              rw [finalType] at sameResult
              subst result
              refine ⟨_, _, middleHeap, middleMap, middleWorld, .coercionsFault trace, .fault matched,
                middleHeaps, maps, worlds, frame, metadata, ⟨reached, related⟩, ?_⟩
              intro value same
              cases same

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationCoercionPathBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationCoercedDirectExpressionBounds
/-! Original direct-call forms and their authentic ordered conversions compose
at the same reached physical state. Both internal body continuations use one
budget; the original staged trace supplies the final Source admission. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationCoercedDirectExpressionBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open SelectedCompilationPhysicalRawDirectBounds (RawPreservesAt RawReflectsAt)
open CallableIndexedOwnedPreparedStagedCoercionChain (Chain)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {project : SourceCoreEvidence.Projector} {caller : SourceSpecialization.SpecializedFunction}
  {lowerChild : SourceCoreEvidence.Child} {fuel : Nat} {callables : SourceCoreFunctions.CallablePolicy}
  {compilation : SourceCoreFunctions.Context} {scope : SourceCoreLocalCell.Scope}
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {instantiation : DeclarationInstantiation}
  {reasonAt : ExpressionId → Word} {output : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
  (receipt : CallableCoercionExpressionCertificates.Direct compiled.sourceProgram project caller compilation
    lowerChild fuel invocation.source scope id callee ids instantiation reasonAt callables node output)
  (callerBridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun index => CallableIndexedOwnedExpressionHeads.Globals (headers := headers)
      owner compilation.administrativePrefix index.scope index.canonical) callerProtocol)
  (physical : ∀ {index}, callerProtocol.State index →
    CallableIndexedOwnedPhysicalGlobals.Authority compiled index.mapping index.store)
  (slots : ∀ {index}, callerProtocol.State index →
    CallableIndexedOwnedPhysicalGlobals.Slots compiled compilation.administrativePrefix index.scope index.canonical)
  (ownerFrame : owner.key.frameLocation = 0)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry} (faults : RecursiveStageMeaning.FaultRep)
  {stages : Staging.Recursive.Registry} {calls : List CallableCoercionSpine.Call}
  (chain : Chain compiled project compilation caller receipt.available scope node callables context invocation stages
    node.rawType node.type receipt.operand node.coercions output calls)
  (nonempty : node.coercions ≠ [])
  (unique : NodeOccurrencesUnique invocation.source)
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
  (ledger : context.solvedRequirements = caller.function.solvedRequirements)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions

variable (typed : ExpressionHasType invocation.source context id node.type)
  {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap} {store : Store} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) mapping world administrativeContext scope
    environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission callerBridge.forgetSlots context initial)

include physical slots ownerFrame chain nonempty unique runtime ledger typed environments heaps locals agrees actualTyped admitted in
theorem preserves (budget : Nat)
    (rawMeaning : ∀ size, size ≤ budget → RawPreservesAt (context := context) (receiving := receiving) owner receipt callerBridge functions faults stages size)
    (bodyMeaning : SelectedCompilationCoercionPathBounds.SourceBodies
      (headers := headers) (receiving := receiving) owner functions faults chain budget)
    {size : Nat} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages size
      invocation context environment before id outcome after) (within : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (output.expression.rename ξ) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld node.type output.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ PostAdmission callerBridge.forgetSlots context node.type outcome reached := by
  rcases CallableIndexedOwnedPreparedStagedCoercedExpressionSource.ordinary_branches receipt.found unique nonempty
      (by intro name binder impossible; rw [receipt.form] at impossible; cases impossible) trace with
    ⟨rawSize, pathSize, source, middle, sameSize, rawTrace, pathTrace⟩ |
    ⟨rawSize, failure, sameSize, outcomeEq, rawTrace⟩
  · have rawLess : rawSize < size := by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp)
    have pathLess : pathSize < size := by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp)
    have rawWithin : rawSize ≤ budget := Nat.le_trans (Nat.le_of_lt rawLess) within
    have pathWithin : pathSize ≤ budget := Nat.le_trans (Nat.le_of_lt pathLess) within
    obtain ⟨native, middleStore, middleMap, middleWorld, evaluated, represented, middleHeaps,
        maps, worlds, frame, metadata, middleState, related, rawPost⟩ :=
      rawMeaning rawSize rawWithin typed environments heaps locals agrees actualTyped initial admitted rawTrace
    cases represented with
    | value valueRep =>
      have valueTyped := rawPost.at_value.1
      have middleTyped := rawPost.at_value.2.heap
      obtain ⟨value, finalStore, finalMap, finalWorld, runs, result, finalHeaps,
          tailMaps, tailWorlds, tailFrame, tailMetadata, ⟨finalPool, tailRelated⟩, preserved⟩ :=
        SelectedCompilationCoercionPathBounds.preserves owner functions faults chain ownerFrame
          runtime ledger (callerBridge.pool middleState) (physical middleState) (slots middleState)
          agrees middleHeaps valueRep middleTyped valueTyped
          (CallableIndexedOwnedIndirectExpressionHeads.StableRows.after_administrative
            (callerBridge.pool initial) (callerBridge.pool middleState) admitted.rows frame)
          budget bodyMeaning pathTrace pathWithin
      obtain ⟨returned, _samePool, returnedRelated⟩ := callerBridge.restore middleState finalPool
        tailMaps tailWorlds tailFrame tailMetadata tailRelated
      refine ⟨value, finalStore, finalMap, finalWorld, ?_, result, finalHeaps,
        maps.trans tailMaps, worlds.trans tailWorlds, frame.trans tailFrame, metadata.trans tailMetadata,
        returned, callerProtocol.trans related returnedRelated, ?_⟩
      · exact (chain.spine.renamed_completed_iff ξ).mpr ⟨_, _, evaluated, runs⟩
      · exact after_expression_sized_of_preserved initial returned admitted trace (fun value same => ⟨(preserved value same).value_typed, (preserved value same).heap_typed, metadata.trans (preserved value same).heap_extends⟩)
          (frame.trans tailFrame)
  · subst outcome
    have rawLess : rawSize < size := by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp)
    have rawWithin : rawSize ≤ budget := Nat.le_trans (Nat.le_of_lt rawLess) within
    obtain ⟨native, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
        maps, worlds, frame, metadata, reached, related, rawPost⟩ :=
      rawMeaning rawSize rawWithin typed environments heaps locals agrees actualTyped initial admitted rawTrace
    cases represented with
    | @fault _ token matched =>
      have runs := CallableCoercionSpine.Runs.failure actual compilation.internalReason finalStore
        receipt.operand.type (.word token) (calls.map (CallableCoercionSpine.Call.rename ξ))
      rw [chain.final_type ξ] at runs
      exact ⟨_, finalStore, finalMap, finalWorld,
        (chain.spine.renamed_completed_iff ξ).mpr ⟨_, _, evaluated, runs⟩, .fault matched,
        finalHeaps, maps, worlds, frame, metadata, reached, related,
        by cases failure with
           | semantic => exact ⟨rawPost.rows, by intro _ impossible; cases impossible⟩
           | stage => exact rawPost⟩

private theorem failed_runs {budget : Nat} {environment : Environment} {reason : Word}
    {store finalStore : Store} {tag : Ty} {payload result : Value} {calls : List CallableCoercionSpine.Call}
    (trace : CallableCoercionSpine.RunsFor (CallableCoercionSpine.InvokeSized budget environment reason)
      store (.inLeft tag payload) calls result finalStore) :
    result = .inLeft (CallableCoercionSpine.finalType tag calls) payload ∧ finalStore = store := by
  generalize original : Value.inLeft tag payload = input at trace
  induction trace generalizing tag with
  | nil => cases original; exact ⟨rfl, rfl⟩
  | cons head tail ih =>
      cases original
      cases head with
      | skipped => exact ih rfl

include physical slots ownerFrame chain nonempty runtime typed environments heaps locals agrees actualTyped admitted in
theorem reflects (budget : Nat)
    (rawMeaning : ∀ size, size ≤ budget → RawReflectsAt (context := context) (receiving := receiving) owner receipt callerBridge functions faults stages size)
    (bodyMeaning : SelectedCompilationCoercionPathBounds.NativeBodies
      (headers := headers) (receiving := receiving) owner functions faults chain budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (output.expression.rename ξ) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages sourceSize
        invocation context environment before id outcome after ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld node.type output.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ PostAdmission callerBridge.forgetSlots context node.type outcome reached := by
  obtain ⟨rawSize, native, middleStore, rawBound, _rawStrict, rawEvaluation, runs⟩ :=
    chain.spine.renamed_completed_sized ξ completed
  obtain ⟨sourceRawSize, rawOutcome, middle, middleMap, middleWorld, rawTrace, represented, middleHeaps,
      maps, worlds, frame, metadata, middleState, related, rawPost⟩ :=
    rawMeaning rawSize (Nat.le_trans rawBound within) typed environments heaps locals agrees actualTyped initial admitted rawEvaluation
  cases represented with
  | value valueRep =>
      have valueTyped := rawPost.at_value.1
      have middleTyped := rawPost.at_value.2.heap
      obtain ⟨pathSize, outcome, after, finalMap, finalWorld, pathTrace, result, finalHeaps,
          tailMaps, tailWorlds, tailFrame, tailMetadata, ⟨finalPool, tailRelated⟩, preserved⟩ :=
        SelectedCompilationCoercionPathBounds.reflects owner functions faults chain ownerFrame
          runtime (callerBridge.pool middleState) (physical middleState) (slots middleState)
          agrees middleHeaps valueRep middleTyped valueTyped
          (CallableIndexedOwnedIndirectExpressionHeads.StableRows.after_administrative
            (callerBridge.pool initial) (callerBridge.pool middleState) admitted.rows frame)
          budget bodyMeaning (runs.mono within)
      obtain ⟨returned, _samePool, returnedRelated⟩ := callerBridge.restore middleState finalPool
        tailMaps tailWorlds tailFrame tailMetadata tailRelated
      have trace := Staging.Recursive.Size.Expression.coercedValue (lookupExpression?_sound receipt.found)
        nonempty rawTrace pathTrace
      exact ⟨_, outcome, after, finalMap, finalWorld, trace, result, finalHeaps,
        maps.trans tailMaps, worlds.trans tailWorlds, frame.trans tailFrame, metadata.trans tailMetadata,
        returned, callerProtocol.trans related returnedRelated,
        after_expression_sized_of_preserved initial returned admitted trace (fun value same => ⟨(preserved value same).value_typed, (preserved value same).heap_typed, metadata.trans (preserved value same).heap_extends⟩) (frame.trans tailFrame)⟩
  | @fault failure token matched =>
      obtain ⟨sameValue, rfl⟩ := failed_runs runs
      rw [chain.final_type ξ] at sameValue
      subst value
      have trace := Staging.Recursive.Size.Expression.coercedFault (lookupExpression?_sound receipt.found) nonempty rawTrace
      exact ⟨_, _, middle, middleMap, middleWorld, trace, .fault matched, middleHeaps,
        maps, worlds, frame, metadata, middleState, related,
        by cases failure with
           | semantic => exact ⟨rawPost.rows, by intro _ impossible; cases impossible⟩
           | stage => exact rawPost⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationCoercedDirectExpressionBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationHeaderFacts
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationHeaderFacts
open Core Frontend SourceInference
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}

theorem scoped_ledger (certified : SelectedCompilationNamedSourceTyping.Certified header) :
    ScopedRequirementLedgerWellFormed header.context header.function.source := by
  obtain ⟨_, certificate⟩ := certified
  have original : ScopedRequirementLedgerWellFormed header.function.context header.function.source := by
    simpa only [header.frame.context, header.frame.source] using certificate.requirement_ledger
  exact (RecursiveNamedInitialContextValidity.mono_fields header.extended).scopedRequirementLedger original

theorem runtime_ledger (certified : SelectedCompilationNamedSourceTyping.Certified header) :
    RuntimeRequirementLedgerValid header.context := (scoped_ledger certified).toRuntime

theorem hidden_fresh (certified : SelectedCompilationNamedSourceTyping.Certified header) :
    GenericImperativeMatch.MatchHiddenFresh header.function.source := by
  obtain ⟨_, certificate⟩ := certified
  apply CallableIndexedOwnedLocalIdentityFreshness.match_hidden_fresh
  rw [header.frame.source]
  exact certificate.local_identity_ownership

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationHeaderFacts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationOperatorMethodIssuance
/-! Authentic method issuance ties the actual compiler hook to the selected
Source method, full dictionary, real cache slot and staged method scope. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationOperatorMethodIssuance
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedStagedOperatorMethodCertificates (Receipt)
open CallableIndexedOwnedPreparedStagedOperatorMethodAuthority (Port SelectionSupport SelectionCore)
open CallablePreparedMethodSelection CallablePreparedMethodRuntimeMeaning
open CallableNamedMetadata (environment)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {values : SourceCoreCompatibleValues.Context}
  {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (receipt : Receipt policy body fuel compilation values source scope id reasonAt lowered)
  {project : SourceCoreEvidence.Projector} {caller : SourceSpecialization.SpecializedFunction}
  (actual : Operator compiled.sourceProgram project caller compilation
    (CallableIndexedOwnedPreparedStagedDirectCallCertificates.Child policy body fuel compilation) (fuel+1)
    source scope id reasonAt policy.callables receipt.node lowered)
  (special : (match policy.lowerSpecial? with
    | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
    | some lower => lower compilation
        (CallableIndexedOwnedPreparedStagedDirectCallCertificates.Child policy body fuel compilation)
        (fuel+1) source scope id reasonAt) = .ok (some lowered))

def authentic : Receipt policy body fuel compilation values source scope id reasonAt lowered :=
  ⟨compiled.sourceProgram, project, caller, receipt.node, receipt.metadata, actual, special, receipt.accepted⟩

include receipt actual special in
theorem selection_core
    (selected : OperatorSource actual)
    (formed : CallableCoercionMethodInstantiation.Formation
      selected.certificate.selected.implementation selected.certificate.selected.declaration)
    (covered : CallableCoercionEvidenceOrigins.CallerCovered caller actual.selection.method)
    (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
    (bodies : SelectedCompilationBodyTyping.Bodies compiled)
    (cached : Cached compiled actual.selection.method.specialized)
    {context : SourceSemantics.Context}
    (signatures : context.signatures = compiled.sourceProgram.signatures)
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (assumptions : ∀ goal, goal ∈ caller.assumptions → goal ∈ context.assumptions)
    (unique : NodeOccurrencesUnique source) (idsUnique : RequirementIdsUnique context)
    (typed : ExpressionHasType source context id receipt.node.type) :
    SelectionCore (authentic receipt actual special) selected := by
  have goal := CallableIndexedOwnedPreparedStagedMethodSelectionGoal.admissible
    (authentic receipt actual special) selected signatures ledger assumptions unique idsUnique typed
  have range := SelectedCompilationMethodSelectionRanges.of_selected
    selected.certificate.selected bodies.signatures formed signatures goal
  obtain ⟨definition, member, identity, instantiated, types, lexical, facts, certificate⟩ :=
    SelectedCompilationMethodSelectionTyping.certificate checked bodies cached
      selected.certificate.selected formed.parameters range
  exact ⟨formed, range, covered, certificate.graph_closed.wellFormed.nodeOccurrencesUnique⟩

private theorem exact_key {plan : SourceCompilationPlan.Plan} {key : SourceCompilationPlan.Key}
    {row : SourceSpecialization.SpecializedFunction}
    (selected : SourceCompilationPlan.exactSpecialization plan key = .ok row) : row.key = key := by
  unfold SourceCompilationPlan.exactSpecialization at selected
  split at selected <;> try contradiction
  rename_i actual found
  cases selected
  have member : row ∈ plan.specializations.filter (fun candidate => decide (candidate.key = key)) := by
    rw [found]
    simp
  exact of_decide_eq_true (List.mem_filter.mp member).2

private theorem cached_key {method : ExecutableImplMethods.CheckedMethod}
    (cached : Cached compiled method.specialized) : cached.named.signature.key = method.specialized.key := by
  have record := CallableIndexedActualNamedSourceReceipts.cached_record compiled cached.selected cached.compilation.hook
  exact (exact_key record).symm.trans (congrArg (fun row : SourceSpecialization.SpecializedFunction => row.key) cached.same)

private theorem descriptor {method : ExecutableImplMethods.CheckedMethod}
    (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method) :
    Nonempty (SourceCoreCallableContracts.Descriptor compiled.indexed.ancestry.graph.inputs.callable.table
      (.named principal.named.signature.key)) := by
  obtain ⟨origin, selected, _, _⟩ := principal.hook_history
  cases made : SourceCoreCallableContracts.descriptor compiled.indexed.ancestry.graph.inputs.callable.table
      (.named principal.named.signature.key) with
  | error error =>
    unfold SourceCoreCallableContracts.descriptor at made
    split at made
    · next absent => rw [selected] at absent; cases absent
    · cases made
  | ok descriptor => exact ⟨descriptor⟩

include receipt actual special in
private theorem of_actual_with_identity
    (selected : OperatorSource actual)
    (support : SelectionCore (authentic receipt actual special) selected)
    (resolved : CallableIndexedOwnedPreparedStagedDirectCallAuthority.ResolvedCaller compiled.sourceProgram
      actual.selection.method.specialized (environment actual.dictionary))
        (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
    (bodies : SelectedCompilationBodyTyping.Bodies compiled)
    (_catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
    {before : SourceCompilationPlan.Plan} {preparationFuel budget : Nat}
    (prepared : SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget compiled.sourceProgram before
      preparationFuel budget = .ok compilation.plan)
    (callerMember : caller ∈ compilation.plan.specializations)
    (nodeMember : .expression receipt.node ∈ caller.function.typedBody.nodes)
    (samePlan : compilation.plan = compiled.indexed.base.plan)
    (globals : compilation.globals = compiled.indexed.base.globals)
    {context : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    (signatures : context.signatures = compiled.sourceProgram.signatures)
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (assumptions : ∀ goal, goal ∈ caller.assumptions → goal ∈ context.assumptions)
    (_unique : RequirementIdsUnique context)
    (dictionary : callerEvidence = environment actual.available)
    (identity : ∀ actualBody actualDictionary,
      Dynamic.OperatorMethodSelected (Program.ofChecked compiled.sourceProgram) context callerEvidence
        selected.traitName selected.methodName receipt.node.requirements actualBody actualDictionary →
      actualBody = CallableCoercionMethodInstantiation.bodyInstance compiled.sourceProgram actual.selection.method ∧
        actualDictionary = environment actual.dictionary)
    (actualStages : RecursiveNamedPreparedStageContracts.Prepared compiled
      compiled.indexed.ancestry.graph.inputs.callable) :
    Nonempty {port : Port (compiled := compiled) receipt context callerEvidence
      (RecursiveNamedPreparedStageScopes.registry actualStages) //
      Dynamic.TypedOperatorMethodSelected (Program.ofChecked compiled.sourceProgram) context callerEvidence
        port.principal.traitName port.principal.methodName receipt.node.requirements
        port.principal.sourceBody port.principal.dictionary} := by
  let authentic := authentic receipt actual special
  obtain ⟨_, _, _, _, _, target⟩ := actual.prepared prepared callerMember nodeMember
  obtain ⟨initial⟩ := actual.cached prepared callerMember nodeMember compiled samePlan
  obtain ⟨diagnostics, code, diagnosticPresent, codeFound, codeAccepted⟩ := NamedCalls.compiled_at compiled.indexed initial.selected
  obtain ⟨generation⟩ := CallableIndexedNamedGeneration.of_accepted compiled.indexed codeAccepted
  let cached : Cached compiled actual.selection.method.specialized :=
    ⟨initial.index, initial.named, _, code, initial.selected, initial.same, codeFound, generation⟩
  have chosenTyped := SelectedCompilationMethodSelectionTyping.source_selects checked bodies cached
    selected.toSourceReceipt support.formed support.range signatures ledger assumptions support.covered
  have requirements : actual.requirements = receipt.node.requirements := by
    have layout := CallableCallRequirementLayouts.ordinary_owned actual.ordinary
    simpa only [receipt.metadata.coercions, coercionRequirementIds, List.flatMap_nil, List.append_nil] using layout.symm
  have chosenTyped : Dynamic.TypedOperatorMethodSelected (Program.ofChecked compiled.sourceProgram) context callerEvidence
      selected.traitName selected.methodName receipt.node.requirements
      (CallableCoercionMethodInstantiation.bodyInstance compiled.sourceProgram actual.selection.method)
      (environment actual.dictionary) := by
    simpa only [dictionary, requirements] using chosenTyped
  have chosen := chosenTyped.selected
  let principal := CallableIndexedOwnedMethodPrincipal.of_selected cached chosen
  have key : cached.named.signature.key = actual.key :=
    (cached_key cached).trans ((congrArg (fun row : SourceSpecialization.SpecializedFunction => row.key) target).symm.trans
      (exact_key actual.target.selected))
  have member : (cached.named.signature, cached.index) ∈ compilation.globals.zipIdx.filter
      (fun row => decide (row.1.key = actual.key)) := by
    refine List.mem_filter.mpr ⟨List.mk_mem_zipIdx_iff_getElem?.mpr ?_, ?_⟩
    · rw [globals]
      exact CallableIndexedPreparedInventories.cached_global_at compiled cached.selected
    · simp only [key, decide_true]
  rw [actual.native.global] at member
  have aligned := Prod.mk.inj (List.mem_singleton.mp member)
  have signature : principal.named.signature = receipt.signature :=
    aligned.1.trans (authentic.signature_eq receipt)
  have slot : principal.cached.index = receipt.index := aligned.2.trans (authentic.index_eq receipt)
  obtain ⟨descriptor⟩ := descriptor principal
  obtain ⟨sidecar, _, _, staged⟩ := RecursiveMethodPreparedStageScopes.selected_of_descriptor actualStages principal descriptor
  obtain ⟨retained⟩ := selected.toSourceReceipt.retained checked
  obtain ⟨sourceAt⟩ := SelectedCompilationMethodRuntimeProfile.source_at (values := .initial compiled.compatible.checked) cached rfl retained bodies
    chosenTyped support.unique (CallableIndexedOwnedPublicSignatureCatalog.signatures compiled).symm
  let port : Port (compiled := compiled) receipt context callerEvidence
      (RecursiveNamedPreparedStageScopes.registry actualStages) :=
    ⟨authentic, rfl, principal, signature, slot, by
      rcases actual.form with ⟨operator, operand, form, _⟩ | ⟨operator, left, right, form, _⟩
      · exact .inl ⟨operator, operand, form, by simpa only [principal, CallableIndexedOwnedMethodPrincipal.of_selected, form] using selected.dispatch⟩
      · exact .inr ⟨operator, left, right, form, by simpa only [principal, CallableIndexedOwnedMethodPrincipal.of_selected, form] using selected.dispatch⟩,
      chosen, identity, _, staged, ⟨diagnostics, diagnosticPresent, rfl⟩, by
        change CallableIndexedOwnedPreparedStagedDirectCallAuthority.ResolvedCaller compiled.sourceProgram
          cached.named.specialized (environment actual.dictionary)
        rw [cached.same]
        exact resolved,
      sourceAt⟩
  exact ⟨⟨port, chosenTyped⟩⟩

include receipt actual special in
theorem of_actual_with_evidence
    (selected : OperatorSource actual)
    (support : SelectionCore (authentic receipt actual special) selected)
    (coherent : RecursiveMethodDictionaryIdentity.Coherent compiled.sourceProgram.signatures.resolutionRules
      (CallableCoercionMethodInstantiation.bodyInstance compiled.sourceProgram actual.selection.method).context.assumptions)
    (resolved : CallableIndexedOwnedPreparedStagedDirectCallAuthority.ResolvedCaller compiled.sourceProgram
      actual.selection.method.specialized (environment actual.dictionary))
        (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
    (bodies : SelectedCompilationBodyTyping.Bodies compiled)
    (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
    {before : SourceCompilationPlan.Plan} {preparationFuel budget : Nat}
    (prepared : SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget compiled.sourceProgram before
      preparationFuel budget = .ok compilation.plan)
    (callerMember : caller ∈ compilation.plan.specializations)
    (nodeMember : .expression receipt.node ∈ caller.function.typedBody.nodes)
    (samePlan : compilation.plan = compiled.indexed.base.plan)
    (globals : compilation.globals = compiled.indexed.base.globals)
    {context : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    (signatures : context.signatures = compiled.sourceProgram.signatures)
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (assumptions : ∀ goal, goal ∈ caller.assumptions → goal ∈ context.assumptions)
    (unique : RequirementIdsUnique context)
    (dictionary : callerEvidence = environment actual.available)
    (actualStages : RecursiveNamedPreparedStageContracts.Prepared compiled
      compiled.indexed.ancestry.graph.inputs.callable) :
    Nonempty {port : Port (compiled := compiled) receipt context callerEvidence
      (RecursiveNamedPreparedStageScopes.registry actualStages) //
      Dynamic.TypedOperatorMethodSelected (Program.ofChecked compiled.sourceProgram) context callerEvidence
        port.principal.traitName port.principal.methodName receipt.node.requirements
        port.principal.sourceBody port.principal.dictionary} := by
  have chosen := selected.toSourceReceipt.selects checked support.formed support.range signatures ledger assumptions support.covered
  have requirements : actual.requirements = receipt.node.requirements := by
    have layout := CallableCallRequirementLayouts.ordinary_owned actual.ordinary
    simpa only [receipt.metadata.coercions, coercionRequirementIds, List.flatMap_nil, List.append_nil] using layout.symm
  have chosen : Dynamic.OperatorMethodSelected (Program.ofChecked compiled.sourceProgram) context callerEvidence
      selected.traitName selected.methodName receipt.node.requirements
      (CallableCoercionMethodInstantiation.bodyInstance compiled.sourceProgram actual.selection.method)
      (environment actual.dictionary) := by
    simpa only [dictionary, requirements] using chosen
  apply of_actual_with_identity receipt actual special selected support resolved checked bodies catalog
    prepared callerMember nodeMember samePlan globals signatures ledger assumptions unique dictionary ?_ actualStages
  intro actualBody actualDictionary selectedActual
  have req : receipt.node.requirements = actual.selection.primaryRequirement :: selected.methodIds :=
    requirements.symm.trans selected.requirements
  rw [req] at chosen selectedActual
  have callerValid : callerEvidence.Valid compiled.sourceProgram.signatures.resolutionRules := by
    rw [dictionary]
    exact (CallableEvidenceEnvironment.resolved_valid actual.resolved).1
  exact RecursiveMethodDictionaryIdentity.same_coherent catalog
    (fun _ _ first second => unique.contains_unique first second) signatures callerValid chosen selectedActual coherent


include receipt actual special in
theorem of_actual_with_origins
    (selected : OperatorSource actual)
    (support : SelectionCore (authentic receipt actual special) selected)
    (coherent : RecursiveMethodOriginIdentity.Coherent (environment actual.available)
      ((selected.certificate.roots.primary :: selected.certificate.roots.methodEvidence).map CallableNamedMetadata.evidence)
      (CallableCoercionMethodInstantiation.bodyInstance compiled.sourceProgram actual.selection.method).context.assumptions)
    (resolved : CallableIndexedOwnedPreparedStagedDirectCallAuthority.ResolvedCaller compiled.sourceProgram
      actual.selection.method.specialized (environment actual.dictionary))
        (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
    (bodies : SelectedCompilationBodyTyping.Bodies compiled)
    (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
    {before : SourceCompilationPlan.Plan} {preparationFuel budget : Nat}
    (prepared : SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget compiled.sourceProgram before
      preparationFuel budget = .ok compilation.plan)
    (callerMember : caller ∈ compilation.plan.specializations)
    (nodeMember : .expression receipt.node ∈ caller.function.typedBody.nodes)
    (samePlan : compilation.plan = compiled.indexed.base.plan)
    (globals : compilation.globals = compiled.indexed.base.globals)
    {context : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    (signatures : context.signatures = compiled.sourceProgram.signatures)
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (assumptions : ∀ goal, goal ∈ caller.assumptions → goal ∈ context.assumptions)
    (unique : RequirementIdsUnique context)
    (dictionary : callerEvidence = environment actual.available)
    (actualStages : RecursiveNamedPreparedStageContracts.Prepared compiled
      compiled.indexed.ancestry.graph.inputs.callable) :
    Nonempty {port : Port (compiled := compiled) receipt context callerEvidence
      (RecursiveNamedPreparedStageScopes.registry actualStages) //
      Dynamic.TypedOperatorMethodSelected (Program.ofChecked compiled.sourceProgram) context callerEvidence
        port.principal.traitName port.principal.methodName receipt.node.requirements
        port.principal.sourceBody port.principal.dictionary} := by
  have chosen := selected.toSourceReceipt.selects checked support.formed support.range signatures ledger assumptions support.covered
  have requirements : actual.requirements = receipt.node.requirements := by
    have layout := CallableCallRequirementLayouts.ordinary_owned actual.ordinary
    simpa only [receipt.metadata.coercions, coercionRequirementIds, List.flatMap_nil, List.append_nil] using layout.symm
  have chosen : Dynamic.OperatorMethodSelected (Program.ofChecked compiled.sourceProgram) context callerEvidence
      selected.traitName selected.methodName receipt.node.requirements
      (CallableCoercionMethodInstantiation.bodyInstance compiled.sourceProgram actual.selection.method)
      (environment actual.dictionary) := by
    simpa only [dictionary, requirements] using chosen
  apply of_actual_with_identity receipt actual special selected support resolved checked bodies catalog
    prepared callerMember nodeMember samePlan globals signatures ledger assumptions unique dictionary ?_ actualStages
  intro actualBody actualDictionary selectedActual
  have req : receipt.node.requirements = actual.selection.primaryRequirement :: selected.methodIds :=
    requirements.symm.trans selected.requirements
  rw [req] at chosen selectedActual
  have produced := CallableMethodOriginSource.roots_produced selected.toSourceReceipt signatures ledger assumptions
  have produced := (congrArg (fun ids => RecursiveMethodOriginIdentity.RootsProduced context
    (environment actual.available) ids
    ((selected.certificate.roots.primary :: selected.certificate.roots.methodEvidence).map CallableNamedMetadata.evidence))
    selected.requirements).mp produced
  rw [← dictionary] at produced coherent
  exact RecursiveMethodOriginIdentity.same_from_origins catalog unique produced chosen selectedActual coherent



include receipt actual special in
/-- Existing empty-method issuers construct the strengthened receipt internally. -/
theorem of_actual
    (selected : OperatorSource actual)
    (support : SelectionSupport (authentic receipt actual special) selected)
        (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
    (bodies : SelectedCompilationBodyTyping.Bodies compiled)
    (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
    {before : SourceCompilationPlan.Plan} {preparationFuel budget : Nat}
    (prepared : SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget compiled.sourceProgram before
      preparationFuel budget = .ok compilation.plan)
    (callerMember : caller ∈ compilation.plan.specializations)
    (nodeMember : .expression receipt.node ∈ caller.function.typedBody.nodes)
    (samePlan : compilation.plan = compiled.indexed.base.plan)
    (globals : compilation.globals = compiled.indexed.base.globals)
    {context : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    (signatures : context.signatures = compiled.sourceProgram.signatures)
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (assumptions : ∀ goal, goal ∈ caller.assumptions → goal ∈ context.assumptions)
    (unique : RequirementIdsUnique context)
    (dictionary : callerEvidence = environment actual.available)
    (actualStages : RecursiveNamedPreparedStageContracts.Prepared compiled
      compiled.indexed.ancestry.graph.inputs.callable) :
    Nonempty {port : Port (compiled := compiled) receipt context callerEvidence
      (RecursiveNamedPreparedStageScopes.registry actualStages) //
      Dynamic.TypedOperatorMethodSelected (Program.ofChecked compiled.sourceProgram) context callerEvidence
        port.principal.traitName port.principal.methodName receipt.node.requirements
        port.principal.sourceBody port.principal.dictionary} := by
  have chosen := selected.toSourceReceipt.selects checked support.formed support.range signatures ledger assumptions support.covered
  have emptyDictionary := RecursiveMethodSelectionIdentity.dictionary_empty chosen support.empty
  have empty : actual.selection.method.specialized.assumptions = [] := support.empty
  have resolved : CallableIndexedOwnedPreparedStagedDirectCallAuthority.ResolvedCaller compiled.sourceProgram
      actual.selection.method.specialized (environment actual.dictionary) :=
    ⟨[], by rw [empty]; rfl, emptyDictionary⟩
  apply of_actual_with_evidence receipt actual special selected (support.core (authentic receipt actual special))
    (support.empty ▸ RecursiveMethodDictionaryIdentity.Coherent.empty _) resolved
    checked bodies catalog prepared callerMember nodeMember samePlan globals
    signatures ledger assumptions unique dictionary actualStages

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationOperatorMethodIssuance
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodSelectionIssuer
/-! One issuer dispatches the existing empty-method catalog and the validated
full-evidence and actual-origin catalogs. Named and closure collectors share the same proof bodies. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodSelectionIssuer
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedStagedOperatorMethodCertificates (Receipt)
open CallablePreparedMethodSelection CallablePreparedMethodRuntimeMeaning
open CallableNamedMetadata (environment)

open CallableIndexedOwnedPreparedStagedMethodSelectionIssuer (Catalog)
open CallableIndexedOwnedPreparedStagedOperatorMethodAuthority (Port SelectionSupport)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {values : SourceCoreCompatibleValues.Context}
  {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (receipt : Receipt policy body fuel compilation values source scope id reasonAt lowered)
  {project : SourceCoreEvidence.Projector} {caller : SourceSpecialization.SpecializedFunction}
  (actual : Operator compiled.sourceProgram project caller compilation
    (CallableIndexedOwnedPreparedStagedDirectCallCertificates.Child policy body fuel compilation) (fuel+1)
    source scope id reasonAt policy.callables receipt.node lowered)
  (special : (match policy.lowerSpecial? with
    | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
    | some lower => lower compilation
        (CallableIndexedOwnedPreparedStagedDirectCallCertificates.Child policy body fuel compilation)
        (fuel+1) source scope id reasonAt) = .ok (some lowered))

include receipt actual special in
/-- Complete static evidence is recovered from the actual compiler table.
The public body family supplies no method execution or dictionary equality. -/
theorem of_actual
    (selected : OperatorSource actual)
    (methods : Catalog compiled)
        (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
    (bodies : SelectedCompilationBodyTyping.Bodies compiled)
    (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
    {before : SourceCompilationPlan.Plan} {preparationFuel budget : Nat}
    (prepared : SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget compiled.sourceProgram before
      preparationFuel budget = .ok compilation.plan)
    (callerMember : caller ∈ compilation.plan.specializations)
    (nodeMember : .expression receipt.node ∈ caller.function.typedBody.nodes)
    (samePlan : compilation.plan = compiled.indexed.base.plan)
    (globals : compilation.globals = compiled.indexed.base.globals)
    {context : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    (signatures : context.signatures = compiled.sourceProgram.signatures)
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (assumptions : ∀ goal, goal ∈ caller.assumptions → goal ∈ context.assumptions)
    (unique : RequirementIdsUnique context)
    (dictionary : callerEvidence = environment actual.available)
    (sourceUnique : NodeOccurrencesUnique source)
    (typed : ExpressionHasType source context id receipt.node.type)
    (actualStages : RecursiveNamedPreparedStageContracts.Prepared compiled
      compiled.indexed.ancestry.graph.inputs.callable) :
    Nonempty {port : Port (compiled := compiled) receipt context callerEvidence
      (RecursiveNamedPreparedStageScopes.registry actualStages) //
      Dynamic.TypedOperatorMethodSelected (Program.ofChecked compiled.sourceProgram) context callerEvidence
        port.principal.traitName port.principal.methodName receipt.node.requirements
        port.principal.sourceBody port.principal.dictionary} := by
  obtain ⟨cached⟩ := actual.cached prepared callerMember nodeMember compiled samePlan
  let authentic := SelectedCompilationOperatorMethodIssuance.authentic receipt actual special
  cases methods with
  | generic methods =>
      let chosen := selected.certificate.selected
      have formed := methods.formed _ chosen.implementationMember _ chosen.methodMember
      have emptyAssumptions : actual.selection.method.specialized.assumptions = [] := by
        have fields := CallableCoercionBodyProvenance.specialization_fields chosen.specialized
        rw [fields.2]
        change List.map _ (chosen.implementation.methodAssumptions chosen.trait chosen.declaration) = []
        rw [methods.assumptions chosen.implementation chosen.implementationMember
          chosen.declaration chosen.methodMember chosen.trait chosen.traitMember]
        rfl
      have covered : CallableCoercionEvidenceOrigins.CallerCovered caller actual.selection.method := by
        obtain ⟨headers, resolved, assembled, goals⟩ :=
          CallableCoercionEvidenceOrigins.materialized_operator actual.materialized
        have emptyDictionary : actual.dictionary = [] := List.map_eq_nil_iff.mp (goals.trans emptyAssumptions)
        have allEmpty := assembled.symm.trans emptyDictionary
        have headersEmpty : headers = [] := (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp allEmpty).1).1
        rw [headersEmpty] at resolved
        have goalsEmpty : actual.selection.method.traitPredicates = [] := by
          have lengths := resolved.length_eq
          simpa using lengths
        intro goal member
        rw [goalsEmpty] at member
        cases member
      have core := SelectedCompilationOperatorMethodIssuance.selection_core receipt actual special
        selected formed covered checked bodies cached signatures ledger assumptions sourceUnique unique typed
      have support : SelectionSupport authentic selected :=
        ⟨core.formed, core.range, core.covered, core.unique, emptyAssumptions⟩
      exact SelectedCompilationOperatorMethodIssuance.of_actual receipt actual special
        selected support checked bodies catalog prepared callerMember nodeMember samePlan globals
        signatures ledger assumptions unique dictionary actualStages
  | evidence methods =>
      have finalMember : caller ∈ compiled.indexed.base.plan.specializations := samePlan ▸ callerMember
      obtain ⟨evidence⟩ := methods.ready.operator finalMember actual nodeMember
      have formed := methods.formed.formed _ selected.certificate.selected.implementationMember
        _ selected.certificate.selected.methodMember
      have support := SelectedCompilationOperatorMethodIssuance.selection_core receipt actual special
        selected formed evidence.covered checked bodies cached
        signatures ledger assumptions sourceUnique unique typed
      obtain ⟨definition, _member, _identity, instantiated⟩ :=
        selected.certificate.selected.instantiates checked support.formed.parameters support.range
      have coherent := methods.coherent.of_instantiated cached instantiated
      exact SelectedCompilationOperatorMethodIssuance.of_actual_with_evidence receipt actual special
        selected support coherent (evidence.materialized.for_actual actual.materialized)
        checked bodies catalog prepared callerMember nodeMember samePlan globals
        signatures ledger assumptions unique dictionary actualStages
  | origins methods =>
      have finalMember : caller ∈ compiled.indexed.base.plan.specializations := samePlan ▸ callerMember
      obtain ⟨evidence⟩ := methods.ready.operator finalMember actual nodeMember
      have formed := methods.formed.formed _ selected.certificate.selected.implementationMember
        _ selected.certificate.selected.methodMember
      have support := SelectedCompilationOperatorMethodIssuance.selection_core receipt actual special
        selected formed evidence.covered checked bodies cached
        signatures ledger assumptions sourceUnique unique typed
      have coherent := evidence.at_source_receipt selected.toSourceReceipt
      exact SelectedCompilationOperatorMethodIssuance.of_actual_with_origins receipt actual special
        selected support coherent (evidence.materialized.for_actual actual.materialized)
        checked bodies catalog prepared callerMember nodeMember samePlan globals
        signatures ledger assumptions unique dictionary actualStages

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodSelectionIssuer
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationCoercionChainIssuance
/-! Original Source path typing and accepted compiler steps produce the ordered
method chain. Every method port is issued from the same final preparation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationCoercionChainIssuance
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedStagedCoercionChain (Chain)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {project : SourceCoreEvidence.Projector} {compilation : SourceCoreFunctions.Context}
  {caller : SourceSpecialization.SpecializedFunction}
  {available : SourceTypedRuntime.RuntimeEvidenceEnvironment}
  {scope : SourceCoreBasic.Scope} {node : ExpressionNode}
  {policy : SourceCoreFunctions.CallablePolicy}
  (methods : CallableIndexedOwnedPreparedStagedClosedCoercionSelection.Catalog compiled)
    (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
  (bodies : SelectedCompilationBodyTyping.Bodies compiled)
  (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
  {before : SourceCompilationPlan.Plan} {preparationFuel budget : Nat}
  (prepared : SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget compiled.sourceProgram before
    preparationFuel budget = .ok compilation.plan)
  (callerMember : caller ∈ compilation.plan.specializations)
  (nodeMember : .expression node ∈ caller.function.typedBody.nodes)
  (samePlan : compilation.plan = compiled.indexed.base.plan)
  (globals : compilation.globals = compiled.indexed.base.globals)
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  (signatures : context.signatures = compiled.sourceProgram.signatures)
  (ledger : context.solvedRequirements = caller.function.solvedRequirements)
  (assumptions : ∀ goal, goal ∈ caller.assumptions → goal ∈ context.assumptions)
  (resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment compiled.sourceProgram caller.key caller.assumptions = .ok available)
  (unique : RequirementIdsUnique context)
  (dictionary : invocation.evidence = CallableNamedMetadata.environment available)
  (actualStages : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)

def Certified {source target : TypeSystem.Ty} {input output : SourceCoreBasic.LoweredExpr}
    {steps : List CoercionStep} {calls : List CallableCoercionSpine.Call}
    (chain : Chain compiled project compilation caller available scope node policy context invocation
      (RecursiveNamedPreparedStageScopes.registry actualStages) source target input steps output calls) : Prop :=
  match chain with
  | .nil => True
  | .cons _ port _ tail =>
      SelectedCompilationMethodBodySupport.Certified port.principal port.sourceAt ∧ Certified tail

include methods checked bodies catalog prepared callerMember nodeMember samePlan globals
  signatures ledger assumptions resolved unique dictionary actualStages in
theorem of_spine {input output : SourceCoreBasic.LoweredExpr} {steps : List CoercionStep}
    {calls : List CallableCoercionSpine.Call}
    (spine : CallableCoercionSpine.Spine compiled.sourceProgram project compilation caller available
      scope node policy input steps output calls)
    {source target : TypeSystem.Ty} (valid : CoercionPathValid context source target steps)
    (sites : ∀ step ∈ steps, step ∈ node.coercions ++ CallableCoercionPreparation.argumentSteps node) :
    Nonempty {chain : Chain compiled project compilation caller available scope node policy context invocation
      (RecursiveNamedPreparedStageScopes.registry actualStages) source target input steps output calls // Certified actualStages chain} := by
  induction spine generalizing source with
  | nil => cases valid; exact ⟨⟨.nil, True.intro⟩⟩
  | @cons input step middle rest output call calls head tail ih =>
    cases valid with
    | cons valid remaining =>
      obtain ⟨⟨port, certified⟩⟩ := SelectedCompilationClosedCoercionSelection.of_actual head methods checked
        bodies catalog prepared callerMember nodeMember (sites step (by simp)) samePlan globals
        signatures ledger assumptions resolved unique dictionary actualStages
      obtain ⟨⟨chain, tailCertified⟩⟩ := ih remaining (fun step member => sites step (List.mem_cons_of_mem _ member))
      exact ⟨⟨.cons head port valid chain, certified, tailCertified⟩⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationCoercionChainIssuance
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPrimitiveMethodTerminalSupport
/-! An actual terminal method with reads, literals and conditional selection
uses the same recursive compiler certificate and original Source typing. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPrimitiveMethodTerminalSupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SelectedCompilationMethodBodySupport (Packet Support)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)
open CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles (MetadataFor)

open CallableIndexedOwnedPreparedStagedPrimitiveMethodTerminalSupport (PrimitiveSource)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {method : ExecutableImplMethods.CheckedMethod}
  (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
  (packet : Packet principal)
  (diagnostic : CallableIndexedOwnedPreparedStagedMethodTerminalSupport.DiagnosticAt principal.cached)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (signatures : SignatureCatalogWellFormed compiled.sourceProgram.signatures)
  (certified : SelectedCompilationMethodBodySupport.Certified principal packet.sourceAt)
  (forms : PrimitiveSource principal.sourceBody.source)
  (metadata : MetadataFor compiled.indexed principal.named principal.sourceBody.source (fun _ => False))
  (tree : GeneralSyntax principal.sourceBody.source packet.expression (fun _ => False))

include diagnostic receiver signatures certified forms metadata tree in
theorem of_child
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
    {stages : Staging.Recursive.Registry} {child : Staging.Recursive.Scope}
    (selected : stages.Closure principal.sourceFunction child) :
    Nonempty (SelectedCompilationMethodBodySupport.Child principal packet headers stages child
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) := by
  have sourceEq : child.source = principal.sourceBody.source := stages.source selected
  obtain ⟨node, childFound, rawType, typed⟩ :=
    SelectedCompilationMethodBodySupport.child_typed principal packet certified selected
  have found : principal.sourceBody.source.lookupExpression? packet.expression = some node := sourceEq ▸ childFound
  have originalTyped : ExpressionHasType principal.sourceBody.source packet.sourceAt.context packet.expression node.type := sourceEq ▸ typed
  obtain ⟨fuel, ⟨root⟩⟩ := SelectedCompilationMethodBodySupport.policy_receipt principal packet
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
  have noIndirect : SelectedCompilationMethodRootSupport.NoIndirect
      (compiled := compiled) (invocation := child) childCertificate := by
    intro callFuel callScope callId callee ids callMetadata code compiler _path
    rcases forms callId compiler.original (by simpa only [sourceEq] using compiler.found) with
      ⟨name, resolution, form⟩ | ⟨spelling, resolution, form⟩ | ⟨condition, first, second, form⟩ <;>
      have impossible := compiler.originalForm <;> simp [form] at impossible
  let actual : SelectedCompilationMethodRootSupport.Root compiled headers stages
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
    catalog := signatures
    runtime := by simpa only [sourceEq] using SelectedCompilationMethodBodySupport.runtime principal packet certified
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
      intro indexScope indexId base key actual baseNode keyNode layout comparison first second indexed _keyFound form _sourceType _path
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
  exact ⟨⟨SelectedCompilationMethodRootSupport.RootAt.ofRoot actual, rfl, rfl, rfl⟩⟩

include diagnostic receiver signatures certified forms metadata tree in
theorem of_actual
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
    {stages : Staging.Recursive.Registry} :
    Support principal packet headers stages
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics) :=
  ⟨fun _ selected => of_child principal packet diagnostic receiver signatures certified forms metadata tree selected⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPrimitiveMethodTerminalSupport
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPrimitiveMethodAdmission
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPrimitiveMethodAdmission
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedPrimitiveMethodAdmission (Certificate)
open CallableIndexedOwnedPreparedNamedSourceAdmissionTransport (statements)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (certificate : Certificate compiled)
  {method : ExecutableImplMethods.CheckedMethod}
  (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)

include certificate in
/-- SourceAt fixes the original method context, evidence and body typing. The
actual accepted compiler action issues the static packet used by the family. -/
theorem support
    (sourceAt : CallablePreparedMethodRuntimeProfileFactory.SourceAt principal.cached.compilation
      (.initial compiled.compatible.checked) principal.sourceBody principal.dictionary)
    (diagnostic : CallableIndexedOwnedPreparedStagedMethodTerminalSupport.DiagnosticAt principal.cached)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (signatures : SignatureCatalogWellFormed compiled.sourceProgram.signatures)
    (certified : SelectedCompilationMethodBodySupport.Certified principal sourceAt)
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
    (stages : Staging.Recursive.Registry) :
    ∃ packet : SelectedCompilationMethodBodySupport.Packet principal,
      packet.sourceAt = sourceAt ∧ SelectedCompilationMethodBodySupport.Support
        principal packet headers stages (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics) := by
  obtain ⟨source⟩ := certificate.selected principal
  have roots : statements (CallableIndexedNamedGeneration.source principal.named) = principal.cached.compilation.statements := by
    rw [principal.source_eq]
    exact principal.source_frame.roots.filterMap_eq
  have terminal := source.terminal
  rw [roots, principal.source_eq] at terminal
  obtain ⟨receipt⟩ := CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.of_accepted
    (by rfl) terminal sourceAt.accepted
  let packet : SelectedCompilationMethodBodySupport.Packet principal :=
    ⟨sourceAt, source.expression, receipt⟩
  refine ⟨packet, rfl, ?_⟩
  apply SelectedCompilationPrimitiveMethodTerminalSupport.of_actual principal packet diagnostic receiver signatures certified
  · simpa only [principal.source_eq] using source.forms
  · simpa only [principal.source_eq] using source.metadata
  · simpa only [principal.source_eq] using source.tree

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPrimitiveMethodAdmission
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationScopedMethodAdmission
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationScopedMethodAdmission
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedScopedMethodAdmission (Certificate)
open CallableIndexedOwnedPreparedNamedSyntaxAdmission (DirectSite TableAligned)
open CallableIndexedOwnedPreparedNamedSourceAdmissionTransport (statements)
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {directRows : List SourceSpecialization.SpecializedFunction}
  (certificate : Certificate compiled directRows)
  {method : ExecutableImplMethods.CheckedMethod}
  (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)

include certificate in
/-- Genuine method selection supplies the resolved caller internally to the
program issuer. The certificate supplies static Source syntax and metadata. -/
theorem support
    (sourceAt : CallablePreparedMethodRuntimeProfileFactory.SourceAt principal.cached.compilation
      (.initial compiled.compatible.checked) principal.sourceBody principal.dictionary)
    (resolved : CallableIndexedOwnedPreparedStagedDirectCallAuthority.ResolvedCaller
      compiled.sourceProgram principal.named.specialized principal.dictionary)
    (diagnostic : CallableIndexedOwnedPreparedStagedMethodTerminalSupport.DiagnosticAt principal.cached)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (bodies : SelectedCompilationBodyTyping.Bodies compiled)
    (certified : SelectedCompilationMethodBodySupport.Certified principal sourceAt)
    {inputs : List (Input compiled)} (rows : Inventory inputs) (aligned : TableAligned inputs directRows)
    {recipe : SourceCoreIndexedSession.Recipe}
    (ready : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : entry ∈ compiled.indexed.entries)
    (stages : Staging.Recursive.Registry) :
    ∃ packet : SelectedCompilationMethodBodies.Packet principal,
      packet.sourceAt = sourceAt ∧ SelectedCompilationMethodBodies.Support
        principal packet (headers rows) stages
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics) := by
  obtain ⟨source⟩ := certificate.selected principal
  have roots : statements (CallableIndexedNamedGeneration.source principal.named) = principal.cached.compilation.statements := by
    rw [principal.source_eq]
    exact principal.source_frame.roots.filterMap_eq
  have resultType : principal.named.specialized.function.inferredBodyType = principal.sourceBody.resultType := by
    rw [principal.cached.same]
    rfl
  have shape := source.source.body.shape
  rw [roots, principal.source_eq] at shape
  have accepted := sourceAt.accepted principal.cached.compilation
  unfold SourceCoreLoops.lowerStatementsWithPolicy at accepted
  obtain ⟨flow, generated, returned⟩ := CompatibleEncoding.bind_ok accepted
  let packet : SelectedCompilationMethodScopedSupport.Packet principal :=
    ⟨sourceAt, flow, generated, (Except.ok.inj returned).symm, shape⟩
  refine ⟨.scoped packet, rfl, ?_⟩
  apply SelectedCompilationMethodEvidenceScopedRoots.of_actual_with_evidence
    (directSites := DirectSite directRows)
    principal packet diagnostic receiver bodies certified
    (by simpa only [principal.source_eq] using source.forms)
    (fun _ site => site.supported aligned)
    (by simpa only [principal.source_eq] using source.source.metadata)
    rows (fun _ site _ _ target global => site.covered rows aligned target global)
    resolved ready member
  obtain ⟨final, facts, typed, _complete⟩ :=
    SelectedCompilationMethodScopedSupport.statements principal packet certified
  have body := source.source.body
  rw [roots, principal.source_eq, resultType] at body
  exact body.syntax sourceAt.unique typed

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationScopedMethodAdmission
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationCatalogFrontdoor
set_option autoImplicit false
set_option Elab.async false

namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationCatalogFrontdoor
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SourceCoreIndexedSession RecursiveNamedPublicStartMeaning RecursiveNamedPublicHistoryFrontdoor
open CallableIndexedOwnedPreparedOrdinaryCatalogReceipts
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open RecursiveNamedPublicRootMeaning (RootSelection)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}

theorem eligible_of_admissible {compiled : SourceCoreUnifiedCompilation.Compiled}
    (formed : SignatureCatalogWellFormed compiled.sourceProgram.signatures)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : compiled.indexed.base.functions[index]? = some named)
    {context : Context} {instantiation : DeclarationInstantiation}
    (matched : CallableNamedMetadata.Matches named.specialized instantiation)
    (admissible : SourceSemantics.DeclarationInstantiation.Admissible context instantiation)
    (signatures : context.signatures = compiled.sourceProgram.signatures)
    (ordinaryReturn : instantiation.returnComptime = false)
    (ordinaryParameters : ∀ flag ∈ instantiation.parameterComptime, flag = false) :
    Eligible compiled named.specialized := by
  obtain ⟨signature, member, declaration⟩ := admissible.signature_id
  have origin := SelectedCompilationCatalog.ordinary_origin compiled formed
    (RecursiveNamedPreparedFinalPlanOrigins.final_member compiled selected rfl)
    (by simpa only [signatures] using member) (matched.declaration.trans declaration.symm)
  apply Eligible.of_admissible origin matched admissible signatures
    (matched.returnComptime.trans ordinaryReturn)
  intro binder member
  apply ordinaryParameters binder.comptime
  rw [← matched.parameterComptime]
  exact List.mem_map.mpr ⟨binder, member, rfl⟩

theorem eligible_of_entry {compiled : SourceCoreUnifiedCompilation.Compiled}
    (formed : SignatureCatalogWellFormed compiled.sourceProgram.signatures)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : compiled.indexed.base.functions[index]? = some named)
    {entry : Dynamic.ProgramEntry} {heap : Dynamic.Heap} {body : Dynamic.BodyInstance}
    (matched : CallableNamedMetadata.Matches named.specialized entry.instantiation)
    (valid : Dynamic.ProgramEntryValid (Program.ofChecked compiled.sourceProgram) entry heap body)
    (ordinaryReturn : entry.instantiation.returnComptime = false)
    (ordinaryParameters : ∀ flag ∈ entry.instantiation.parameterComptime, flag = false) :
    Eligible compiled named.specialized := by
  cases valid.instantiates with
  | intro _ _ _ _ admitted _ _ _ =>
    exact eligible_of_admissible formed selected matched admitted.toAdmissible rfl
      ordinaryReturn ordinaryParameters

/-- A reached direct target obtains its Header from the actual final cache and
the original Source declaration admission. Other cached rows need no admission. -/
theorem covers_direct {compiled : SourceCoreUnifiedCompilation.Compiled}
    (catalog : Catalog compiled)
    (formed : SignatureCatalogWellFormed compiled.sourceProgram.signatures)
    {context : Context} {instantiation : DeclarationInstantiation}
    {index : Nat} {signature : SourceCoreGeneralFunctions.Signature}
    (admissible : SourceSemantics.DeclarationInstantiation.Admissible context instantiation)
    (signatures : context.signatures = compiled.sourceProgram.signatures)
    (ordinaryReturn : instantiation.returnComptime = false)
    (ordinaryParameters : ∀ flag ∈ instantiation.parameterComptime, flag = false)
    (target : SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan instantiation =
      .ok signature.key)
    (global : compiled.indexed.base.globals[index]? = some signature) :
    ∃ header ∈ CallableIndexedOwnedPreparedFiniteNamedInventories.headers catalog.rows,
      header.slot = index ∧ header.named.signature = signature := by
  rw [CallableIndexedPreparedInventories.cached_globals, List.getElem?_map] at global
  cases selected : compiled.indexed.base.functions[index]? with
  | none => simp [selected] at global
  | some named =>
    have same : named.signature = signature := by simpa [selected] using global
    have matched := CallableNamedMetadata.matches_of_exact
      (show SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan instantiation =
        .ok named.signature.key by simpa only [same] using target)
      (CallableIndexedOwnedPreparedOrdinaryCachedInputs.cached_record compiled selected)
    obtain ⟨header, member, slot, namedAt⟩ := catalog.header_at selected
      (eligible_of_admissible formed selected matched admissible signatures
        ordinaryReturn ordinaryParameters)
    exact ⟨header, member, slot, by rw [namedAt]; exact same⟩

/-- Admission is required only for the actual first matching cache row. -/
theorem selected_at_entry (catalog : Catalog compiled)
    (formed : SignatureCatalogWellFormed compiled.sourceProgram.signatures)
    {root : Root compiled}
    {publicEntry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : publicEntry ∈ compiled.indexed.entries)
    (shape : root.FactoryShape compiled publicEntry)
    {named : SourceCoreGeneralFunctions.Function} {index : Nat}
    (found : compiled.indexed.base.functions.zipIdx.find?
      (fun item => decide (item.1.signature.key = publicEntry.key)) = some (named, index))
    {entry : Dynamic.ProgramEntry} {heap : Dynamic.Heap} {body : Dynamic.BodyInstance}
    (matched : CallableNamedMetadata.Matches named.specialized entry.instantiation)
    (valid : Dynamic.ProgramEntryValid (Program.ofChecked compiled.sourceProgram) entry heap body)
    (ordinaryReturn : entry.instantiation.returnComptime = false)
    (ordinaryParameters : ∀ flag ∈ entry.instantiation.parameterComptime, flag = false) :
    ∃ header, RootSelection
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram) (headers catalog.rows) root header ∧
      CallableNamedMetadata.Matches header.named.specialized entry.instantiation := by
  have selected : compiled.indexed.base.functions[index]? = some named :=
    List.mk_mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some found)
  obtain ⟨header, retained, slot, same⟩ := catalog.header_at selected
    (eligible_of_entry formed selected matched valid
      ordinaryReturn ordinaryParameters)
  exact ⟨header, RecursiveNamedPublicRootMeaning.selection_at retained member shape found slot,
    by simpa only [same] using matched⟩

/-- The actual target equation identifies the Source entry's complete cached
row. No caller-supplied Header or whole-root coverage is needed. -/
theorem selected_entry (catalog : Catalog compiled)
    (formed : SignatureCatalogWellFormed compiled.sourceProgram.signatures)
    {root : Root compiled} (issued : root.Issued compiled)
    {entry : Dynamic.ProgramEntry} {heap : Dynamic.Heap} {body : Dynamic.BodyInstance}
    (target : SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan entry.instantiation =
      .ok root.key)
    (valid : Dynamic.ProgramEntryValid (Program.ofChecked compiled.sourceProgram) entry heap body)
    (ordinaryReturn : entry.instantiation.returnComptime = false)
    (ordinaryParameters : ∀ flag ∈ entry.instantiation.parameterComptime, flag = false) :
    ∃ header, RootSelection
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram) (headers catalog.rows) root header ∧
      CallableNamedMetadata.Matches header.named.specialized entry.instantiation := by
  obtain ⟨publicEntry, member, shape⟩ := issued
  have factory := shape
  obtain ⟨named, index, found, key, rootKey, _rest⟩ := factory
  have selected : compiled.indexed.base.functions[index]? = some named :=
    List.mk_mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some found)
  have matched := CallableNamedMetadata.matches_of_exact
    (show SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan entry.instantiation =
      .ok named.signature.key by simpa only [rootKey, key] using target)
    (CallableIndexedOwnedPreparedOrdinaryCachedInputs.cached_record compiled selected)
  exact selected_at_entry catalog formed member shape found matched valid ordinaryReturn ordinaryParameters

/-- Recover one successful public start using independent Source entry
admission and its real compiled target. The returned receipt retains the exact
current native state and the Source match for its actual selected Header. -/
theorem recover_start_entry (catalog : Catalog compiled)
    (formed : SignatureCatalogWellFormed compiled.sourceProgram.signatures)
    {recipe : Recipe} (prepared : Recipe.prepare compiled = .ok recipe)
    {nativeArtifact : Artifact} {session : Session nativeArtifact}
    (atRecipe : ArtifactRecipe nativeArtifact recipe)
    {world : StoreTyping} {store : Store} (native : session.NativeAt world store)
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicSession : SourceCoreExecution.Session publicArtifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    (atSession : publicSession.IndexedAt session)
    {key : Key} {publicArguments : List SourceCorePublicValues.Value} {fuel : Nat}
    {entry : Dynamic.ProgramEntry} {heap : Dynamic.Heap} {body : Dynamic.BodyInstance}
    (target : SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan entry.instantiation =
      .ok key)
    (valid : Dynamic.ProgramEntryValid (Program.ofChecked compiled.sourceProgram) entry heap body)
    (ordinaryReturn : entry.instantiation.returnComptime = false)
    (ordinaryParameters : ∀ flag ∈ entry.instantiation.parameterComptime, flag = false)
    (accepted : publicSession.start key publicArguments fuel = .ok publicCheckpoint) :
    ∃ request : Started (headers catalog.rows) prepared publicCheckpoint session key publicArguments fuel world store,
      CallableNamedMetadata.Matches request.header.named.specialized entry.instantiation := by
  apply RecursiveNamedPublicPhysicalFrontdoor.recover_start_at_with prepared catalog.inputs catalog.rows
    atRecipe native atSession (fun _ header =>
      CallableNamedMetadata.Matches header.named.specialized entry.instantiation) _ accepted
  intro root selected
  have sameCompiled := Recipe.prepare_compiled prepared
  cases sameCompiled
  change recipe.roots.find? (fun candidate => decide (candidate.key = key)) = some root at selected
  have issued := Recipe.prepare_roots prepared (List.mem_of_find?_eq_some selected)
  have keyEq : root.key = key := by simpa only [decide_eq_true_eq] using (List.find?_some selected)
  exact selected_entry catalog formed issued (by simpa only [keyEq] using target)
    valid ordinaryReturn ordinaryParameters


end Solcore.SourceSemantics.CoreLowering.SelectedCompilationCatalogFrontdoor
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodCertificateTransport
/-! Actual checker headers align a shared instantiated body certificate with
the exact method selected by Source execution. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodCertificateTransport
open Frontend SourceInference TypeSystem
open Solcore.SourceSemantics.Dynamic

theorem of_body {program : CheckedProgram} {raw : Workspace.RawWorkspace} {fuel : Nat}
    (checked : Frontend.checkProgram raw fuel = .ok program)
    {implementation : ProgramImplementationSignature} {method : ProgramImplMethodSignature}
    {trait : ProgramTraitSignature} {definition : MethodDefinition}
    {substitution : ParameterSubstitution} {body : BodyInstance}
    {inputTypes : List Ty} {lexical : Context} {facts : BodyFacts}
    (instantiates : TraitMethodInstantiates (Program.ofChecked program)
      implementation method trait definition substitution body)
    (certificate : BodyInstanceTypingCertificate (Program.ofChecked program)
      body inputTypes lexical facts) :
    TraitMethodInstanceTypingCertificate (Program.ofChecked program)
      method substitution definition body inputTypes lexical facts := by
  cases instantiates with
  | intro implementationMember methodMember _ _ definitionMember definitionId _ _ _ sourceEq resultEq _ =>
    obtain ⟨retained, retainedMember, rfl⟩ := List.mem_map.mp definitionMember
    obtain ⟨checkedImplementation, checkedMethod, checkedTrait, checkedImplementationMember,
      checkedMethodMember, _, checkedId, header⟩ :=
      checkedMethodHeaderWellFormed_ofCheckProgram checked retainedMember
    have catalog := SignatureCatalogWellFormed.ofCheckProgram checked
    have methodIds : ((program.signatures.implementations.flatMap (fun item => item.methods)).map
        (fun item => item.id)).Nodup := by
      simpa [List.map_flatMap, Function.comp_def] using catalog.implementation_method_ids
    have sameMethod : checkedMethod = method :=
      StructuralSubstitution.eq_of_mem_of_mapped_nodup methodIds
        (List.mem_flatMap.mpr ⟨checkedImplementation, checkedImplementationMember, checkedMethodMember⟩)
        (List.mem_flatMap.mpr ⟨implementation, implementationMember, methodMember⟩)
        (checkedId.symm.trans definitionId)
    subst checkedMethod
    obtain ⟨genericLexical, genericInputs⟩ := header.inputs_extend
    have genericTypes : retained.checked.typedBody.inputs.map (fun binder => binder.scheme.body) =
        method.parameterTypes := MonoBindersExtend.bodyTypes_eq genericInputs
    have types : inputTypes = method.parameterTypes.map substitution.apply := by
      rw [← MonoBindersExtend.bodyTypes_eq certificate.typing.inputs_extend, sourceEq]
      change ((StructuralSubstitution.applyTypedSource substitution retained.checked.typedBody).inputs.map
        (fun binder => binder.scheme.body)) = _
      simp only [StructuralSubstitution.applyTypedSource, List.map_map, Function.comp_def,
        StructuralSubstitution.applyBinder, StructuralSubstitution.applyScheme]
      simpa only [List.map_map, Function.comp_def] using congrArg (List.map substitution.apply) genericTypes
    have result : body.resultType = substitution.apply (Ty.productMany method.returnTypes) := by
      rw [resultEq]
      exact congrArg substitution.apply header.result_type
    refine { certificate with input_types_eq := types, result_type_eq := result, callable_type := ?_ }
    change substitution.apply retained.checked.type = _
    rw [header.callable_type]
    change Ty.function (substitution.apply (Ty.productMany method.parameterTypes))
      (substitution.apply (Ty.productMany method.returnTypes)) = _
    rw [StructuralSubstitution.apply_productMany, ← types, ← result]

theorem selected {program : CheckedProgram} {raw : Workspace.RawWorkspace} {fuel : Nat}
    (checked : Frontend.checkProgram raw fuel = .ok program)
    {context : Context} {evidence dictionary : EvidenceEnvironment}
    {traitName methodName : String} {requirements : List RequirementId} {body : BodyInstance}
    (selection : OperatorMethodSelected (Program.ofChecked program) context evidence
      traitName methodName requirements body dictionary)
    (certificate : ∃ inputTypes lexical facts,
      BodyInstanceTypingCertificate (Program.ofChecked program) body inputTypes lexical facts) :
    TypedOperatorMethodSelected (Program.ofChecked program) context evidence
      traitName methodName requirements body dictionary := by
  obtain ⟨inputTypes, lexical, facts, certificate⟩ := certificate
  cases selection with
  | intro selects closed implementation trait traitName goal head method methodName owner
      requirements instantiates assembled covers =>
    exact .intro selects closed implementation trait traitName goal head method methodName owner
      requirements instantiates assembled covers ⟨inputTypes, lexical, facts, of_body checked instantiates certificate⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodCertificateTransport
end
