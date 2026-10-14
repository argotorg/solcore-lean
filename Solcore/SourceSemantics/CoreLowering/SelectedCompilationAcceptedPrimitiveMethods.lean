import Solcore.SourceSemantics.CoreLowering.AcceptedMethodBodyAdmission
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPrimitiveMethodAdmission

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
