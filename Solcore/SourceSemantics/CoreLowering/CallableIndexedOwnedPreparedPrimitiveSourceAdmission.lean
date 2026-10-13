import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPrimitiveMethodTerminalSupport

/-! Bounded admission reads original expression nodes and their metadata.
The native metadata scan covers the whole admitted grammar. Declaration calls
are excluded by the empty direct-site criterion, so their original coercion
and requirement rows remain available to a separate parent certificate. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPrimitiveSourceAdmission
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)
open CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles (NativeMetadataFor SupportedForm)
open CallableIndexedOwnedPreparedStagedPrimitiveMethodTerminalSupport (PrimitiveSource)

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

/-- This recognizer constructs syntax from the original lookups. Its budget
bounds graph traversal; it has no runtime or semantic inventory input. -/
def expression? (source : TypedSource) :
    (fuel : Nat) → (id : ExpressionId) → Option (PLift (GeneralSyntax source id (fun _ => False)))
  | 0, _ => none
  | fuel + 1, id =>
      match found : source.lookupExpression? id with
      | none => none
      | some node =>
          match form : node.form with
          | .reference _name (.local _binder) => some ⟨.leaf (.read found form)⟩
          | .reference name (.builtinBoolean value) => some ⟨.leaf (.literal found (form ▸ .bool name value))⟩
          | .literal literal => some ⟨.leaf (.literal found (form ▸ .word literal))⟩
          | .integerLiteral literal resolution => some ⟨.leaf (.literal found (form ▸ .integer literal resolution))⟩
          | .tuple [] => some ⟨.leaf (.literal found (form ▸ .unit))⟩
          | .group inner => do
              let ⟨child⟩ ← expression? source fuel inner
              pure ⟨.group found form child⟩
          | .conditional condition first second => do
              let ⟨test⟩ ← expression? source fuel condition
              let ⟨yes⟩ ← expression? source fuel first
              let ⟨no⟩ ← expression? source fuel second
              pure ⟨.conditional found form test yes no⟩
          | _ => none

private def PrimitiveForm (form : ExpressionForm) : Prop :=
  (∃ name resolution, form = .reference name resolution) ∨
  (∃ spelling resolution, form = .integerLiteral spelling resolution) ∨
  (∃ condition first second, form = .conditional condition first second)

private def primitiveNode? (node : SourceInference.Node) :
    Option (PLift (∀ expression, node = .expression expression → PrimitiveForm expression.form)) :=
  match node with
  | .statement _ => some ⟨by intro expression impossible; cases impossible⟩
  | .expression expression =>
      match form : expression.form with
      | .reference name resolution =>
          some ⟨by intro actual same; cases same; exact .inl ⟨name, resolution, form⟩⟩
      | .integerLiteral literal resolution =>
          some ⟨by intro actual same; cases same; exact .inr (.inl ⟨literal, resolution, form⟩)⟩
      | .conditional condition first second =>
          some ⟨by intro actual same; cases same; exact .inr (.inr ⟨condition, first, second, form⟩)⟩
      | _ => none

/-- The terminal-method profile is deliberately narrower than expression
admission: every original expression must be a reference, integer or conditional. -/
def primitiveSource? (source : TypedSource) : Option (PLift (PrimitiveSource source)) := do
  let ⟨all⟩ ← allProof? (fun node => ∀ expression, node = .expression expression →
    PrimitiveForm expression.form) primitiveNode? source.nodes
  pure ⟨by
    intro id node found
    exact all _ (lookupExpression?_sound found).1 node rfl⟩

def NativeMetadataTest {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked)
    (named : SourceCoreGeneralFunctions.Function) (node : ExpressionNode) : Prop :=
  node.coercions = [] ∧
  prepared.base.locals.bindings.find? (fun binding => decide
    (binding.caller = (CallableIndexedNamedGeneration.context prepared named).owner ∧ binding.initializer = node.id)) = none ∧
  (match node.form with | .integerLiteral _ _ => True | _ => node.requirements = []) ∧
  (match node.form with | .call _ _ (.indirect metadata) => metadata.argumentCoercions = [] | _ => True) ∧
  (match node.form with
    | .reference _ (.local binder) => prepared.base.locals.bindings.any (fun binding => decide
        (binding.caller = (CallableIndexedNamedGeneration.context prepared named).owner ∧ binding.binder.id = binder)) = false
    | _ => True)

private instance nativeMetadataTestDecidable {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked)
    (named : SourceCoreGeneralFunctions.Function) (node : ExpressionNode) :
    Decidable (NativeMetadataTest prepared named node) := by
  unfold NativeMetadataTest
  cases node.form <;> try infer_instance
  case reference name resolution => cases resolution <;> infer_instance
  case call callee ids resolution => cases resolution <;> infer_instance

private def relevantForm : ExpressionForm → Bool
  | .reference _ (.local _) | .reference _ (.builtinBoolean _) | .literal _ | .integerLiteral _ _
    | .unary _ _ | .binary _ _ _ | .index _ _ | .conditional _ _ _ | .group _ | .tuple _
    | .constructor _ _ | .call _ _ (.builtinFunction _) | .call _ _ (.indirect _) => true
  | _ => false

private theorem relevant_of_supported {form : ExpressionForm}
    (supported : SupportedForm form)
    (noDirect : ∀ callee ids instantiation, form = .call callee ids (.declaration instantiation) → False) :
    relevantForm form = true := by
  cases supported with
  | literal atomic => cases atomic <;> rfl
  | direct callee ids instantiation => exact False.elim (noDirect callee ids instantiation rfl)
  | read | unary | binary | index | conditional | group | tuple | constructor | builtin | call => rfl

private def nativeNodeMetadata? {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked)
    (named : SourceCoreGeneralFunctions.Function) (node : SourceInference.Node) :
    Option (PLift (∀ expression, node = .expression expression →
      relevantForm expression.form = true → NativeMetadataTest prepared named expression)) :=
  match node with
  | .expression expression =>
      if relevant : relevantForm expression.form = true then
        if accepted : NativeMetadataTest prepared named expression then
          some ⟨by intro actual same _; cases same; exact accepted⟩
        else none
      else some ⟨by intro actual same supported; cases same; exact False.elim (relevant supported)⟩
  | .statement _ => some ⟨by intro expression impossible; cases impossible⟩

/-- Native metadata for the empty direct-site grammar. The scanner examines
all relevant nodes, including unused ones. Integer evidence is preserved;
no other admitted node may carry requirements or output coercions. -/
def nativeMetadata? {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked)
    (named : SourceCoreGeneralFunctions.Function) (source : TypedSource) :
    Option (PLift (NativeMetadataFor prepared named source (fun _ => False))) := do
  let ⟨all⟩ ← allProof? (fun node => ∀ expression, node = .expression expression →
    relevantForm expression.form = true → NativeMetadataTest prepared named expression)
    (nativeNodeMetadata? prepared named) source.nodes
  have metadataAt : ∀ id, GeneralSyntax source id (fun _ => False) → ∀ node,
      source.lookupExpression? id = some node → NativeMetadataTest prepared named node := by
    intro id tree node found
    obtain ⟨original, originalFound, supported⟩ :=
      CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles.syntax_node tree
    cases Option.some.inj (originalFound.symm.trans found)
    exact all _ (lookupExpression?_sound found).1 node rfl
      (relevant_of_supported supported (fun _ _ _ form => tree.direct_site found form))
  pure ⟨{
    requirements := by
      intro id tree node found
      have accepted := (metadataAt id tree node found).2.2.1
      cases form : node.form <;> simp only [form] at accepted
      all_goals try exact .inl accepted
      case integerLiteral literal resolution => exact .inr ⟨literal, resolution, rfl⟩
    coercions := fun id tree node found => (metadataAt id tree node found).1
    initializer := by
      intro id tree
      obtain ⟨node, found⟩ := GeneralSyntax.syntax_found tree
      have nodeId := (lookupExpression?_sound found).2
      simpa only [nodeId] using (metadataAt id tree node found).2.1
    arguments := by
      intro id tree node found callee ids metadata form
      simpa only [form] using (metadataAt id tree node found).2.2.2.1
    directCaller := by
      intro id tree node found callee ids instantiation form
      exact False.elim (tree.direct_site found form)
    localRead := by
      intro id tree node found name binder form
      simpa only [form] using (metadataAt id tree node found).2.2.2.2 }⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPrimitiveSourceAdmission
