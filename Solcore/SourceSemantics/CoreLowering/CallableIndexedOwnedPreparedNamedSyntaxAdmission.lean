import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryCachedInputs
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedPhysicalMixedScopedCollectors

/-! Executable admission of original named source. The bounded scanner retains
actual lookups and complete declaration metadata. It constructs static syntax
and metadata receipts; no execution or body correspondence is a test. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedSyntaxAdmission
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)
open CallableIndexedOwnedPreparedStagedDirectCallCertificates (Supported)

/-- Exact ordinary inventory rows, including all retained raw replacements,
authenticate admitted direct sites. The range test is independent of native types. -/
def DirectSite (rows : List SourceSpecialization.SpecializedFunction)
    (instantiation : DeclarationInstantiation) : Prop :=
  ∃ row ∈ rows, instantiation = CallableNamedCanonicalOrder.retainedInstantiation row ∧
    CompatibleSourceInstantiationClosure.ClosedParameterRange instantiation.parameterSubstitution

/-- The executable table stores ordinary compiler data. Its later connection
to the semantic inventory is a proof and is never evaluated by the scanner. -/
def TableAligned {compiled : SourceCoreUnifiedCompilation.Compiled}
    (inputs : List (Input compiled)) (rows : List SourceSpecialization.SpecializedFunction) : Prop :=
  ∀ row ∈ rows, ∃ input ∈ inputs, input.row = row

theorem TableAligned.empty {compiled : SourceCoreUnifiedCompilation.Compiled}
    (inputs : List (Input compiled)) : TableAligned inputs [] := by
  intro row member
  cases member

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

private def closedRange? (substitution : TypeSystem.ParameterSubstitution) :
    Option (PLift (CompatibleSourceInstantiationClosure.ClosedParameterRange substitution)) :=
  if closed : substitution.all (fun item => SourceCoreDataCatalog.closed item.2) = true then
    some ⟨by intro parameter replacement member; exact List.all_eq_true.mp closed _ member⟩
  else none

def directSite?
    (inputs : List SourceSpecialization.SpecializedFunction) (instantiation : DeclarationInstantiation) :
    Option (PLift (DirectSite inputs instantiation)) := do
  let ⟨closed⟩ ← closedRange? instantiation.parameterSubstitution
  let rec find (remaining : List SourceSpecialization.SpecializedFunction) :
      Option (PLift (∃ input ∈ remaining,
        instantiation = CallableNamedCanonicalOrder.retainedInstantiation input)) :=
    match remaining with
    | [] => none
    | input :: rest =>
        if same : instantiation = CallableNamedCanonicalOrder.retainedInstantiation input then
          some ⟨⟨input, List.mem_cons_self, same⟩⟩
        else do
          let ⟨found⟩ ← find rest
          pure ⟨by obtain ⟨actual, member, same⟩ := found; exact ⟨actual, List.mem_cons_of_mem _ member, same⟩⟩
  let ⟨found⟩ ← find inputs
  pure ⟨by obtain ⟨input, member, same⟩ := found; exact ⟨input, member, same, closed⟩⟩

theorem DirectSite.supported {compiled : SourceCoreUnifiedCompilation.Compiled}
    {inputs : List (Input compiled)} {rawRows : List SourceSpecialization.SpecializedFunction}
    (aligned : TableAligned inputs rawRows) {instantiation : DeclarationInstantiation}
    (site : DirectSite rawRows instantiation) : Supported compiled.indexed.base.plan instantiation := by
  obtain ⟨row, member, same, range⟩ := site
  obtain ⟨input, _member, rowEq⟩ := aligned row member
  subst row
  refine ⟨range, ?_⟩
  intro key row target record
  rw [same] at target
  have keyEq := Except.ok.inj (target.symm.trans input.target)
  subst key
  have actual := CallableIndexedOwnedPreparedOrdinaryCachedInputs.cached_record compiled input.prepared.selected
  have rowEq := (Except.ok.inj (record.symm.trans actual)).trans input.prepared.same
  subst row
  simp only [same, CallableNamedCanonicalOrder.retainedInstantiation, List.map_reverse]

theorem DirectSite.covered {compiled : SourceCoreUnifiedCompilation.Compiled}
    {inputs : List (Input compiled)} (rows : Inventory inputs)
    {rawRows : List SourceSpecialization.SpecializedFunction} (aligned : TableAligned inputs rawRows)
    {instantiation : DeclarationInstantiation} (site : DirectSite rawRows instantiation)
    {index : Nat} {signature : SourceCoreCalls.Signature}
    (target : SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan instantiation = .ok signature.key)
    (global : compiled.indexed.base.globals[index]? = some signature) :
    ∃ header ∈ headers rows, header.slot = index ∧ header.named.signature = signature := by
  obtain ⟨row, rowMember, same, _range⟩ := site
  obtain ⟨input, member, rowEq⟩ := aligned row rowMember
  subst row
  have keys := Except.ok.inj ((same ▸ target).symm.trans input.target)
  have selected : (signature, index) ∈ compiled.indexed.base.globals.zipIdx.filter
      (fun item => decide (item.1.key = input.prepared.named.signature.key)) :=
    List.mem_filter.mpr ⟨List.mk_mem_zipIdx_iff_getElem?.mpr global, by simpa using keys⟩
  rw [input.slot] at selected
  have samePair := List.mem_singleton.mp selected
  obtain ⟨packet, retained⟩ := rows.row_at input member
  exact ⟨packet.header, Inventory.header_member retained,
    packet.aligned.slot.trans (congrArg Prod.snd samePair).symm,
    (congrArg (·.signature) packet.aligned.named).trans (congrArg Prod.fst samePair).symm⟩

/-- Fuel bounds traversal of the original graph; failed admission adds no
hypothesis and does not alter any node or compiler metadata. -/
def expression?
    (inputs : List SourceSpecialization.SpecializedFunction) (source : TypedSource) :
    (fuel : Nat) → (id : ExpressionId) → Option (PLift (GeneralSyntax source id (DirectSite inputs)))
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
              let ⟨child⟩ ← expression? inputs source fuel inner
              pure ⟨.group found form child⟩
          | .call _callee ids (.declaration instantiation) => do
              let ⟨site⟩ ← directSite? inputs instantiation
              let ⟨children⟩ ← allProof? (fun child => GeneralSyntax source child (DirectSite inputs))
                (expression? inputs source fuel) ids
              pure ⟨.direct found form site children⟩
          | .call callee ids (.indirect _metadata) => do
              let ⟨function⟩ ← expression? inputs source fuel callee
              let ⟨children⟩ ← allProof? (fun child => GeneralSyntax source child (DirectSite inputs))
                (expression? inputs source fuel) ids
              pure ⟨.call found form function children⟩
          | _ => none

def MetadataTest {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked)
    (named : SourceCoreGeneralFunctions.Function) (node : ExpressionNode) : Prop :=
  node.coercions = [] ∧
  prepared.base.locals.bindings.find? (fun binding => decide
    (binding.caller = (CallableIndexedNamedGeneration.context prepared named).owner ∧ binding.initializer = node.id)) = none ∧
  (match node.form with
    | .integerLiteral _ _ | .call _ _ (.declaration _) | .unary _ _ | .binary _ _ _ => True
    | _ => node.requirements = []) ∧
  (match node.form with | .call _ _ (.indirect metadata) => metadata.argumentCoercions = [] | _ => True) ∧
  (match node.form with
    | .reference _ (.local binder) => prepared.base.locals.bindings.any (fun binding => decide
        (binding.caller = (CallableIndexedNamedGeneration.context prepared named).owner ∧ binding.binder.id = binder)) = false
    | _ => True)

private instance metadataTestDecidable {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked)
    (named : SourceCoreGeneralFunctions.Function) (node : ExpressionNode) :
    Decidable (MetadataTest prepared named node) := by
  unfold MetadataTest
  cases node.form <;> try infer_instance
  case reference name resolution => cases resolution <;> infer_instance
  case call callee ids resolution => cases resolution <;> infer_instance

private def relevantForm : ExpressionForm → Bool
  | .reference _ (.local _) | .reference _ (.builtinBoolean _) | .literal _ | .integerLiteral _ _
    | .unary _ _ | .binary _ _ _ | .index _ _ | .conditional _ _ _ | .group _ | .tuple _
    | .constructor _ _ | .call _ _ (.builtinFunction _) | .call _ _ (.declaration _)
    | .call _ _ (.indirect _) => true
  | _ => false

private theorem relevant_of_supported {form : ExpressionForm}
    (supported : CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles.SupportedForm form) :
    relevantForm form = true := by
  cases supported with
  | literal atomic => cases atomic <;> rfl
  | read | unary | binary | index | conditional | group | tuple | constructor | builtin | direct | call => rfl

private def nodeMetadata? {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked)
    (named : SourceCoreGeneralFunctions.Function) (node : SourceInference.Node) :
    Option (PLift (∀ expression, node = .expression expression →
      relevantForm expression.form = true → MetadataTest prepared named expression)) :=
  match node with
  | .expression expression =>
      if relevant : relevantForm expression.form = true then
        if accepted : MetadataTest prepared named expression then
          some ⟨by intro actual same _; cases same; exact accepted⟩
        else none
      else some ⟨by intro actual same supported; cases same; exact False.elim (relevant supported)⟩
  | .statement _ => some ⟨by intro expression impossible; cases impossible⟩

/-- Every lookupable node in the admitted global grammar is checked, including
unused nodes. Unsupported forms have no GeneralSyntax witness and are skipped. -/
def metadata? {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked)
    (named : SourceCoreGeneralFunctions.Function) (source : TypedSource)
    (directSites : DeclarationInstantiation → Prop) :
    Option (PLift (CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
      prepared named source directSites)) := do
  let ⟨all⟩ ← allProof? (fun node => ∀ expression, node = .expression expression →
    relevantForm expression.form = true → MetadataTest prepared named expression) (nodeMetadata? prepared named) source.nodes
  have metadataAt : ∀ id, GeneralSyntax source id directSites → ∀ node,
      source.lookupExpression? id = some node → MetadataTest prepared named node := by
    intro id tree node found
    obtain ⟨original, originalFound, supported⟩ :=
      CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles.syntax_node tree
    cases Option.some.inj (originalFound.symm.trans found)
    exact all _ (lookupExpression?_sound found).1 node rfl (relevant_of_supported supported)
  pure ⟨{
    coercions := fun id tree node found => (metadataAt id tree node found).1
    initializer := by
      intro id tree
      obtain ⟨node, found⟩ := GeneralSyntax.syntax_found tree
      have nodeId := (lookupExpression?_sound found).2
      simpa only [nodeId] using (metadataAt id tree node found).2.1
    requirements := by
      intro id tree node found
      have accepted := (metadataAt id tree node found).2.2.1
      cases form : node.form <;> simp only [form] at accepted
      all_goals try exact .inl accepted
      case integerLiteral literal resolution => exact .inr (.inl ⟨literal, resolution, rfl⟩)
      case unary operator operand => exact .inr (.inr (.inr True.intro))
      case binary left operator right => exact .inr (.inr (.inr True.intro))
      case call callee ids resolution =>
        cases resolution <;> simp only at accepted
        all_goals try exact .inl accepted
        case declaration instantiation => exact .inr (.inr (.inl ⟨callee, ids, instantiation, rfl⟩))
    arguments := by
      intro id tree node found callee ids callMetadata form
      simpa only [form] using (metadataAt id tree node found).2.2.2.1
    localRead := by
      intro id tree node found name binder form
      simpa only [form] using (metadataAt id tree node found).2.2.2.2 }⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedSyntaxAdmission
