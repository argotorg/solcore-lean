import Solcore.SourceSemantics.CoreLowering.AcceptedNamedExpressionBoundaryExclusion

/-! Flat checks of actual source nodes and operand edges supply the finite
facts used to close accepted compiler traces. Static declaration references
are excluded from the reached set; declaration calls retain only arguments.
This profile constructs no recursive expression grammar. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.AcceptedCompilerExpressionProfile
open Core Frontend SourceInference
open CallableIndexedNamedGeneration
open AcceptedNamedExpressionFlow
open CallableIndexedOwnedPreparedNamedSyntaxAdmission (DirectSite MetadataTest metadata? directSite?)
open CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles (MetadataFor)

/-- The restricted lane is used by existing direct/read method and closure
producers. The general lane additionally accepts indirect and method calls. -/
def supportedForm (directOnly : Bool) : ExpressionForm → Bool
  | .reference _ (.local _) | .reference _ (.builtinBoolean _)
    | .literal _ | .integerLiteral _ _ | .tuple []
    | .call _ _ (.declaration _) => true
  | .call _ _ (.indirect _) | .unary _ _ | .binary _ _ _ => !directOnly
  | _ => false

/-- These are operand positions in their actual evaluation order. A direct
callee is a static declaration reference, while an indirect callee is first. -/
def operands : ExpressionForm → List ExpressionId
  | .call _ arguments (.declaration _) => arguments
  | .call callee arguments (.indirect _) => callee :: arguments
  | .unary _ operand => [operand]
  | .binary left _ right => [left, right]
  | _ => []

def supportedIds (source : TypedSource) (directOnly : Bool) : List ExpressionId :=
  source.nodes.filterMap fun node => match node with
    | .expression expression => if supportedForm directOnly expression.form then some expression.id else none
    | .statement _ => none

private theorem supported_mem {source : TypedSource} {directOnly : Bool}
    {id : ExpressionId} {node : ExpressionNode}
    (found : source.lookupExpression? id = some node)
    (supported : supportedForm directOnly node.form = true) : id ∈ supportedIds source directOnly := by
  obtain ⟨member, same⟩ := lookupExpression?_sound found
  apply List.mem_filterMap.mpr
  refine ⟨.expression node, member, ?_⟩
  simp only [supported, ↓reduceIte]
  exact congrArg some same

private theorem form_of_supported {directOnly : Bool} {form : ExpressionForm}
    (supported : supportedForm directOnly form = true) :
    LeafForm form ∨ DirectForm form ∨
      (directOnly = false ∧ (IndirectForm form ∨ MethodForm form)) := by
  match form with
  | .reference name (.local binder) => exact .inl (.read name binder)
  | .reference name (.builtinBoolean value) => exact .inl (.literal (.bool name value))
  | .literal literal => exact .inl (.literal (.word literal))
  | .integerLiteral literal resolution => exact .inl (.literal (.integer literal resolution))
  | .tuple [] => exact .inl (.literal .unit)
  | .call callee arguments (.declaration instantiation) => exact .inr (.inl ⟨callee, arguments, instantiation, rfl⟩)
  | .call callee arguments (.indirect metadata) =>
      exact .inr (.inr ⟨(by cases directOnly <;> simp_all [supportedForm]), .inl ⟨callee, arguments, metadata, rfl⟩⟩)
  | .unary operator operand =>
      exact .inr (.inr ⟨(by cases directOnly <;> simp_all [supportedForm]), .inr (.inl ⟨operator, operand, rfl⟩)⟩)
  | .binary left operator right =>
      exact .inr (.inr ⟨(by cases directOnly <;> simp_all [supportedForm]), .inr (.inr ⟨operator, left, right, rfl⟩)⟩)
  | .reference name resolution =>
      cases resolution with
      | «local» binder => exact .inl (.read name binder)
      | builtinBoolean value => exact .inl (.literal (.bool name value))
      | _ => cases supported
  | .tuple (_ :: _) | .group _ | .index _ _ | .conditional _ _ _
    | .constructor _ _ | .call _ _ (.builtinFunction _) | .lambda _ _ _ => cases supported

private theorem policy_supported {directOnly : Bool} {form : ExpressionForm}
    (supported : supportedForm directOnly form = true) :
    CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles.SupportedForm form := by
  rcases form_of_supported supported with leaf | ⟨callee, args, instantiation, rfl⟩ | ⟨_, rest⟩
  · rcases leaf.view with atomic | ⟨name, binder, rfl⟩
    · exact .literal atomic
    · exact .read name binder
  · exact .direct callee args instantiation
  · rcases rest with ⟨callee, args, metadata, rfl⟩ | method
    · exact .call callee args metadata
    · rcases method with ⟨operator, operand, rfl⟩ | ⟨operator, left, right, rfl⟩
      · exact .unary operator operand
      · exact .binary left operator right

def SiteReady (rows : List SourceSpecialization.SpecializedFunction) (node : ExpressionNode) : Prop :=
  match node.form with
  | .call _ _ (.declaration instantiation) => DirectSite rows instantiation
  | _ => True

def RequirementsReady (node : ExpressionNode) : Prop :=
  match node.form with
  | .unary _ _ | .binary _ _ _ => node.requirements ≠ []
  | _ => True

private def site? (rows : List SourceSpecialization.SpecializedFunction) (node : ExpressionNode) :
    Option (PLift (SiteReady rows node)) := by
  cases form : node.form with
  | call callee arguments resolution =>
      cases resolution with
      | declaration instantiation =>
          exact (directSite? rows instantiation).map fun site => ⟨by simpa only [SiteReady, form] using site.down⟩
      | _ => exact some ⟨by simp [SiteReady, form]⟩
  | _ => exact some ⟨by simp [SiteReady, form]⟩

private def requirements? (node : ExpressionNode) : Option (PLift (RequirementsReady node)) := by
  cases form : node.form with
  | unary _ _ | binary _ _ _ =>
      exact if present : node.requirements ≠ [] then some ⟨by simpa only [RequirementsReady, form] using present⟩ else none
  | _ => exact some ⟨by simp [RequirementsReady, form]⟩

/-- All facts refer to the node selected by the actual source lookup. -/
def NodeReady (source : TypedSource) (rows : List SourceSpecialization.SpecializedFunction)
    (directOnly : Bool) (id : ExpressionId) : Prop :=
  ∃ node, source.lookupExpression? id = some node ∧ supportedForm directOnly node.form = true ∧
    (∀ child ∈ operands node.form, child ∈ supportedIds source directOnly) ∧
    SiteReady rows node ∧ RequirementsReady node

private def node? (source : TypedSource) (rows : List SourceSpecialization.SpecializedFunction)
    (directOnly : Bool) (id : ExpressionId) : Option (PLift (NodeReady source rows directOnly id)) := do
  match found : source.lookupExpression? id with
  | none => none
  | some node =>
    if supported : supportedForm directOnly node.form = true then do
      if edges : (operands node.form).all (fun child => decide (child ∈ supportedIds source directOnly)) = true then do
        let ⟨site⟩ ← site? rows node
        let ⟨requirements⟩ ← requirements? node
        pure ⟨⟨node, found, supported, by
          intro child member
          exact of_decide_eq_true (List.all_eq_true.mp edges child member), site, requirements⟩⟩
      else none
    else none

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

structure Profile {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked) (named : Named)
    (source : TypedSource) (rows : List SourceSpecialization.SpecializedFunction)
    (directOnly : Bool := false) : Type where
  nodes : ∀ id ∈ supportedIds source directOnly, NodeReady source rows directOnly id
  metadataAccepted : ∃ receipt : PLift (MetadataFor prepared named source (DirectSite rows)),
    metadata? prepared named source (DirectSite rows) = some receipt

namespace Profile
variable {checked : SourceCoreCompatibleCatalog.Checked}
  {prepared : CallableIndexedNamedGeneration.Prepared checked} {named : Named}
  {source : TypedSource} {rows : List SourceSpecialization.SpecializedFunction} {directOnly : Bool}

abbrev ids (_profile : Profile prepared named source rows directOnly) : List ExpressionId := supportedIds source directOnly
abbrev Reached (profile : Profile prepared named source rows directOnly) (id : ExpressionId) : Prop := id ∈ profile.ids

private theorem at_node (profile : Profile prepared named source rows directOnly) {id : ExpressionId} {node : ExpressionNode}
    (reached : profile.Reached id) (found : source.lookupExpression? id = some node) :
    supportedForm directOnly node.form = true ∧
    (∀ child ∈ operands node.form, profile.Reached child) ∧ SiteReady rows node ∧ RequirementsReady node := by
  obtain ⟨actual, selected, rest⟩ := profile.nodes id reached
  cases Option.some.inj (selected.symm.trans found)
  exact rest

theorem metadata (profile : Profile prepared named source rows directOnly) : MetadataFor prepared named source (DirectSite rows) := by
  obtain ⟨receipt, _accepted⟩ := profile.metadataAccepted
  exact receipt.down

theorem covered (profile : Profile prepared named source rows directOnly) (id : ExpressionId) (node : ExpressionNode)
    (found : source.lookupExpression? id = some node)
    (callee : ExpressionId) (arguments : List ExpressionId) (instantiation : DeclarationInstantiation)
    (form : node.form = .call callee arguments (.declaration instantiation)) : DirectSite rows instantiation := by
  have member := supported_mem found (show supportedForm directOnly node.form = true by simp only [form, supportedForm])
  have facts := profile.at_node member found
  simpa only [SiteReady, form] using facts.2.2.1

theorem forms (profile : Profile prepared named source rows directOnly) : ReachedMethodForms source profile.Reached := by
  intro id node reached found
  rcases form_of_supported (profile.at_node reached found).1 with leaf | direct | ⟨_, rest⟩
  · exact .inl leaf
  · exact .inr (.inl direct)
  · exact .inr (.inr rest)

theorem arguments (profile : Profile prepared named source rows directOnly) : ReachedMethodArguments source profile.Reached := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro id node reached found callee arguments instantiation form child member
    exact (profile.at_node reached found).2.1 child (by simpa only [operands, form] using member)
  · intro id node reached found callee arguments metadata form
    have edges := (profile.at_node reached found).2.1
    refine ⟨edges callee ?_, ?_⟩
    · simp only [form, operands, List.mem_cons_self]
    · intro child member
      exact edges child (by simp only [form, operands, List.mem_cons]; exact .inr member)
  · intro id node reached found operator operand form
    exact (profile.at_node reached found).2.1 operand (by simp only [form, operands, List.mem_singleton])
  · intro id node reached found operator left right form
    have edges := (profile.at_node reached found).2.1
    exact ⟨edges left (by simp [form, operands]), edges right (by simp [form, operands])⟩

theorem requirements (profile : Profile prepared named source rows directOnly) : ReachedMethodRequirements source profile.Reached := by
  intro id node reached found method
  have facts := (profile.at_node reached found).2.2.2
  rcases method with ⟨operator, operand, form⟩ | ⟨operator, left, right, form⟩
  · simpa only [RequirementsReady, form] using facts
  · simpa only [RequirementsReady, form] using facts

theorem rawMetadata (profile : Profile prepared named source rows directOnly) : ReachedMethodMetadata prepared named source profile.Reached := by
  obtain ⟨receipt, accepted⟩ := profile.metadataAccepted
  exact ReachedMethodMetadata.of_accepted accepted

theorem noInitializer (profile : Profile prepared named source rows directOnly) (id : ExpressionId) (reached : profile.Reached id) :
    ¬ Nonempty (AcceptedContextualDirectReceipt.InitializerAt prepared (context prepared named) id) := by
  obtain ⟨node, found, supported, _rest⟩ := profile.nodes id reached
  obtain ⟨receipt, accepted⟩ := profile.metadataAccepted
  have raw := AcceptedNamedExpressionMetadata.at_of_accepted accepted found (policy_supported supported)
  have empty := raw.2.1
  rw [(lookupExpression?_sound found).2] at empty
  rintro ⟨initializer⟩
  have impossible := initializer.found
  rw [empty] at impossible
  cases impossible

theorem directForms (profile : Profile prepared named source rows true) : ReachedForms source profile.Reached := by
  intro id node reached found
  rcases form_of_supported (profile.at_node reached found).1 with leaf | direct | ⟨impossible, _⟩
  · exact .inl leaf
  · exact .inr direct
  · cases impossible

theorem directArguments (profile : Profile prepared named source rows true) : ReachedArguments source profile.Reached :=
  profile.arguments.1.1

end Profile

/-- Only finite tables are traversed. Child closure is checked against the
flat set, and all original metadata checks run on the unchanged source. -/
def certify {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked) (named : Named)
    (source : TypedSource) (rows : List SourceSpecialization.SpecializedFunction)
    (directOnly : Bool := false) : Option (Profile prepared named source rows directOnly) := do
  let ⟨nodes⟩ ← allProof? (NodeReady source rows directOnly) (node? source rows directOnly)
    (supportedIds source directOnly)
  match accepted : metadata? prepared named source (DirectSite rows) with
  | none => none
  | some receipt => pure ⟨nodes, ⟨receipt, accepted⟩⟩

def certifyDirect {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked) (named : Named)
    (source : TypedSource) (rows : List SourceSpecialization.SpecializedFunction) :
    Option (Profile prepared named source rows true) := certify prepared named source rows true

end Solcore.SourceSemantics.CoreLowering.AcceptedCompilerExpressionProfile
