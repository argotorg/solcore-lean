import Solcore.SourceSemantics.CoreLowering.AcceptedNamedExpressionMetadata

/-! A finite set of reached original occurrences excludes expression boundaries.
Closure follows actual ordered call children. Declaration names stay static;
indirect callees are retained as the leading child. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.AcceptedNamedExpressionFlow
open Core Frontend SourceInference
open CallableIndexedNamedGeneration
open CallableIndexedOwnedContextualCompilerPolicyProfiles (RootPolicyReceipt)
open CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles (MetadataFor)
open CallableIndexedOwnedPreparedStagedDirectCallCertificates (Child)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : Compilation compiled.indexed named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  {root : RootPolicyReceipt (compiled := compiled) named diagnostics namedCode compilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered}
  {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Word}
  {fuel : Nat} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  {directSites : DeclarationInstantiation → Prop} {reached : ExpressionId → Prop}

/-- Only original occurrences that are actually reached need these form facts. -/
def ReachedForms (source : TypedSource) (reached : ExpressionId → Prop) : Prop :=
  ∀ id node, reached id → source.lookupExpression? id = some node →
    LeafForm node.form ∨ DirectForm node.form

/-- Every argument occurrence is retained, including duplicate positions. -/
def ReachedArguments (source : TypedSource) (reached : ExpressionId → Prop) : Prop :=
  ∀ id node, reached id → source.lookupExpression? id = some node →
    ∀ callee arguments instantiation, node.form = .call callee arguments (.declaration instantiation) →
      ∀ argument ∈ arguments, reached argument

private theorem leaf_not_method {form : ExpressionForm} (leaf : LeafForm form) : ¬ MethodForm form := by
  rcases leaf.view with atomic | ⟨name, binder, rfl⟩
  · cases atomic <;> simp [MethodForm, AcceptedContextualOperatorReceipt.Form]
  · simp [MethodForm, AcceptedContextualOperatorReceipt.Form]

private theorem direct_not_method {form : ExpressionForm} (direct : DirectForm form) : ¬ MethodForm form := by
  obtain ⟨callee, arguments, instantiation, rfl⟩ := direct
  simp [MethodForm, AcceptedContextualOperatorReceipt.Form]

private theorem indirect_not_method {form : ExpressionForm} (indirect : IndirectForm form) : ¬ MethodForm form := by
  obtain ⟨callee, arguments, metadata, rfl⟩ := indirect
  simp [MethodForm, AcceptedContextualOperatorReceipt.Form]

private theorem not_index {form : ExpressionForm}
    (allowed : LeafForm form ∨ DirectForm form ∨ IndirectForm form ∨ MethodForm form) : ¬ IndexForm form := by
  rcases allowed with leaf | ⟨callee, args, inst, rfl⟩ | ⟨callee, args, metadata, rfl⟩ | method
  · rcases leaf.view with atomic | ⟨name, binder, rfl⟩
    · cases atomic <;> simp [IndexForm]
    · simp [IndexForm]
  · simp [IndexForm]
  · simp [IndexForm]
  · rcases method with ⟨operator, operand, rfl⟩ | ⟨operator, left, right, rfl⟩ <;> simp [IndexForm]

private theorem not_constructor {form : ExpressionForm}
    (allowed : (LeafForm form ∨ DirectForm form ∨ IndirectForm form ∨ MethodForm form) ∨ IndexForm form) :
    ¬ ConstructorForm form := by
  rcases allowed with (leaf | ⟨callee, args, inst, rfl⟩ | ⟨callee, args, metadata, rfl⟩ | method) | ⟨base, key, rfl⟩
  · rcases leaf.view with atomic | ⟨name, binder, rfl⟩
    · cases atomic <;> simp [ConstructorForm]
    · simp [ConstructorForm]
  · simp [ConstructorForm]
  · simp [ConstructorForm]
  · rcases method with ⟨operator, operand, rfl⟩ | ⟨operator, left, right, rfl⟩ <;> simp [ConstructorForm]
  · simp [ConstructorForm]

private theorem not_composite {form : ExpressionForm}
    (allowed : ((LeafForm form ∨ DirectForm form ∨ IndirectForm form ∨ MethodForm form) ∨ IndexForm form) ∨ ConstructorForm form) :
    ¬ CompositeForm form := by
  intro composite
  rcases allowed with ((leaf | ⟨callee, args, inst, rfl⟩ | ⟨callee, args, metadata, rfl⟩ | method) | ⟨base, key, rfl⟩) | ⟨inst, ids, rfl⟩
  · rcases leaf.view with atomic | ⟨name, binder, rfl⟩
    · cases atomic <;> cases composite
    · cases composite
  · cases composite
  · cases composite
  · rcases method with ⟨operator, operand, rfl⟩ | ⟨operator, left, right, rfl⟩ <;> cases composite
  · cases composite
  · cases composite

private theorem receipt_method_form
    (receipt : CallableIndexedOwnedPreparedStagedOperatorMethodCertificates.Receipt
      root.selected.policy root.selected.lowerBody fuel (context compiled.indexed named)
      (.initial compiled.compatible.checked) source scope id reasonAt lowered) : MethodForm receipt.node.form := by
  rcases receipt.operator.form with ⟨operator, operand, form, _⟩ | ⟨operator, left, right, form, _⟩
  · exact .inl ⟨operator, operand, form⟩
  · exact .inr ⟨operator, left, right, form⟩

private theorem forms_not_method (forms : ReachedForms source reached)
    {id : ExpressionId} {node : ExpressionNode} (present : reached id)
    (found : source.lookupExpression? id = some node) : ¬ MethodForm node.form := by
  rcases forms id node present found with leaf | direct
  · exact leaf_not_method leaf
  · exact direct_not_method direct

theorem Cause.impossible
    (metadata : MetadataFor compiled.indexed named source directSites)
    (forms : ReachedForms source reached)
    (initializers : ∀ id, reached id →
      ¬ Nonempty (AcceptedContextualDirectReceipt.InitializerAt compiled.indexed (context compiled.indexed named) id))
    {head : Head root.selected.policy root.selected.lowerBody fuel (context compiled.indexed named)
      source scope id reasonAt lowered}
    (cause : Cause root head) (present : reached id) : False := by
  have form := forms id head.node present head.found
  cases cause with
  | form _ notLeaf notDirect _ _ _ _ _ =>
    rcases form with leaf | direct
    · exact notLeaf leaf
    · exact notDirect direct
  | initializer _ selected => exact initializers id present ⟨selected⟩
  | special selected outside _ =>
    rcases form with leaf | direct
    · have profile := AcceptedNamedExpressionPolicy.leaf_profile root.compilerPolicy metadata
        head.found leaf.view (Child root.selected.policy root.selected.lowerBody fuel
          (context compiled.indexed named)) (fuel + 1) scope reasonAt
      have same := head.selected.symm.trans profile.2.2
      rw [selected] at same
      cases same
    · exact outside direct

  | operatorOrdinary _ operator _ | operatorCoercions _ operator _ =>
    exact forms_not_method forms present head.found operator

  | indexOperands _ indexForm _ => exact not_index (by rcases form with leaf | direct; exact .inl leaf; exact .inr (.inl direct)) ⟨_, _, indexForm⟩

  | constructorRange _ constructorForm _ => exact not_constructor (by rcases form with leaf | direct; exact .inl (.inl leaf); exact .inl (.inr (.inl direct))) ⟨_, _, constructorForm⟩

theorem Step.child_reached
    (forms : ReachedForms source reached)
    (arguments : ReachedArguments source reached)
    (step : Step root source scope reasonAt fuel id lowered)
    (present : reached id) {entry : ExpressionId × SourceCoreBasic.LoweredExpr}
    (member : entry ∈ step.children) : reached entry.1 := by
  cases step with
  | leaf => cases member
  | boundary => cases member
  | ordinary head _ receipt =>
    exact arguments id receipt.node present receipt.metadata.found _ _ _ receipt.form
      entry.1 (List.of_mem_zip member).1
  | evidence head _ receipt =>
    exact arguments id head.node present receipt.found _ _ _ receipt.form
      entry.1 (List.of_mem_zip member).1
  | indirect head _ receipt =>
    have original := forms id receipt.original present receipt.found
    rcases original with leaf | ⟨callee, args, instantiation, direct⟩
    · rw [receipt.originalForm] at leaf
      cases leaf with
      | literal atomic => cases atomic
    · rw [receipt.originalForm] at direct
      cases direct

  | method head selected receipt =>
    exact False.elim (forms_not_method forms present receipt.metadata.found (receipt_method_form receipt))

  | index head plain receipt =>
    exact False.elim (not_index (by rcases forms id receipt.node present receipt.found with leaf | direct; exact .inl leaf; exact .inr (.inl direct)) ⟨_, _, receipt.form⟩)

  | constructor head plain receipt =>
    exact False.elim (not_constructor (by rcases forms id receipt.node present receipt.found with leaf | direct; exact .inl (.inl leaf); exact .inl (.inr (.inl direct))) ⟨_, _, receipt.form⟩)

  | composite head plain receipt =>
    exact False.elim (not_composite (by rcases forms id receipt.node present receipt.found with leaf | direct; exact .inl (.inl (.inl leaf)); exact .inl (.inl (.inr (.inl direct)))) receipt.form)

/-- The excluded endpoint belongs to this same trace and its actual child path. -/
theorem Boundary.impossible
    (metadata : MetadataFor compiled.indexed named source directSites)
    (forms : ReachedForms source reached)
    (initializers : ∀ id, reached id →
      ¬ Nonempty (AcceptedContextualDirectReceipt.InitializerAt compiled.indexed (context compiled.indexed named) id))
    (arguments : ReachedArguments source reached)
    {tree : Trace root source scope reasonAt fuel id lowered}
    (boundary : Boundary tree) (present : reached id) : False := by
  induction boundary with
  | here head cause children => exact cause.impossible metadata forms initializers present
  | child step children entry member next ih => exact ih (step.child_reached forms arguments present member)

/-- The Header residual is excluded by forms and actual argument reachability.
No recursive expression grammar is a premise. -/
theorem Residual.impossible {row : SourceSpecialization.SpecializedFunction}
    {prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row}
    {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    (residual : Residual prepared header directSites fuel source scope id lowered)
    (metadata : MetadataFor compiled.indexed prepared.named source directSites)
    (forms : ReachedForms source reached)
    (initializers : ∀ id, reached id → ¬ Nonempty (AcceptedContextualDirectReceipt.InitializerAt
      compiled.indexed (context compiled.indexed prepared.named) id))
    (arguments : ReachedArguments source reached)
    (present : reached id) : False :=
  residual.boundary.impossible metadata forms initializers arguments present

/-- Indirect calls include the original callee occurrence as well as arguments. -/
def ReachedCallForms (source : TypedSource) (reached : ExpressionId → Prop) : Prop :=
  ∀ id node, reached id → source.lookupExpression? id = some node →
    LeafForm node.form ∨ DirectForm node.form ∨ IndirectForm node.form

/-- Reachability follows original argument order, with an indirect callee first. -/
def ReachedCallArguments (source : TypedSource) (reached : ExpressionId → Prop) : Prop :=
  ReachedArguments source reached ∧
  ∀ id node, reached id → source.lookupExpression? id = some node →
    ∀ callee arguments metadata, node.form = .call callee arguments (.indirect metadata) →
      reached callee ∧ ∀ argument ∈ arguments, reached argument

/-- These are raw original-node checks, independent of recursive grammar. -/
def ReachedIndirectMetadata {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked) (named : Named)
    (source : TypedSource) (reached : ExpressionId → Prop) : Prop :=
  ∀ id node, reached id → source.lookupExpression? id = some node →
    ∀ callee arguments metadata, node.form = .call callee arguments (.indirect metadata) →
      CallableIndexedOwnedPreparedNamedSyntaxAdmission.MetadataTest prepared named node

theorem ReachedIndirectMetadata.of_accepted {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : CallableIndexedNamedGeneration.Prepared checked} {named : Named}
    {source : TypedSource} {reached : ExpressionId → Prop}
    {directSites : DeclarationInstantiation → Prop}
    {receipt : PLift (MetadataFor prepared named source directSites)}
    (accepted : CallableIndexedOwnedPreparedNamedSyntaxAdmission.metadata?
      prepared named source directSites = some receipt) :
    ReachedIndirectMetadata prepared named source reached := by
  intro id node _ found callee arguments metadata form
  exact AcceptedNamedExpressionMetadata.indirect_of_accepted accepted found form

private theorem callForms_not_method (forms : ReachedCallForms source reached)
    {id : ExpressionId} {node : ExpressionNode} (present : reached id)
    (found : source.lookupExpression? id = some node) : ¬ MethodForm node.form := by
  rcases forms id node present found with leaf | direct | indirect
  · exact leaf_not_method leaf
  · exact direct_not_method direct
  · exact indirect_not_method indirect

theorem Cause.impossible_calls
    (metadata : MetadataFor compiled.indexed named source directSites)
    (forms : ReachedCallForms source reached)
    (initializers : ∀ id, reached id →
      ¬ Nonempty (AcceptedContextualDirectReceipt.InitializerAt compiled.indexed (context compiled.indexed named) id))
    (rawMetadata : ReachedIndirectMetadata compiled.indexed named source reached)
    {head : Head root.selected.policy root.selected.lowerBody fuel (context compiled.indexed named)
      source scope id reasonAt lowered}
    (cause : Cause root head) (present : reached id) : False := by
  have original := forms id head.node present head.found
  cases cause with
  | form _ notLeaf notDirect notIndirect _ _ _ _ =>
    rcases original with leaf | direct | indirect
    · exact notLeaf leaf
    · exact notDirect direct
    · exact notIndirect indirect
  | initializer _ selected => exact initializers id present ⟨selected⟩
  | special selected outside _ =>
    rcases original with leaf | direct | ⟨callee, arguments, callMetadata, form⟩
    · have profile := AcceptedNamedExpressionPolicy.leaf_profile root.compilerPolicy metadata
        head.found leaf.view (Child root.selected.policy root.selected.lowerBody fuel
          (context compiled.indexed named)) (fuel + 1) scope reasonAt
      have same := head.selected.symm.trans profile.2.2
      rw [selected] at same
      cases same
    · exact outside direct
    · have clean := rawMetadata id head.node present head.found callee arguments callMetadata form
      have profile := CallableIndexedOwnedContextualCompilerPolicyProfiles.indirect_policy root (scope := scope) (reasonAt := reasonAt) head.found form
        (by simpa only [form] using clean.2.2.1) clean.1
        (by simpa only [form] using clean.2.2.2.1)
        (by simpa only [(lookupExpression?_sound head.found).2] using clean.2.1)
      have noneSelected := profile.special
        (Child root.selected.policy root.selected.lowerBody fuel (context compiled.indexed named)) (fuel + 1)
      have same := head.selected.symm.trans noneSelected
      rw [selected] at same
      cases same

  | operatorOrdinary _ operator _ | operatorCoercions _ operator _ =>
    exact callForms_not_method forms present head.found operator

  | indexOperands _ indexForm _ => exact not_index (by rcases original with leaf | direct | indirect; exact .inl leaf; exact .inr (.inl direct); exact .inr (.inr (.inl indirect))) ⟨_, _, indexForm⟩

  | constructorRange _ constructorForm _ => exact not_constructor (by rcases original with leaf | direct | indirect; exact .inl (.inl leaf); exact .inl (.inr (.inl direct)); exact .inl (.inr (.inr (.inl indirect)))) ⟨_, _, constructorForm⟩

theorem Step.child_reached_calls
    (forms : ReachedCallForms source reached)
    (arguments : ReachedCallArguments source reached)
    (step : Step root source scope reasonAt fuel id lowered)
    (present : reached id) {entry : ExpressionId × SourceCoreBasic.LoweredExpr}
    (member : entry ∈ step.children) : reached entry.1 := by
  cases step with
  | leaf => cases member
  | boundary => cases member
  | ordinary head _ receipt =>
    exact arguments.1 id receipt.node present receipt.metadata.found _ _ _ receipt.form
      entry.1 (List.of_mem_zip member).1
  | evidence head _ receipt =>
    exact arguments.1 id head.node present receipt.found _ _ _ receipt.form
      entry.1 (List.of_mem_zip member).1
  | indirect head _ receipt =>
    have children := arguments.2 id receipt.original present receipt.found _ _ _ receipt.originalForm
    rcases List.mem_cons.mp member with same | member
    · exact same ▸ children.1
    · exact children.2 entry.1 (List.of_mem_zip member).1

  | method head selected receipt =>
    exact False.elim (callForms_not_method forms present receipt.metadata.found (receipt_method_form receipt))

  | index head plain receipt =>
    exact False.elim (not_index (by rcases forms id receipt.node present receipt.found with leaf | direct | indirect; exact .inl leaf; exact .inr (.inl direct); exact .inr (.inr (.inl indirect))) ⟨_, _, receipt.form⟩)

  | constructor head plain receipt =>
    exact False.elim (not_constructor (by rcases forms id receipt.node present receipt.found with leaf | direct | indirect; exact .inl (.inl leaf); exact .inl (.inr (.inl direct)); exact .inl (.inr (.inr (.inl indirect)))) ⟨_, _, receipt.form⟩)

  | composite head plain receipt =>
    exact False.elim (not_composite (by rcases forms id receipt.node present receipt.found with leaf | direct | indirect; exact .inl (.inl (.inl leaf)); exact .inl (.inl (.inr (.inl direct))); exact .inl (.inl (.inr (.inr (.inl indirect))))) receipt.form)

theorem Boundary.impossible_calls
    (metadata : MetadataFor compiled.indexed named source directSites)
    (forms : ReachedCallForms source reached)
    (initializers : ∀ id, reached id →
      ¬ Nonempty (AcceptedContextualDirectReceipt.InitializerAt compiled.indexed (context compiled.indexed named) id))
    (arguments : ReachedCallArguments source reached)
    (rawMetadata : ReachedIndirectMetadata compiled.indexed named source reached)
    {tree : Trace root source scope reasonAt fuel id lowered}
    (boundary : Boundary tree) (present : reached id) : False := by
  induction boundary with
  | here head cause children => exact cause.impossible_calls metadata forms initializers rawMetadata present
  | child step children entry member next ih => exact ih (step.child_reached_calls forms arguments present member)

theorem Residual.impossible_calls {row : SourceSpecialization.SpecializedFunction}
    {prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row}
    {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    (residual : Residual prepared header directSites fuel source scope id lowered)
    (metadata : MetadataFor compiled.indexed prepared.named source directSites)
    (forms : ReachedCallForms source reached)
    (initializers : ∀ id, reached id → ¬ Nonempty (AcceptedContextualDirectReceipt.InitializerAt
      compiled.indexed (context compiled.indexed prepared.named) id))
    (arguments : ReachedCallArguments source reached)
    (rawMetadata : ReachedIndirectMetadata compiled.indexed prepared.named source reached)
    (present : reached id) : False :=
  residual.boundary.impossible_calls metadata forms initializers arguments rawMetadata present

/-- Method occurrences are original unary or binary nodes. -/
def ReachedMethodForms (source : TypedSource) (reached : ExpressionId → Prop) : Prop :=
  ∀ id node, reached id → source.lookupExpression? id = some node →
    LeafForm node.form ∨ DirectForm node.form ∨ IndirectForm node.form ∨ MethodForm node.form

/-- Method operands retain unary or left-to-right binary order. -/
def ReachedMethodArguments (source : TypedSource) (reached : ExpressionId → Prop) : Prop :=
  ReachedCallArguments source reached ∧
  (∀ id node, reached id → source.lookupExpression? id = some node →
    ∀ operator operand, node.form = .unary operator operand → reached operand) ∧
  (∀ id node, reached id → source.lookupExpression? id = some node →
    ∀ operator left right, node.form = .binary left operator right → reached left ∧ reached right)

/-- The bounded method lane requires the genuine nonempty requirement list. -/
def ReachedMethodRequirements (source : TypedSource) (reached : ExpressionId → Prop) : Prop :=
  ∀ id node, reached id → source.lookupExpression? id = some node →
    MethodForm node.form → node.requirements ≠ []

def ReachedMethodMetadata {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked) (named : Named)
    (source : TypedSource) (reached : ExpressionId → Prop) : Prop :=
  ReachedIndirectMetadata prepared named source reached ∧
  ∀ id node, reached id → source.lookupExpression? id = some node →
    MethodForm node.form → CallableIndexedOwnedPreparedNamedSyntaxAdmission.MetadataTest prepared named node

theorem ReachedMethodMetadata.of_accepted {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : CallableIndexedNamedGeneration.Prepared checked} {named : Named}
    {source : TypedSource} {reached : ExpressionId → Prop}
    {directSites : DeclarationInstantiation → Prop}
    {receipt : PLift (MetadataFor prepared named source directSites)}
    (accepted : CallableIndexedOwnedPreparedNamedSyntaxAdmission.metadata?
      prepared named source directSites = some receipt) :
    ReachedMethodMetadata prepared named source reached := by
  refine ⟨ReachedIndirectMetadata.of_accepted accepted, ?_⟩
  intro id node _ found form
  apply AcceptedNamedExpressionMetadata.at_of_accepted accepted found
  rcases form with ⟨operator, operand, form⟩ | ⟨operator, left, right, form⟩
  · exact form ▸ .unary operator operand
  · exact form ▸ .binary left operator right

theorem Cause.impossible_methods
    (metadata : MetadataFor compiled.indexed named source directSites)
    (forms : ReachedMethodForms source reached)
    (initializers : ∀ id, reached id →
      ¬ Nonempty (AcceptedContextualDirectReceipt.InitializerAt compiled.indexed (context compiled.indexed named) id))
    (rawMetadata : ReachedMethodMetadata compiled.indexed named source reached)
    (requirements : ReachedMethodRequirements source reached)
    {head : Head root.selected.policy root.selected.lowerBody fuel (context compiled.indexed named)
      source scope id reasonAt lowered}
    (cause : Cause root head) (present : reached id) : False := by
  have original := forms id head.node present head.found
  cases cause with
  | form _ notLeaf notDirect notIndirect notMethod _ _ _ =>
    rcases original with leaf | direct | indirect | method
    · exact notLeaf leaf
    · exact notDirect direct
    · exact notIndirect indirect
    · exact notMethod method
  | initializer _ selected => exact initializers id present ⟨selected⟩
  | operatorOrdinary _ form empty => exact requirements id head.node present head.found form empty
  | operatorCoercions _ form nonempty => exact nonempty (rawMetadata.2 id head.node present head.found form).1
  | special selected outside outsideMethod =>
    rcases original with leaf | direct | ⟨callee, arguments, callMetadata, form⟩ | method
    · have profile := AcceptedNamedExpressionPolicy.leaf_profile root.compilerPolicy metadata
        head.found leaf.view (Child root.selected.policy root.selected.lowerBody fuel
          (context compiled.indexed named)) (fuel + 1) scope reasonAt
      have same := head.selected.symm.trans profile.2.2
      rw [selected] at same
      cases same
    · exact outside direct
    · have clean := rawMetadata.1 id head.node present head.found callee arguments callMetadata form
      have profile := CallableIndexedOwnedContextualCompilerPolicyProfiles.indirect_policy root
        (scope := scope) (reasonAt := reasonAt) head.found form
        (by simpa only [form] using clean.2.2.1) clean.1
        (by simpa only [form] using clean.2.2.2.1)
        (by simpa only [(lookupExpression?_sound head.found).2] using clean.2.1)
      have noneSelected := profile.special
        (Child root.selected.policy root.selected.lowerBody fuel (context compiled.indexed named)) (fuel + 1)
      have same := head.selected.symm.trans noneSelected
      rw [selected] at same
      cases same
    · exact outsideMethod method

  | indexOperands _ indexForm _ => exact not_index (original) ⟨_, _, indexForm⟩

  | constructorRange _ constructorForm _ => exact not_constructor (.inl (original)) ⟨_, _, constructorForm⟩

theorem Step.child_reached_methods
    (forms : ReachedMethodForms source reached)
    (arguments : ReachedMethodArguments source reached)
    (step : Step root source scope reasonAt fuel id lowered)
    (present : reached id) {entry : ExpressionId × SourceCoreBasic.LoweredExpr}
    (member : entry ∈ step.children) : reached entry.1 := by
  cases step with
  | leaf => cases member
  | boundary => cases member
  | ordinary head _ receipt =>
    exact arguments.1.1 id receipt.node present receipt.metadata.found _ _ _ receipt.form
      entry.1 (List.of_mem_zip member).1
  | evidence head _ receipt =>
    exact arguments.1.1 id head.node present receipt.found _ _ _ receipt.form
      entry.1 (List.of_mem_zip member).1
  | indirect head _ receipt =>
    have children := arguments.1.2 id receipt.original present receipt.found _ _ _ receipt.originalForm
    rcases List.mem_cons.mp member with same | member
    · exact same ▸ children.1
    · exact children.2 entry.1 (List.of_mem_zip member).1
  | method head _ receipt =>
    have child := (List.of_mem_zip member).1
    rcases receipt.operator.form with ⟨operator, operand, form, actual⟩ |
      ⟨operator, left, right, form, actual⟩
    · have same : entry.1 = operand := by
        simpa only [CallableIndexedOwnedPreparedStagedOperatorMethodCertificates.Receipt.arguments,
          actual, List.mem_singleton] using child
      exact same ▸ arguments.2.1 id receipt.node present receipt.metadata.found operator operand form
    · have cases : entry.1 = left ∨ entry.1 = right := by
        simpa only [CallableIndexedOwnedPreparedStagedOperatorMethodCertificates.Receipt.arguments,
          actual, List.mem_cons, List.not_mem_nil, or_false] using child
      have children := arguments.2.2 id receipt.node present receipt.metadata.found operator left right form
      rcases cases with same | same
      · exact same ▸ children.1
      · exact same ▸ children.2

  | index head plain receipt =>
    exact False.elim (not_index (forms id receipt.node present receipt.found) ⟨_, _, receipt.form⟩)

  | constructor head plain receipt =>
    exact False.elim (not_constructor (.inl (forms id receipt.node present receipt.found)) ⟨_, _, receipt.form⟩)

  | composite head plain receipt =>
    exact False.elim (not_composite (.inl (.inl (forms id receipt.node present receipt.found))) receipt.form)

theorem Boundary.impossible_methods
    (metadata : MetadataFor compiled.indexed named source directSites)
    (forms : ReachedMethodForms source reached)
    (initializers : ∀ id, reached id →
      ¬ Nonempty (AcceptedContextualDirectReceipt.InitializerAt compiled.indexed (context compiled.indexed named) id))
    (arguments : ReachedMethodArguments source reached)
    (rawMetadata : ReachedMethodMetadata compiled.indexed named source reached)
    (requirements : ReachedMethodRequirements source reached)
    {tree : Trace root source scope reasonAt fuel id lowered}
    (boundary : Boundary tree) (present : reached id) : False := by
  induction boundary with
  | here head cause children => exact cause.impossible_methods metadata forms initializers rawMetadata requirements present
  | child step children entry member next ih => exact ih (step.child_reached_methods forms arguments present member)

theorem Residual.impossible_methods {row : SourceSpecialization.SpecializedFunction}
    {prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row}
    {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    (residual : Residual prepared header directSites fuel source scope id lowered)
    (metadata : MetadataFor compiled.indexed prepared.named source directSites)
    (forms : ReachedMethodForms source reached)
    (initializers : ∀ id, reached id → ¬ Nonempty (AcceptedContextualDirectReceipt.InitializerAt
      compiled.indexed (context compiled.indexed prepared.named) id))
    (arguments : ReachedMethodArguments source reached)
    (rawMetadata : ReachedMethodMetadata compiled.indexed prepared.named source reached)
    (requirements : ReachedMethodRequirements source reached)
    (present : reached id) : False :=
  residual.boundary.impossible_methods metadata forms initializers arguments rawMetadata requirements present

/-- The expanded lane retains indices without changing the method-only predicates. -/
def ReachedIndexForms (source : TypedSource) (reached : ExpressionId → Prop) : Prop :=
  ∀ id node, reached id → source.lookupExpression? id = some node →
    (LeafForm node.form ∨ DirectForm node.form ∨ IndirectForm node.form ∨ MethodForm node.form) ∨ IndexForm node.form

def ReachedIndexArguments (source : TypedSource) (reached : ExpressionId → Prop) : Prop :=
  ReachedMethodArguments source reached ∧
  ∀ id node, reached id → source.lookupExpression? id = some node →
    ∀ base key, node.form = .index base key → reached base ∧ reached key

def ReachedIndexOperands (source : TypedSource) (reached : ExpressionId → Prop) : Prop :=
  ∀ id node, reached id → source.lookupExpression? id = some node →
    ∀ base key, node.form = .index base key → AcceptedIndexExpressionReceipt.Operands source base key

def ReachedIndexMetadata {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked) (named : Named)
    (source : TypedSource) (reached : ExpressionId → Prop) : Prop :=
  ReachedMethodMetadata prepared named source reached ∧
  ∀ id node, reached id → source.lookupExpression? id = some node →
    ∀ base key, node.form = .index base key →
      CallableIndexedOwnedPreparedNamedSyntaxAdmission.MetadataTest prepared named node

theorem ReachedIndexMetadata.of_accepted {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : CallableIndexedNamedGeneration.Prepared checked} {named : Named}
    {source : TypedSource} {reached : ExpressionId → Prop}
    {directSites : DeclarationInstantiation → Prop}
    {receipt : PLift (MetadataFor prepared named source directSites)}
    (accepted : CallableIndexedOwnedPreparedNamedSyntaxAdmission.metadata?
      prepared named source directSites = some receipt) :
    ReachedIndexMetadata prepared named source reached := by
  refine ⟨ReachedMethodMetadata.of_accepted accepted, ?_⟩
  intro id node _ found base key form
  exact AcceptedNamedExpressionMetadata.at_of_accepted accepted found (form ▸ .index base key)

theorem Cause.impossible_indices
    (metadata : MetadataFor compiled.indexed named source directSites)
    (forms : ReachedIndexForms source reached)
    (initializers : ∀ id, reached id →
      ¬ Nonempty (AcceptedContextualDirectReceipt.InitializerAt compiled.indexed (context compiled.indexed named) id))
    (rawMetadata : ReachedIndexMetadata compiled.indexed named source reached)
    (requirements : ReachedMethodRequirements source reached)
    (operands : ReachedIndexOperands source reached)
    {head : Head root.selected.policy root.selected.lowerBody fuel (context compiled.indexed named)
      source scope id reasonAt lowered}
    (cause : Cause root head) (present : reached id) : False := by
  have original := forms id head.node present head.found
  cases cause with
  | form _ notLeaf notDirect notIndirect notMethod notIndex _ _ =>
    rcases original with (leaf | direct | indirect | method) | index
    · exact notLeaf leaf
    · exact notDirect direct
    · exact notIndirect indirect
    · exact notMethod method
    · exact notIndex index
  | initializer _ selected => exact initializers id present ⟨selected⟩
  | operatorOrdinary _ form empty => exact requirements id head.node present head.found form empty
  | operatorCoercions _ form nonempty => exact nonempty (rawMetadata.1.2 id head.node present head.found form).1
  | special selected outside outsideMethod =>
    rcases original with (leaf | direct | ⟨callee, arguments, callMetadata, form⟩ | method) | ⟨base, key, form⟩
    · have profile := AcceptedNamedExpressionPolicy.leaf_profile root.compilerPolicy metadata
        head.found leaf.view (Child root.selected.policy root.selected.lowerBody fuel
          (context compiled.indexed named)) (fuel + 1) scope reasonAt
      have same := head.selected.symm.trans profile.2.2
      rw [selected] at same
      cases same
    · exact outside direct
    · have clean := rawMetadata.1.1 id head.node present head.found callee arguments callMetadata form
      have profile := CallableIndexedOwnedContextualCompilerPolicyProfiles.indirect_policy root
        (scope := scope) (reasonAt := reasonAt) head.found form
        (by simpa only [form] using clean.2.2.1) clean.1
        (by simpa only [form] using clean.2.2.2.1)
        (by simpa only [(lookupExpression?_sound head.found).2] using clean.2.1)
      have noneSelected := profile.special
        (Child root.selected.policy root.selected.lowerBody fuel (context compiled.indexed named)) (fuel + 1)
      have same := head.selected.symm.trans noneSelected
      rw [selected] at same
      cases same
    · exact outsideMethod method
    · have clean := rawMetadata.2 id head.node present head.found base key form
      have noneSelected := AcceptedIndexExpressionReceipt.special_none root (scope := scope) (reasonAt := reasonAt) head.found form clean
        (Child root.selected.policy root.selected.lowerBody fuel (context compiled.indexed named)) (fuel + 1)
      have same := head.selected.symm.trans noneSelected
      rw [selected] at same
      cases same

  | indexOperands _ indexForm missing => exact missing (operands id head.node present head.found _ _ indexForm)

  | constructorRange _ constructorForm _ => exact not_constructor (original) ⟨_, _, constructorForm⟩

theorem Step.child_reached_indices
    (forms : ReachedIndexForms source reached)
    (arguments : ReachedIndexArguments source reached)
    (step : Step root source scope reasonAt fuel id lowered)
    (present : reached id) {entry : ExpressionId × SourceCoreBasic.LoweredExpr}
    (member : entry ∈ step.children) : reached entry.1 := by
  cases step with
  | leaf => cases member
  | boundary => cases member
  | ordinary head _ receipt =>
    exact arguments.1.1.1 id receipt.node present receipt.metadata.found _ _ _ receipt.form
      entry.1 (List.of_mem_zip member).1
  | evidence head _ receipt =>
    exact arguments.1.1.1 id head.node present receipt.found _ _ _ receipt.form
      entry.1 (List.of_mem_zip member).1
  | indirect head _ receipt =>
    have children := arguments.1.1.2 id receipt.original present receipt.found _ _ _ receipt.originalForm
    rcases List.mem_cons.mp member with same | member
    · exact same ▸ children.1
    · exact children.2 entry.1 (List.of_mem_zip member).1
  | method head _ receipt =>
    have child := (List.of_mem_zip member).1
    rcases receipt.operator.form with ⟨operator, operand, form, actual⟩ |
      ⟨operator, left, right, form, actual⟩
    · have same : entry.1 = operand := by
        simpa only [CallableIndexedOwnedPreparedStagedOperatorMethodCertificates.Receipt.arguments,
          actual, List.mem_singleton] using child
      exact same ▸ arguments.1.2.1 id receipt.node present receipt.metadata.found operator operand form
    · have cases : entry.1 = left ∨ entry.1 = right := by
        simpa only [CallableIndexedOwnedPreparedStagedOperatorMethodCertificates.Receipt.arguments,
          actual, List.mem_cons, List.not_mem_nil, or_false] using child
      have children := arguments.1.2.2 id receipt.node present receipt.metadata.found operator left right form
      rcases cases with same | same
      · exact same ▸ children.1
      · exact same ▸ children.2

  | index head plain receipt =>
    have children := arguments.2 id receipt.node present receipt.found _ _ receipt.form
    rcases List.mem_cons.mp member with same | member
    · exact same ▸ children.1
    · exact (List.mem_singleton.mp member) ▸ children.2

  | constructor head plain receipt =>
    exact False.elim (not_constructor (forms id receipt.node present receipt.found) ⟨_, _, receipt.form⟩)

  | composite head plain receipt =>
    exact False.elim (not_composite (.inl (forms id receipt.node present receipt.found)) receipt.form)

theorem Boundary.impossible_indices
    (metadata : MetadataFor compiled.indexed named source directSites)
    (forms : ReachedIndexForms source reached)
    (initializers : ∀ id, reached id →
      ¬ Nonempty (AcceptedContextualDirectReceipt.InitializerAt compiled.indexed (context compiled.indexed named) id))
    (arguments : ReachedIndexArguments source reached)
    (rawMetadata : ReachedIndexMetadata compiled.indexed named source reached)
    (requirements : ReachedMethodRequirements source reached)
    (operands : ReachedIndexOperands source reached)
    {tree : Trace root source scope reasonAt fuel id lowered}
    (boundary : Boundary tree) (present : reached id) : False := by
  induction boundary with
  | here head cause children => exact cause.impossible_indices metadata forms initializers rawMetadata requirements operands present
  | child step children entry member next ih => exact ih (step.child_reached_indices forms arguments present member)

theorem Residual.impossible_indices {row : SourceSpecialization.SpecializedFunction}
    {prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row}
    {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    (residual : Residual prepared header directSites fuel source scope id lowered)
    (metadata : MetadataFor compiled.indexed prepared.named source directSites)
    (forms : ReachedIndexForms source reached)
    (initializers : ∀ id, reached id → ¬ Nonempty (AcceptedContextualDirectReceipt.InitializerAt
      compiled.indexed (context compiled.indexed prepared.named) id))
    (arguments : ReachedIndexArguments source reached)
    (rawMetadata : ReachedIndexMetadata compiled.indexed prepared.named source reached)
    (requirements : ReachedMethodRequirements source reached)
    (operands : ReachedIndexOperands source reached)
    (present : reached id) : False :=
  residual.boundary.impossible_indices metadata forms initializers arguments rawMetadata requirements operands present

/-- Constructors add their complete ordered payload list to the existing lane. -/
def ReachedConstructorForms (source : TypedSource) (reached : ExpressionId → Prop) : Prop :=
  ∀ id node, reached id → source.lookupExpression? id = some node →
    ((LeafForm node.form ∨ DirectForm node.form ∨ IndirectForm node.form ∨ MethodForm node.form) ∨ IndexForm node.form) ∨ ConstructorForm node.form

def ReachedConstructorArguments (source : TypedSource) (reached : ExpressionId → Prop) : Prop :=
  ReachedIndexArguments source reached ∧
  ∀ id node, reached id → source.lookupExpression? id = some node →
    ∀ instantiation ids, node.form = .constructor instantiation ids → ∀ child ∈ ids, reached child

def ReachedConstructorRanges (source : TypedSource) (reached : ExpressionId → Prop) : Prop :=
  ∀ id node, reached id → source.lookupExpression? id = some node →
    ∀ instantiation ids, node.form = .constructor instantiation ids →
      CompatibleSourceInstantiationClosure.ClosedParameterRange instantiation.parameterSubstitution

def ReachedConstructorMetadata {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked) (named : Named)
    (source : TypedSource) (reached : ExpressionId → Prop) : Prop :=
  ReachedIndexMetadata prepared named source reached ∧
  ∀ id node, reached id → source.lookupExpression? id = some node →
    ∀ instantiation ids, node.form = .constructor instantiation ids →
      CallableIndexedOwnedPreparedNamedSyntaxAdmission.MetadataTest prepared named node

theorem ReachedConstructorMetadata.of_accepted {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : CallableIndexedNamedGeneration.Prepared checked} {named : Named}
    {source : TypedSource} {reached : ExpressionId → Prop}
    {directSites : DeclarationInstantiation → Prop}
    {receipt : PLift (MetadataFor prepared named source directSites)}
    (accepted : CallableIndexedOwnedPreparedNamedSyntaxAdmission.metadata?
      prepared named source directSites = some receipt) :
    ReachedConstructorMetadata prepared named source reached := by
  refine ⟨ReachedIndexMetadata.of_accepted accepted, ?_⟩
  intro id node _ found instantiation ids form
  exact AcceptedNamedExpressionMetadata.at_of_accepted accepted found (form ▸ .constructor instantiation ids)

private theorem Cause.impossible_constructor_at
    (metadata : MetadataFor compiled.indexed named source directSites)
    (initializers : ∀ id, reached id →
      ¬ Nonempty (AcceptedContextualDirectReceipt.InitializerAt compiled.indexed (context compiled.indexed named) id))
    (rawMetadata : ReachedConstructorMetadata compiled.indexed named source reached)
    (requirements : ReachedMethodRequirements source reached)
    (operands : ReachedIndexOperands source reached)
    (ranges : ReachedConstructorRanges source reached)
    {head : Head root.selected.policy root.selected.lowerBody fuel (context compiled.indexed named)
      source scope id reasonAt lowered}
    (cause : Cause root head)
    (original : ((LeafForm head.node.form ∨ DirectForm head.node.form ∨ IndirectForm head.node.form ∨ MethodForm head.node.form) ∨ IndexForm head.node.form) ∨ ConstructorForm head.node.form)
    (present : reached id) : False := by
  cases cause with
  | form _ notLeaf notDirect notIndirect notMethod notIndex notConstructor _ =>
    rcases original with ((leaf | direct | indirect | method) | index) | constructor
    · exact notLeaf leaf
    · exact notDirect direct
    · exact notIndirect indirect
    · exact notMethod method
    · exact notIndex index
    · exact notConstructor constructor
  | initializer _ selected => exact initializers id present ⟨selected⟩
  | operatorOrdinary _ form empty => exact requirements id head.node present head.found form empty
  | operatorCoercions _ form nonempty => exact nonempty (rawMetadata.1.1.2 id head.node present head.found form).1
  | special selected outside outsideMethod =>
    rcases original with ((leaf | direct | ⟨callee, arguments, callMetadata, form⟩ | method) | ⟨base, key, form⟩) | ⟨instantiation, ids, form⟩
    · have profile := AcceptedNamedExpressionPolicy.leaf_profile root.compilerPolicy metadata
        head.found leaf.view (Child root.selected.policy root.selected.lowerBody fuel
          (context compiled.indexed named)) (fuel + 1) scope reasonAt
      have same := head.selected.symm.trans profile.2.2
      rw [selected] at same
      cases same
    · exact outside direct
    · have clean := rawMetadata.1.1.1 id head.node present head.found callee arguments callMetadata form
      have profile := CallableIndexedOwnedContextualCompilerPolicyProfiles.indirect_policy root
        (scope := scope) (reasonAt := reasonAt) head.found form
        (by simpa only [form] using clean.2.2.1) clean.1
        (by simpa only [form] using clean.2.2.2.1)
        (by simpa only [(lookupExpression?_sound head.found).2] using clean.2.1)
      have noneSelected := profile.special
        (Child root.selected.policy root.selected.lowerBody fuel (context compiled.indexed named)) (fuel + 1)
      have same := head.selected.symm.trans noneSelected
      rw [selected] at same
      cases same
    · exact outsideMethod method
    · have clean := rawMetadata.1.2 id head.node present head.found base key form
      have noneSelected := AcceptedIndexExpressionReceipt.special_none root (scope := scope) (reasonAt := reasonAt) head.found form clean
        (Child root.selected.policy root.selected.lowerBody fuel (context compiled.indexed named)) (fuel + 1)
      have same := head.selected.symm.trans noneSelected
      rw [selected] at same
      cases same

    · have clean := rawMetadata.2 id head.node present head.found instantiation ids form
      have noneSelected := AcceptedConstructorExpressionReceipt.special_none root (scope := scope) (reasonAt := reasonAt)
        head.found form clean
        (Child root.selected.policy root.selected.lowerBody fuel (context compiled.indexed named)) (fuel + 1)
      have same := head.selected.symm.trans noneSelected
      rw [selected] at same
      cases same
  | indexOperands _ indexForm missing => exact missing (operands id head.node present head.found _ _ indexForm)

  | constructorRange _ constructorForm missing => exact missing (ranges id head.node present head.found _ _ constructorForm)

theorem Cause.impossible_constructors
    (metadata : MetadataFor compiled.indexed named source directSites)
    (forms : ReachedConstructorForms source reached)
    (initializers : ∀ id, reached id →
      ¬ Nonempty (AcceptedContextualDirectReceipt.InitializerAt compiled.indexed (context compiled.indexed named) id))
    (rawMetadata : ReachedConstructorMetadata compiled.indexed named source reached)
    (requirements : ReachedMethodRequirements source reached)
    (operands : ReachedIndexOperands source reached)
    (ranges : ReachedConstructorRanges source reached)
    {head : Head root.selected.policy root.selected.lowerBody fuel (context compiled.indexed named)
      source scope id reasonAt lowered}
    (cause : Cause root head) (present : reached id) : False :=
  cause.impossible_constructor_at metadata initializers rawMetadata requirements operands ranges
    (forms id head.node present head.found) present

theorem Step.child_reached_constructors
    (forms : ReachedConstructorForms source reached)
    (arguments : ReachedConstructorArguments source reached)
    (step : Step root source scope reasonAt fuel id lowered)
    (present : reached id) {entry : ExpressionId × SourceCoreBasic.LoweredExpr}
    (member : entry ∈ step.children) : reached entry.1 := by
  cases step with
  | leaf => cases member
  | boundary => cases member
  | ordinary head _ receipt =>
    exact arguments.1.1.1.1 id receipt.node present receipt.metadata.found _ _ _ receipt.form
      entry.1 (List.of_mem_zip member).1
  | evidence head _ receipt =>
    exact arguments.1.1.1.1 id head.node present receipt.found _ _ _ receipt.form
      entry.1 (List.of_mem_zip member).1
  | indirect head _ receipt =>
    have children := arguments.1.1.1.2 id receipt.original present receipt.found _ _ _ receipt.originalForm
    rcases List.mem_cons.mp member with same | member
    · exact same ▸ children.1
    · exact children.2 entry.1 (List.of_mem_zip member).1
  | method head _ receipt =>
    have child := (List.of_mem_zip member).1
    rcases receipt.operator.form with ⟨operator, operand, form, actual⟩ |
      ⟨operator, left, right, form, actual⟩
    · have same : entry.1 = operand := by
        simpa only [CallableIndexedOwnedPreparedStagedOperatorMethodCertificates.Receipt.arguments,
          actual, List.mem_singleton] using child
      exact same ▸ arguments.1.1.2.1 id receipt.node present receipt.metadata.found operator operand form
    · have cases : entry.1 = left ∨ entry.1 = right := by
        simpa only [CallableIndexedOwnedPreparedStagedOperatorMethodCertificates.Receipt.arguments,
          actual, List.mem_cons, List.not_mem_nil, or_false] using child
      have children := arguments.1.1.2.2 id receipt.node present receipt.metadata.found operator left right form
      rcases cases with same | same
      · exact same ▸ children.1
      · exact same ▸ children.2

  | index head plain receipt =>
    have children := arguments.1.2 id receipt.node present receipt.found _ _ receipt.form
    rcases List.mem_cons.mp member with same | member
    · exact same ▸ children.1
    · exact (List.mem_singleton.mp member) ▸ children.2

  | constructor head plain receipt =>
    exact arguments.2 id receipt.node present receipt.found _ _ receipt.form
      entry.1 (List.of_mem_zip member).1

  | composite head plain receipt =>
    exact False.elim (not_composite (forms id receipt.node present receipt.found) receipt.form)

theorem Boundary.impossible_constructors
    (metadata : MetadataFor compiled.indexed named source directSites)
    (forms : ReachedConstructorForms source reached)
    (initializers : ∀ id, reached id →
      ¬ Nonempty (AcceptedContextualDirectReceipt.InitializerAt compiled.indexed (context compiled.indexed named) id))
    (arguments : ReachedConstructorArguments source reached)
    (rawMetadata : ReachedConstructorMetadata compiled.indexed named source reached)
    (requirements : ReachedMethodRequirements source reached)
    (operands : ReachedIndexOperands source reached)
    (ranges : ReachedConstructorRanges source reached)
    {tree : Trace root source scope reasonAt fuel id lowered}
    (boundary : Boundary tree) (present : reached id) : False := by
  induction boundary with
  | here head cause children => exact cause.impossible_constructors metadata forms initializers rawMetadata requirements operands ranges present
  | child step children entry member next ih => exact ih (step.child_reached_constructors forms arguments present member)

theorem Residual.impossible_constructors {row : SourceSpecialization.SpecializedFunction}
    {prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row}
    {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    (residual : Residual prepared header directSites fuel source scope id lowered)
    (metadata : MetadataFor compiled.indexed prepared.named source directSites)
    (forms : ReachedConstructorForms source reached)
    (initializers : ∀ id, reached id → ¬ Nonempty (AcceptedContextualDirectReceipt.InitializerAt
      compiled.indexed (context compiled.indexed prepared.named) id))
    (arguments : ReachedConstructorArguments source reached)
    (rawMetadata : ReachedConstructorMetadata compiled.indexed prepared.named source reached)
    (requirements : ReachedMethodRequirements source reached)
    (operands : ReachedIndexOperands source reached)
    (ranges : ReachedConstructorRanges source reached)
    (present : reached id) : False :=
  residual.boundary.impossible_constructors metadata forms initializers arguments rawMetadata requirements operands ranges present


/-- General composites retain their actual ordered source children. -/
def ReachedCompositeForms (source : TypedSource) (reached : ExpressionId → Prop) : Prop :=
  ∀ id node, reached id → source.lookupExpression? id = some node →
    (((LeafForm node.form ∨ DirectForm node.form ∨ IndirectForm node.form ∨ MethodForm node.form) ∨ IndexForm node.form) ∨ ConstructorForm node.form) ∨ CompositeForm node.form

def ReachedCompositeArguments (source : TypedSource) (reached : ExpressionId → Prop) : Prop :=
  ReachedConstructorArguments source reached ∧
  ∀ id node, reached id → source.lookupExpression? id = some node → CompositeForm node.form →
    ∀ child ∈ AcceptedCompositeExpressionReceipt.operands node.form, reached child

def ReachedCompositeMetadata {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked) (named : Named)
    (source : TypedSource) (reached : ExpressionId → Prop) : Prop :=
  ReachedConstructorMetadata prepared named source reached ∧
  ∀ id node, reached id → source.lookupExpression? id = some node → CompositeForm node.form →
    CallableIndexedOwnedPreparedNamedSyntaxAdmission.MetadataTest prepared named node

theorem ReachedCompositeMetadata.of_accepted {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : CallableIndexedNamedGeneration.Prepared checked} {named : Named}
    {source : TypedSource} {reached : ExpressionId → Prop}
    {directSites : DeclarationInstantiation → Prop}
    {receipt : PLift (MetadataFor prepared named source directSites)}
    (accepted : CallableIndexedOwnedPreparedNamedSyntaxAdmission.metadata?
      prepared named source directSites = some receipt) :
    ReachedCompositeMetadata prepared named source reached := by
  refine ⟨ReachedConstructorMetadata.of_accepted accepted, ?_⟩
  intro id node _ found form
  apply AcceptedNamedExpressionMetadata.at_of_accepted accepted found
  generalize eq : node.form = shape at form
  cases form
  · exact .group _
  · exact .tuple _
  · exact .conditional _ _ _

theorem Cause.impossible_composites
    (metadata : MetadataFor compiled.indexed named source directSites)
    (forms : ReachedCompositeForms source reached)
    (initializers : ∀ id, reached id →
      ¬ Nonempty (AcceptedContextualDirectReceipt.InitializerAt compiled.indexed (context compiled.indexed named) id))
    (rawMetadata : ReachedCompositeMetadata compiled.indexed named source reached)
    (requirements : ReachedMethodRequirements source reached)
    (operands : ReachedIndexOperands source reached)
    (ranges : ReachedConstructorRanges source reached)
    {head : Head root.selected.policy root.selected.lowerBody fuel (context compiled.indexed named)
      source scope id reasonAt lowered}
    (cause : Cause root head) (present : reached id) : False := by
  rcases forms id head.node present head.found with old | composite
  · exact cause.impossible_constructor_at metadata initializers rawMetadata.1 requirements operands ranges old present
  · cases cause with
    | form _ _ _ _ _ _ _ outside => exact outside composite
    | initializer _ selected => exact initializers id present ⟨selected⟩
    | special selected _ _ =>
      have noneSelected := AcceptedCompositeExpressionReceipt.special_none root (scope := scope) (reasonAt := reasonAt)
        head.found composite (rawMetadata.2 id head.node present head.found composite)
        (Child root.selected.policy root.selected.lowerBody fuel (context compiled.indexed named)) (fuel + 1)
      have same := head.selected.symm.trans noneSelected
      rw [selected] at same
      cases same
    | operatorOrdinary _ method _ | operatorCoercions _ method _ =>
      exact not_composite (.inl (.inl (.inr (.inr (.inr method))))) composite
    | indexOperands _ form _ => exact not_composite (.inl (.inr ⟨_, _, form⟩)) composite
    | constructorRange _ form _ => exact not_composite (.inr ⟨_, _, form⟩) composite

theorem Step.child_reached_composites
    (arguments : ReachedCompositeArguments source reached)
    (step : Step root source scope reasonAt fuel id lowered)
    (present : reached id) {entry : ExpressionId × SourceCoreBasic.LoweredExpr}
    (member : entry ∈ step.children) : reached entry.1 := by
  cases step with
  | leaf => cases member
  | boundary => cases member
  | ordinary head _ receipt =>
    exact arguments.1.1.1.1.1 id receipt.node present receipt.metadata.found _ _ _ receipt.form
      entry.1 (List.of_mem_zip member).1
  | evidence head _ receipt =>
    exact arguments.1.1.1.1.1 id head.node present receipt.found _ _ _ receipt.form
      entry.1 (List.of_mem_zip member).1
  | indirect head _ receipt =>
    have children := arguments.1.1.1.1.2 id receipt.original present receipt.found _ _ _ receipt.originalForm
    rcases List.mem_cons.mp member with same | member
    · exact same ▸ children.1
    · exact children.2 entry.1 (List.of_mem_zip member).1
  | method head _ receipt =>
    have child := (List.of_mem_zip member).1
    rcases receipt.operator.form with ⟨operator, operand, form, actual⟩ |
      ⟨operator, left, right, form, actual⟩
    · have same : entry.1 = operand := by
        simpa only [CallableIndexedOwnedPreparedStagedOperatorMethodCertificates.Receipt.arguments,
          actual, List.mem_singleton] using child
      exact same ▸ arguments.1.1.1.2.1 id receipt.node present receipt.metadata.found operator operand form
    · have cases : entry.1 = left ∨ entry.1 = right := by
        simpa only [CallableIndexedOwnedPreparedStagedOperatorMethodCertificates.Receipt.arguments,
          actual, List.mem_cons, List.not_mem_nil, or_false] using child
      have children := arguments.1.1.1.2.2 id receipt.node present receipt.metadata.found operator left right form
      rcases cases with same | same
      · exact same ▸ children.1
      · exact same ▸ children.2

  | index head plain receipt =>
    have children := arguments.1.1.2 id receipt.node present receipt.found _ _ receipt.form
    rcases List.mem_cons.mp member with same | member
    · exact same ▸ children.1
    · exact (List.mem_singleton.mp member) ▸ children.2

  | constructor head plain receipt =>
    exact arguments.1.2 id receipt.node present receipt.found _ _ receipt.form
      entry.1 (List.of_mem_zip member).1

  | composite head plain receipt =>
    exact arguments.2 id receipt.node present receipt.found receipt.form entry.1 (List.of_mem_zip member).1

theorem Boundary.impossible_composites
    (metadata : MetadataFor compiled.indexed named source directSites)
    (forms : ReachedCompositeForms source reached)
    (initializers : ∀ id, reached id →
      ¬ Nonempty (AcceptedContextualDirectReceipt.InitializerAt compiled.indexed (context compiled.indexed named) id))
    (arguments : ReachedCompositeArguments source reached)
    (rawMetadata : ReachedCompositeMetadata compiled.indexed named source reached)
    (requirements : ReachedMethodRequirements source reached)
    (operands : ReachedIndexOperands source reached)
    (ranges : ReachedConstructorRanges source reached)
    {tree : Trace root source scope reasonAt fuel id lowered}
    (boundary : Boundary tree) (present : reached id) : False := by
  induction boundary with
  | here head cause children => exact cause.impossible_composites metadata forms initializers rawMetadata requirements operands ranges present
  | child step children entry member next ih => exact ih (step.child_reached_composites arguments present member)

theorem Residual.impossible_composites {row : SourceSpecialization.SpecializedFunction}
    {prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row}
    {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    (residual : Residual prepared header directSites fuel source scope id lowered)
    (metadata : MetadataFor compiled.indexed prepared.named source directSites)
    (forms : ReachedCompositeForms source reached)
    (initializers : ∀ id, reached id → ¬ Nonempty (AcceptedContextualDirectReceipt.InitializerAt
      compiled.indexed (context compiled.indexed prepared.named) id))
    (arguments : ReachedCompositeArguments source reached)
    (rawMetadata : ReachedCompositeMetadata compiled.indexed prepared.named source reached)
    (requirements : ReachedMethodRequirements source reached)
    (operands : ReachedIndexOperands source reached)
    (ranges : ReachedConstructorRanges source reached)
    (present : reached id) : False :=
  residual.boundary.impossible_composites metadata forms initializers arguments rawMetadata requirements operands ranges present



end Solcore.SourceSemantics.CoreLowering.AcceptedNamedExpressionFlow
