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
  | form _ notLeaf notDirect _ =>
    rcases form with leaf | direct
    · exact notLeaf leaf
    · exact notDirect direct
  | initializer _ selected => exact initializers id present ⟨selected⟩
  | special selected outside =>
    rcases form with leaf | direct
    · have profile := AcceptedNamedExpressionPolicy.leaf_profile root.compilerPolicy metadata
        head.found leaf.view (Child root.selected.policy root.selected.lowerBody fuel
          (context compiled.indexed named)) (fuel + 1) scope reasonAt
      have same := head.selected.symm.trans profile.2.2
      rw [selected] at same
      cases same
    · exact outside direct

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
  | form _ notLeaf notDirect notIndirect =>
    rcases original with leaf | direct | indirect
    · exact notLeaf leaf
    · exact notDirect direct
    · exact notIndirect indirect
  | initializer _ selected => exact initializers id present ⟨selected⟩
  | special selected outside =>
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

theorem Step.child_reached_calls
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
  | child step children entry member next ih => exact ih (step.child_reached_calls arguments present member)

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

end Solcore.SourceSemantics.CoreLowering.AcceptedNamedExpressionFlow
