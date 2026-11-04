import Solcore.SourceSemantics.CoreLowering.AcceptedTrees
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.TerminalBodies
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.Bootstrap
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaPolicyRecipes
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.ExpressionBounds
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.CallerMethodSelection
import Solcore.SourceSemantics.CoreLowering.Internal.Accepted.ScopedSourceBodies
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.BranchingTrees
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.HeadersAndPrograms
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.RuntimeProfileFactories
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.NamedCollectors
import Solcore.SourceSemantics.CoreLowering.ActualBodyInvocation
import Solcore.SourceSemantics.CoreLowering.CallableAncestryPairedProfiles
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedTerminalStatements
import Solcore.SourceSemantics.CoreLowering.CallableIndexedAllocation
import Solcore.SourceSemantics.CoreLowering.TypedLexicalWhileTree
import Solcore.SourceSemantics.CoreLowering.CompatibleAssignmentStatementCertificates
import Solcore.SourceSemantics.CoreLowering.CompatibleBitNotStatementCertificates
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.OrdinaryBodies

/-!
# Accepted named bodies

Accepted named bodies: expression flow and policy, completion, finish, shape, syntax, bindings and admission, with body-invocation reads, allocation and snapshots.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.AcceptedBareBitNotHead
/-! The accepted compiler action supplies the complete bare bit-not head.
Its original target equality and independent Source typing determine the
writable runtime local, without equating the two Source records. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.AcceptedBareBitNotReceipt
open Core Frontend SourceInference

variable {policy : SourceCoreLoops.Policy} {fuel : Nat} {compilerSource source : TypedSource}
  {scope : SourceCoreLocalCell.Scope} {site : SourceCoreElaboration.ErrorSite}
  {assignment : AssignmentResolution} {output : Ty} {next code : Expr}
  {reasonAt : ExpressionId → Word} {context : SourceSemantics.Context}

/-- The actual compiler target and typed runtime target identify the same
ordinary writable local, even when their surrounding requirement metadata differs. -/
def Receipt.head
    (receipt : Receipt policy fuel compilerSource scope site assignment output next reasonAt code)
    (targetType : receipt.binder.scheme.body = assignment.target.type)
    (typed : SourceBitNotAssignmentValid source context assignment) :
    CompatibleBitNotStatements.Head context scope assignment where
  prepared := receipt.place
  index := receipt.index
  invalid := receipt.invalidUnary site assignment.target.root
  bare := receipt.bare
  layout := receipt.layout
  slot := receipt.slot
  writable := by
    rw [receipt.rootType, targetType]
    cases typed with
    | intro target _ =>
      cases target with
      | intro writable projections stored =>
        rw [receipt.bare] at projections
        cases projections
        simpa only [stored] using writable
  profile := .inl (by rw [receipt.rawType, receipt.sourceProfile]; rfl)

theorem Receipt.head_emitted
    (receipt : Receipt policy fuel compilerSource scope site assignment output next reasonAt code)
    (targetType : receipt.binder.scheme.body = assignment.target.type)
    (typed : SourceBitNotAssignmentValid source context assignment) :
    code = (receipt.head targetType typed).emit next output :=
  receipt.emitted

theorem Receipt.head_errors
    (receipt : Receipt policy fuel compilerSource scope site assignment output next reasonAt code)
    (targetType : receipt.binder.scheme.body = assignment.target.type)
    (typed : SourceBitNotAssignmentValid source context assignment)
    {faults : FunctionCalls.FaultRep}
    (diagnostic : faults (.invalidUnaryOperand .bitNot)
      (receipt.invalidUnary site assignment.target.root)) :
    (receipt.head targetType typed).Errors faults :=
  diagnostic

end Solcore.SourceSemantics.CoreLowering.AcceptedBareBitNotReceipt
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.AcceptedDirectExpressionReceipt
/-! Exact-step direct-call extraction from the accepted contextual compiler.
Only the special-hook result at the actual recursive child and fuel is used.
The receipt retains the original node, full selected row and ordered actions. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.AcceptedDirectExpressionReceipt
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedStagedDirectCallCertificates

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) : ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

/-- The actual ordinary branch needs a single successful special-hook bypass
at this occurrence. No statement about other callbacks or budgets is required. -/
theorem of_supported
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {compilation : SourceCoreFunctions.Context}
    {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id callee : ExpressionId}
    {ids : List ExpressionId} {instantiation : DeclarationInstantiation}
    {node : ExpressionNode} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (found : source.lookupExpression? id = some node)
    (form : node.form = .call callee ids (.declaration instantiation))
    (ordinary : Supported compilation.plan instantiation)
    (special : (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower compilation (Child policy body fuel compilation)
          (fuel + 1) source scope id reasonAt) = .ok none)
    (readPolicy : policy.readExpression source id =
      SourceCoreCompatibleDataExpressions.readExpression values.checked source id)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body (fuel + 1)
      compilation source scope id reasonAt = .ok lowered) :
    Nonempty (Receipt policy body fuel compilation values source scope id callee ids instantiation reasonAt lowered) := by
  have original := accepted
  have originalSpecial := special
  rw [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
  by_cases owner : id.occurrence.owner = source.owner
  · simp only [owner, ne_eq, not_true_eq_false, ↓reduceIte, found, bind, Except.bind, pure, Except.pure] at accepted
    have bypass := special
    cases hook : policy.lowerSpecial? <;> simp only [hook] at accepted bypass
    all_goals try rw [bypass] at accepted
    all_goals
      simp only [form] at accepted
      obtain ⟨pair, read, _remaining⟩ := bind_ok accepted
      rcases pair with ⟨other, type⟩
      have metadata := CompatibleExpressionReads.metadata_of_read (readPolicy.symm ▸ read)
      have same := Option.some.inj (metadata.found.symm.trans found)
      subst other
      obtain ⟨index, signature, specialized, codes, selected, record, arity, generated,
        parameter, result, emitted, output⟩ := NamedCalls.Arguments.call_of_accepted
          owner found read form originalSpecial original
      exact ⟨⟨node, output.symm ▸ Metadata.of_read metadata, form, ordinary, original, signature,
        index, specialized, (NamedCalls.selected_signature_target selected).1,
        (NamedCalls.selected_signature_target selected).2, record, arity, codes, generated, parameter,
        result.trans output.symm, emitted⟩⟩
  · simp [owner, bind, Except.bind] at accepted

end Solcore.SourceSemantics.CoreLowering.AcceptedDirectExpressionReceipt
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.AcceptedNamedExpressionFlow
/-! Expression receipts start with the actual selected special-hook result.
The original source occurrence and minimum child budget remain explicit. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.AcceptedNamedExpressionFlow
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedStagedDirectCallCertificates (Child)

abbrev specialAction (policy : SourceCoreFunctions.Policy) (body : SourceCoreFunctions.BodyLowerer)
    (fuel : Nat) (context : SourceCoreFunctions.Context) (source : TypedSource)
    (scope : SourceCoreLocalCell.Scope) (id : ExpressionId) (reasonAt : ExpressionId → Word) :=
  match policy.lowerSpecial? with
  | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
  | some lower => lower context (Child policy body fuel context) (fuel + 1) source scope id reasonAt

/-- The selected hook is observed at its actual arguments. A successful override
retains its exact result, without any assumption about other child actions. -/
structure Head (policy : SourceCoreFunctions.Policy) (body : SourceCoreFunctions.BodyLowerer)
    (fuel : Nat) (context : SourceCoreFunctions.Context) (source : TypedSource)
    (scope : SourceCoreLocalCell.Scope) (id : ExpressionId) (reasonAt : ExpressionId → Word)
    (lowered : SourceCoreBasic.LoweredExpr) where
  node : ExpressionNode
  found : source.lookupExpression? id = some node
  owner : id.occurrence.owner = source.owner
  special : Option SourceCoreBasic.LoweredExpr
  selected : specialAction policy body fuel context source scope id reasonAt = .ok special
  result : ∀ actual, special = some actual → lowered = actual
  accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body (fuel + 1)
    context source scope id reasonAt = .ok lowered

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) : ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

theorem Head.of_accepted
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {context : SourceCoreFunctions.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {reasonAt : ExpressionId → Word}
    {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body (fuel + 1)
      context source scope id reasonAt = .ok lowered) :
    Nonempty (Head policy body fuel context source scope id reasonAt lowered) := by
  have original := accepted
  rw [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
  by_cases owner : id.occurrence.owner = source.owner
  · simp only [owner, ne_eq, not_true_eq_false, ↓reduceIte] at accepted
    cases found : source.lookupExpression? id with
    | none => simp [found, bind, Except.bind] at accepted
    | some node =>
      simp only [found, bind, Except.bind, pure, Except.pure] at accepted
      cases hook : policy.lowerSpecial? with
      | none =>
        refine ⟨⟨node, found, owner, none, ?_, ?_, original⟩⟩
        · simp [specialAction, hook]
        · intro actual same
          cases same
      | some lower =>
        cases selected : lower context (Child policy body fuel context) (fuel + 1)
            source scope id reasonAt with
        | error error =>
          simp only [hook, selected] at accepted
          cases accepted
        | ok special =>
          refine ⟨⟨node, found, owner, special, ?_, ?_, original⟩⟩
          · simpa only [specialAction, hook] using selected
          · intro actual same
            rw [same] at selected
            simp only [hook, selected] at accepted
            exact (Except.ok.inj accepted).symm
  · simp [owner, bind, Except.bind] at accepted

/-- The actual contextual action exposes the same head after its genuine
predecessor budget has been recovered by the Header receipt. -/
theorem of_header {compiled : SourceCoreUnifiedCompilation.Compiled}
    {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    {instantiation : DeclarationInstantiation}
    {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
    {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : header.policy.lowerExpression fuel source scope id header.reasonAt = .ok lowered) :
    ∃ predecessor, fuel = predecessor + 1 ∧
      ∃ root : CallableIndexedOwnedContextualCompilerPolicyProfiles.RootPolicyReceipt
        (compiled := compiled) prepared.named prepared.diagnostics prepared.code prepared.compilation
        predecessor source scope id header.reasonAt lowered,
      Nonempty (Head root.selected.policy root.selected.lowerBody predecessor
        (CallableIndexedNamedGeneration.context compiled.indexed prepared.named)
        source scope id header.reasonAt lowered) := by
  obtain ⟨predecessor, same, ⟨root⟩⟩ :=
    CallableIndexedOwnedPreparedHeaderRootPolicyReceipts.at_accepted prepared aligned accepted
  exact ⟨predecessor, same, root, Head.of_accepted root.selected.accepted⟩

end Solcore.SourceSemantics.CoreLowering.AcceptedNamedExpressionFlow
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.AcceptedContextualDirectReceipt
/-! The actual contextual direct-call hook either selects an original local
initializer or exposes the same evidence action on the original source. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.AcceptedContextualDirectReceipt
open Core Frontend SourceInference
open CallableIndexedNamedGeneration
open CallableIndexedOwnedContextualLambdaPolicyRecipes
open CallableIndexedOwnedPreparedStagedDirectCallCertificates

structure InitializerAt {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked)
    (current : SourceCoreFunctions.Context) (id : ExpressionId) where
  binding : SourceCoreLocalPolymorphism.Binding
  found : (prepared.base.locals.bindings.find? fun candidate =>
    decide (candidate.caller = current.owner ∧ candidate.initializer = id)).filter
      (fun _ => (none : Option ExpressionId) ≠ some id) = some binding

/-- The special callback is the one retained by the actual compilation recipe.
The residual keeps its precise initializer selection; otherwise the evidence
receipt retains the original callee, arguments, dictionary and output path. -/
theorem of_special
    {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : CallableIndexedNamedGeneration.Prepared checked} {named : Named}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    (compilation : Compilation prepared named diagnostics namedCode)
    {rootFuel fuel : Nat} {policy : SourceCoreFunctions.Policy}
    {body : SourceCoreFunctions.BodyLowerer} {current : SourceCoreFunctions.Context}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {id callee : ExpressionId} {arguments : List ExpressionId}
    {instantiation : DeclarationInstantiation} {node : ExpressionNode}
    {reasonAt : ExpressionId → Word} {output : SourceCoreBasic.LoweredExpr}
    (recipe : PolicyRecipe compilation rootFuel policy)
    (found : source.lookupExpression? id = some node)
    (form : node.form = .call callee arguments (.declaration instantiation))
    (accepted : (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower current (Child policy body fuel current)
          (fuel + 1) source scope id reasonAt) = .ok (some output)) :
    Nonempty (CallableCoercionExpressionCertificates.Direct prepared.base.sourceProgram
      ((representation prepared).atContext named.signature.key []).expressions.projectType
      named.specialized current (Child policy body fuel current) (fuel + 1)
      source scope id callee arguments instantiation reasonAt
      (SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext []) node output) ∨
      Nonempty (InitializerAt prepared current id) := by
  rw [recipe.lowerSpecial] at accepted
  change special compilation rootFuel current (Child policy body fuel current)
    (fuel + 1) source scope id reasonAt = .ok (some output) at accepted
  have sameSource : SourceCoreGeneralFunctions.contextualSource prepared.base.sourceProgram
      current.plan prepared.base.locals current.owner none source id = .ok source := by
    simp [SourceCoreGeneralFunctions.contextualSource, found, form]
  unfold special at accepted
  simp only [sameSource, bind, Except.bind, found, pure, Except.pure] at accepted
  cases selected : (prepared.base.locals.bindings.find? fun candidate =>
      decide (candidate.caller = current.owner ∧ candidate.initializer = id)).filter
        (fun _ => (none : Option ExpressionId) ≠ some id) with
  | some binding => exact .inr ⟨⟨binding, selected⟩⟩
  | none =>
    rw [selected] at accepted
    cases evidence : SourceCoreEvidence.lowerWithProjector prepared.base.sourceProgram
        ((representation prepared).atContext named.signature.key []).expressions.projectType
        named.specialized current (Child policy body fuel current) (fuel + 1)
        source scope id reasonAt (SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext []) with
    | error error => simp [evidence] at accepted
    | ok value =>
      cases value with
      | none => simp [evidence, form] at accepted
      | some result =>
        simp only [evidence] at accepted
        cases accepted
        exact .inl (CallableCoercionExpressionCertificates.direct_of_accepted found form evidence)

end Solcore.SourceSemantics.CoreLowering.AcceptedContextualDirectReceipt
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.AcceptedContextualOperatorReceipt
/-! The selected contextual hook retains its actual overloaded operator method
and ordered operand actions. Initializer selection remains an exact alternative. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.AcceptedContextualOperatorReceipt
open Core Frontend SourceInference
open CallableIndexedNamedGeneration
open CallableIndexedOwnedContextualLambdaPolicyRecipes
open CallableIndexedOwnedContextualCompilerPolicyProfiles (RootPolicyReceipt)
open CallableIndexedOwnedPreparedStagedDirectCallCertificates (Child)
open AcceptedNamedExpressionFlow (Head specialAction)

def Form (form : ExpressionForm) : Prop :=
  (∃ operator operand, form = .unary operator operand) ∨
    (∃ operator left right, form = .binary left operator right)

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) : ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

/-- Only the actual selected callback is inspected. The original source is not
rewritten, and the method dictionary is retained by the existing receipt. -/
theorem of_special
    {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : CallableIndexedNamedGeneration.Prepared checked} {named : Named}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    (compilation : Compilation prepared named diagnostics namedCode)
    {rootFuel fuel : Nat} {policy : SourceCoreFunctions.Policy}
    {body : SourceCoreFunctions.BodyLowerer} {current : SourceCoreFunctions.Context}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {node : ExpressionNode}
    {reasonAt : ExpressionId → Word} {output : SourceCoreBasic.LoweredExpr}
    (recipe : PolicyRecipe compilation rootFuel policy)
    (found : source.lookupExpression? id = some node)
    (form : Form node.form) (coercions : node.coercions = [])
    (accepted : (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower current (Child policy body fuel current)
          (fuel + 1) source scope id reasonAt) = .ok (some output)) :
    Nonempty (CallablePreparedMethodSelection.Operator prepared.base.sourceProgram
      ((representation prepared).atContext named.signature.key []).expressions.projectType
      named.specialized current (Child policy body fuel current) (fuel + 1)
      source scope id reasonAt (SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext []) node output) ∨
      Nonempty (AcceptedContextualDirectReceipt.InitializerAt prepared current id) := by
  rw [recipe.lowerSpecial] at accepted
  change special compilation rootFuel current (Child policy body fuel current)
    (fuel + 1) source scope id reasonAt = .ok (some output) at accepted
  have sameSource : SourceCoreGeneralFunctions.contextualSource prepared.base.sourceProgram
      current.plan prepared.base.locals current.owner none source id = .ok source := by
    rcases form with ⟨operator, operand, original⟩ | ⟨operator, left, right, original⟩
    all_goals simp [SourceCoreGeneralFunctions.contextualSource, found, original]
  unfold special at accepted
  simp only [sameSource, bind, Except.bind, found, pure, Except.pure] at accepted
  cases selected : (prepared.base.locals.bindings.find? fun candidate =>
      decide (candidate.caller = current.owner ∧ candidate.initializer = id)).filter
        (fun _ => (none : Option ExpressionId) ≠ some id) with
  | some binding => exact .inr ⟨⟨binding, selected⟩⟩
  | none =>
    rw [selected] at accepted
    cases evidence : SourceCoreEvidence.lowerWithProjector prepared.base.sourceProgram
        ((representation prepared).atContext named.signature.key []).expressions.projectType
        named.specialized current (Child policy body fuel current) (fuel + 1)
        source scope id reasonAt (SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext []) with
    | error error => simp [evidence] at accepted
    | ok value =>
      cases value with
      | none =>
        rcases form with ⟨operator, operand, original⟩ | ⟨operator, left, right, original⟩
        all_goals simp [evidence, original] at accepted
      | some result =>
        simp only [evidence] at accepted
        cases accepted
        have ordinary := CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.ordinary_requirements coercions
        have nonempty : node.requirements ≠ [] := by
          intro empty
          rcases form with ⟨operator, operand, original⟩ | ⟨operator, left, right, original⟩
          all_goals simp [SourceCoreEvidence.lowerWithProjector, found, original, ordinary, coercions, empty] at evidence
        exact .inl (CallablePreparedMethodSelection.of_accepted found form ordinary nonempty evidence)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : Compilation compiled.indexed named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) named diagnostics namedCode compilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Word}
  {fuel : Nat} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}

/-- The existing method receipt records the original parent output and the
actual recursive child callback at this budget. -/
theorem of_head
    (head : Head root.selected.policy root.selected.lowerBody fuel (context compiled.indexed named)
      source scope id reasonAt lowered)
    (selected : head.special = some lowered)
    (form : Form head.node.form) (coercions : head.node.coercions = []) :
    Nonempty (CallableIndexedOwnedPreparedStagedOperatorMethodCertificates.Receipt
      root.selected.policy root.selected.lowerBody fuel (context compiled.indexed named)
      (.initial compiled.compatible.checked) source scope id reasonAt lowered) ∨
      Nonempty (AcceptedContextualDirectReceipt.InitializerAt compiled.indexed (context compiled.indexed named) id) := by
  have accepted := head.selected.trans (congrArg Except.ok selected)
  cases of_special compilation root.compilerPolicy head.found form coercions accepted with
  | inr initializer => exact .inr initializer
  | inl methods =>
    obtain ⟨method⟩ := methods
    have projected := method.suffix.outputProjection
    change SourceCoreCompatibleDataExpressions.projectType compiled.compatible.checked
      (.occurrence head.node.id.occurrence) head.node.type = .ok lowered.type at projected
    have actualPolicy : CallablePreparedMethodSelection.Operator compiled.indexed.base.sourceProgram
        ((representation compiled.indexed).atContext named.signature.key []).expressions.projectType
        named.specialized (context compiled.indexed named)
        (Child root.selected.policy root.selected.lowerBody fuel (context compiled.indexed named))
        (fuel + 1) source scope id reasonAt root.selected.policy.callables head.node lowered := by
      rw [root.selected.callables]
      exact method
    exact .inl (CallableIndexedOwnedPreparedStagedOperatorMethodCertificates.of_evidence
      coercions (CompatibleExpressionReads.projectType_of_accepted projected) actualPolicy accepted head.accepted)

/-- Ordinary compatible acceptance forces empty original requirements. This
excludes that exact branch at the fixture's authentic method occurrences. -/
theorem plain_requirements
    (head : Head root.selected.policy root.selected.lowerBody fuel (context compiled.indexed named)
      source scope id reasonAt lowered)
    (plain : head.special = none) (form : Form head.node.form) : head.node.requirements = [] := by
  have sameSource : SourceCoreGeneralFunctions.contextualSource compiled.indexed.base.sourceProgram
      (context compiled.indexed named).plan compiled.indexed.base.locals
      (context compiled.indexed named).owner none source id = .ok source := by
    rcases form with ⟨operator, operand, original⟩ | ⟨operator, left, right, original⟩
    all_goals simp [SourceCoreGeneralFunctions.contextualSource, head.found, original]
  have readPolicy : root.selected.policy.readExpression source id =
      SourceCoreCompatibleDataExpressions.readExpression compiled.compatible.checked source id := by
    rw [root.compilerPolicy.readExpression]
    simp only [sameSource, bind, Except.bind]
    rfl
  have accepted := head.accepted
  have selected := head.selected
  rw [plain] at selected
  rw [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
  simp only [head.owner, ne_eq, not_true_eq_false, ↓reduceIte, head.found,
    bind, Except.bind, pure, Except.pure] at accepted
  cases hook : root.selected.policy.lowerSpecial? <;>
    simp only [specialAction, hook] at selected accepted
  all_goals try rw [selected] at accepted
  all_goals
    rcases form with ⟨operator, operand, original⟩ | ⟨operator, left, right, original⟩
  all_goals
    simp only [original] at accepted
    obtain ⟨pair, read, _⟩ := bind_ok accepted
    obtain ⟨node, type⟩ := pair
    have actual := CompatibleExpressionReads.metadata_of_read (readPolicy ▸ read)
    have same := Option.some.inj (actual.found.symm.trans head.found)
    subst node
    exact actual.requirements

end Solcore.SourceSemantics.CoreLowering.AcceptedContextualOperatorReceipt
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.AcceptedNamedExpressionPolicy
/-! Original direct-call forms bypass contextual source normalization. Original
leaf forms construct their own syntax before using the retained metadata profile.
Neither producer requires a supplied recursive expression grammar. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.AcceptedNamedExpressionPolicy
open Core Frontend SourceInference
open CallableIndexedNamedGeneration
open CallableIndexedOwnedContextualLambdaPolicyRecipes
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)
open CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles (MetadataFor)

variable {checked : SourceCoreCompatibleCatalog.Checked}
  {prepared : CallableIndexedNamedGeneration.Prepared checked} {named : Named}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : Compilation prepared named diagnostics namedCode}
  {rootFuel : Nat} {policy : SourceCoreFunctions.Policy}
  {source : TypedSource} {id : ExpressionId} {node : ExpressionNode}

/-- A declaration call cannot enter local-reference normalization. The same
actual policy therefore reads its original Source occurrence directly. -/
theorem direct_read (recipe : PolicyRecipe compilation rootFuel policy)
    {callee : ExpressionId} {arguments : List ExpressionId} {instantiation : DeclarationInstantiation}
    (found : source.lookupExpression? id = some node)
    (form : node.form = .call callee arguments (.declaration instantiation)) :
    policy.readExpression source id = SourceCoreCompatibleDataExpressions.readExpression checked source id := by
  have same : SourceCoreGeneralFunctions.contextualSource prepared.base.sourceProgram
      (context prepared named).plan prepared.base.locals (context prepared named).owner
      none source id = .ok source := by
    simp [SourceCoreGeneralFunctions.contextualSource, found, form]
  rw [recipe.readExpression]
  simp only [same, bind, Except.bind]
  rfl

/-- Leaf syntax follows from the original read or atomic form. The existing
metadata profile then determines the actual reader and special callback at this
occurrence; no independent child grammar or local-read premise is supplied. -/
theorem leaf_profile (recipe : PolicyRecipe compilation rootFuel policy)
    {directSites : DeclarationInstantiation → Prop}
    (metadata : MetadataFor prepared named source directSites)
    (found : source.lookupExpression? id = some node)
    (form : CompatibleExpressionLiterals.Atomic node.form ∨
      ∃ name binder, node.form = .reference name (.local binder))
    (child : SourceCoreFunctions.ExpressionLowerer) (budget : Nat)
    (scope : SourceCoreLocalCell.Scope) (reasonAt : ExpressionId → Word) :
    GeneralSyntax source id directSites ∧
      policy.readExpression source id = SourceCoreCompatibleDataExpressions.readExpression checked source id ∧
      (match policy.lowerSpecial? with
        | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
        | some lower => lower (context prepared named) child budget source scope id reasonAt) = .ok none := by
  have leaf : CompatibleExpressionProducts.Syntax source id := by
    rcases form with atomic | ⟨name, binder, localForm⟩
    · exact .literal found atomic
    · exact .read found localForm
  refine ⟨.leaf leaf, ?_, ?_⟩
  · exact CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.read_policy recipe metadata (.leaf leaf)
  · rw [recipe.lowerSpecial]
    exact CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.special_none
      compilation rootFuel metadata (.leaf leaf) (GeneralSyntax.leaf_nonDirect leaf)
      (GeneralSyntax.leaf_nonOperator leaf) child budget scope reasonAt

end Solcore.SourceSemantics.CoreLowering.AcceptedNamedExpressionPolicy
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.AcceptedCompilerBodyCompletion
/-! Raw completion inspection distinguishes function tails from nested discarded
values. Stopped blocks and conditionals retain their original finite receipts. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.AcceptedCompilerBodyCompletion
open Frontend SourceInference ScopedSourceBodyStopping

/-- This inspection is bounded by the original occurrence table. A successful
result retains the complete finite stopping proof. -/
def stopped? (source : TypedSource) (statements : List StatementId) :=
  returnStopped? source (source.nodes.length + 1) statements

def Stops (source : TypedSource) (statements : List StatementId) : Prop :=
  (stopped? source statements).isSome = true

instance (source : TypedSource) (statements : List StatementId) : Decidable (Stops source statements) :=
  inferInstanceAs (Decidable ((stopped? source statements).isSome = true))

theorem Stops.original {source statements} (stops : Stops source statements) :
    ReturnStopped source statements := by
  unfold Stops at stops
  cases found : stopped? source statements with
  | none => simp [found] at stops
  | some proof => exact proof.down

/-- Only a true-mode final expression supplies a function result. -/
def notTail (mode : Bool) (_rest : List StatementId) : StatementForm → Bool
  | .expression _expression semicolon => semicolon || !mode
  | _ => true

def matchStops (source : TypedSource) (resolution : MatchResolution) : Bool :=
  resolution.cases.all (fun arm => (stopped? source arm.body).isSome) &&
    (resolution.defaultBody.any (fun statements => (stopped? source statements).isSome))

/-- The emitted outer suffix excludes nonfinal bare values in function mode.
Direct transfers omit their remaining roots, exactly as the compiler does. -/
def stopsHere : StatementForm → Bool
  | .returnStmt _ | .breakStmt | .continueStmt => true
  | _ => false

def tailForms? (source : TypedSource) : Bool → List StatementId → Bool
  | false, _ => true
  | true, [] => true
  | true, id :: rest =>
      match source.lookupStatement? id with
      | none => false
      | some node =>
          if stopsHere node.form then true else
          match node.form with
          | .expression _ false => rest.isEmpty
          | _ => tailForms? source true rest

def TailForms (source : TypedSource) (mode : Bool) (statements : List StatementId) : Prop :=
  tailForms? source mode statements = true

instance (source : TypedSource) (mode : Bool) (statements : List StatementId) :
    Decidable (TailForms source mode statements) := inferInstanceAs (Decidable (_ = true))

theorem TailForms.tail {source mode id node rest}
    (forms : TailForms source mode (id :: rest))
    (found : source.lookupStatement? id = some node)
    (continues : stopsHere node.form = false) : TailForms source mode rest := by
  cases mode with
  | false => simp [TailForms, tailForms?]
  | true =>
    cases form : node.form <;> simp_all [TailForms, tailForms?, stopsHere]
    rename_i expression semicolon
    cases semicolon with
    | true => exact forms
    | false => cases rest <;> simp_all [tailForms?]

theorem TailForms.discard_mode {source mode id node expression rest}
    (forms : TailForms source mode (id :: rest))
    (found : source.lookupStatement? id = some node)
    (form : node.form = .expression expression false)
    (notFinal : (mode && rest.isEmpty) = false) : mode = false := by
  cases mode with
  | false => rfl
  | true => simp [TailForms, tailForms?, found, form, stopsHere] at forms; simp [forms] at notFinal

inductive Finish (source : TypedSource) (expected : TypeSystem.Ty) :
    Bool → List StatementId → Prop where
  | nested (statements) : Finish source expected false statements
  | empty (unit : expected = .unit) : Finish source expected true []
  | returning {id node value rest} (found : source.lookupStatement? id = some node)
      (form : node.form = .returnStmt value) : Finish source expected true (id :: rest)
  | tail {id node expression} (found : source.lookupStatement? id = some node)
      (form : node.form = .expression expression false) (type : node.type = expected) :
      Finish source expected true [id]
  | prefix {id node rest} (found : source.lookupStatement? id = some node)
      (continuing : notTail true rest node.form = true)
      (remaining : Finish source expected true rest) : Finish source expected true (id :: rest)
  | block {id node body rest} (found : source.lookupStatement? id = some node)
      (form : node.form = .block body) (stopped : Stops source body)
      (tailForms : TailForms source true rest) :
      Finish source expected true (id :: rest)
  | matching {id node resolution fallback rest}
      (found : source.lookupStatement? id = some node) (form : node.form = .matchWith resolution)
      (present : resolution.defaultBody = some fallback)
      (arms : resolution.cases.all (fun arm => (stopped? source arm.body).isSome) = true)
      (default : Stops source fallback) (tailForms : TailForms source true rest) : Finish source expected true (id :: rest)
  | conditional {id node condition left right rest} (found : source.lookupStatement? id = some node)
      (form : node.form = .ifThen condition left (some right))
      (first : Stops source left) (second : Stops source right)
      (tailForms : TailForms source true rest) :
      Finish source expected true (id :: rest)

theorem Finish.forms {source expected mode statements}
    (finish : Finish source expected mode statements) : TailForms source mode statements := by
  induction finish with
  | nested => simp [TailForms, tailForms?]
  | empty => rfl
  | returning found form => simp [TailForms, tailForms?, found, form, stopsHere]
  | tail found form type => simp [TailForms, tailForms?, found, form, stopsHere]
  | @«prefix» id node rest found continuing remaining ih =>
    cases form : node.form <;>
      simp_all [TailForms, tailForms?, notTail, stopsHere]
  | block found form stopped tailForms => simpa [TailForms, tailForms?, found, form, stopsHere] using tailForms
  | matching found form present arms default tailForms => simpa [TailForms, tailForms?, found, form, stopsHere] using tailForms
  | conditional found form first second tailForms => simpa [TailForms, tailForms?, found, form, stopsHere] using tailForms

/-- Completion is checked at the original raw result, before native projection.
The remaining statement profile checks all visited operands and binders. -/
def finish? (source : TypedSource) (expected : TypeSystem.Ty) :
    (mode : Bool) → (statements : List StatementId) → Option (PLift (Finish source expected mode statements))
  | false, statements => some ⟨.nested statements⟩
  | true, [] => if unit : expected = .unit then some ⟨.empty unit⟩ else none
  | true, id :: rest =>
    match found : source.lookupStatement? id with
    | none => none
    | some node =>
      let next := do
        if continuing : notTail true rest node.form = true then
          let ⟨remaining⟩ ← finish? source expected true rest
          pure ⟨Finish.prefix found continuing remaining⟩
        else none
      match form : node.form with
      | .returnStmt _ => some ⟨.returning found form⟩
      | .expression expression false =>
        match restEq : rest with
        | [] => if type : node.type = expected then some ⟨.tail found form type⟩ else none
        | _ :: _ => by simpa only [restEq] using next
      | .block body =>
        if stops : Stops source body then
          if tailForms : TailForms source true rest then some ⟨.block found form stops tailForms⟩ else none
        else next
      | .matchWith resolution =>
        match present : resolution.defaultBody with
        | none => next
        | some fallback =>
          if arms : resolution.cases.all (fun arm => (stopped? source arm.body).isSome) = true then
            if default : Stops source fallback then
              if tailForms : TailForms source true rest then some ⟨.matching found form present arms default tailForms⟩ else none
            else next
          else next
      | .ifThen condition left (some right) =>
        if first : Stops source left then
          if second : Stops source right then
            if tailForms : TailForms source true rest then some ⟨.conditional found form first second tailForms⟩ else none
          else next
        else next
      | _ => next

end Solcore.SourceSemantics.CoreLowering.AcceptedCompilerBodyCompletion
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodyCompletion
/-! Completion is indexed by the original result type. The grammar receipt
retains actual dead suffixes while a stopped head supplies the execution path. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodyFlow
open Core Frontend SourceInference AcceptedCompilerBodyCompletion

variable {policy : SourceCoreLoops.Policy} {source : TypedSource} {result : Ty}
  {reasonAt : ExpressionId → Word}

def Tree.formed {mode : Bool} {escaped : Word} {fuel scope statements code}
    (tree : Tree policy source result reasonAt mode escaped fuel scope statements code) : Bool :=
  match tree with
  | .boundary .. | .assigning .. | .bitNotting .. | .forBoundary .. | .matching .. => false
  | .nil | .returning .. | .returnUnit .. | .breaking .. | .continuing .. | .tailValue .. => true
  | .initialized _ _ _ _ _ _ _ tail _ | .absent _ _ _ _ tail _ => tail.formed
  | .assigned _ _ _ tail _ _ | .projectedAssigned _ _ _ tail _ _ | .bitNotted _ _ _ tail _ _ | .projectedBitNotted _ _ _ tail _ _ | .discard _ _ _ _ _ tail => tail.formed
  | .valueDiscard _ _ _ _ _ _ tail => !mode && tail.formed
  | .block _ _ inner tail => inner.formed && tail.formed
  | .conditional _ _ _ _ _ left right tail => left.formed && right.formed && tail.formed
  | .matched _ _ receipt branches tail =>
      receipt.requests.attach.all (fun request => (branches request.val request.property).formed) && tail.formed
  | .whileLoop _ _ _ _ _ _ inner tail => inner.formed && tail.formed
  | .forLoop _ _ _ _ _ _ initial inner after tail => initial.closed && inner.formed && after.closed && tail.formed

def Tree.complete {mode : Bool} {escaped : Word} {fuel scope statements code}
    (tree : Tree policy source result reasonAt mode escaped fuel scope statements code)
    (expected : TypeSystem.Ty) : Bool :=
  match tree with
  | .nil => !mode || decide (expected = .unit)
  | .boundary .. | .assigning .. | .bitNotting .. | .forBoundary .. | .matching .. => false
  | .returning .. | .returnUnit .. | .breaking .. | .continuing .. => true
  | @Tree.tailValue _ _ _ _ _ _ _ _ node _ _ _ _ _ _ _ _ => decide (node.type = expected)
  | .initialized _ _ _ _ _ _ _ tail _ | .absent _ _ _ _ tail _ => tail.complete expected
  | .assigned _ _ _ tail _ _ | .projectedAssigned _ _ _ tail _ _ | .bitNotted _ _ _ tail _ _ | .projectedBitNotted _ _ _ tail _ _ | .discard _ _ _ _ _ tail => tail.complete expected
  | .valueDiscard _ _ _ _ _ _ tail => !mode && tail.complete expected
  | @Tree.block _ _ _ _ _ _ _ _ _ _ _ _ statements _ _ _ _ inner tail =>
      inner.complete expected && tail.formed &&
        (tail.complete expected || (stopped? source statements).isSome)
  | @Tree.conditional _ _ _ _ _ _ _ _ _ _ _ _ _ leftBody rightBody _ _ _ _ _ _ _ _ left right tail =>
      left.complete expected && right.complete expected && tail.formed &&
        (tail.complete expected ||
          ((stopped? source leftBody).isSome &&
            (stopped? source (rightBody.getD [])).isSome))
  | @Tree.matched _ _ _ _ _ _ _ _ _ _ _ _ resolution _ _ _ _ _ receipt branches tail =>
      receipt.requests.attach.all (fun request => (branches request.val request.property).complete expected) && tail.formed &&
        (tail.complete expected || matchStops source resolution)
  | .whileLoop _ _ _ _ _ _ inner tail => inner.complete expected && tail.complete expected
  | .forLoop _ _ _ _ _ _ initial inner after tail =>
      initial.closed && inner.complete expected && after.closed && tail.complete expected

private theorem and_true {left right : Bool} (both : left = true ∧ right = true) :
    (left && right) = true := by simp [both.1, both.2]

private theorem all_map {α : Type} {items : List α} {p q : α → Bool}
    (all : items.all p = true) (mapped : ∀ item ∈ items, p item = true → q item = true) :
    items.all q = true :=
  List.all_eq_true.mpr (fun item member => mapped item member (List.all_eq_true.mp all item member))

theorem Tree.complete_formed {mode : Bool} {escaped : Word} {fuel scope statements code}
    (tree : Tree policy source result reasonAt mode escaped fuel scope statements code)
    {expected : TypeSystem.Ty} (complete : tree.complete expected = true) : tree.formed = true := by
  induction tree with
  | nil | returning | returnUnit | breaking | continuing | tailValue => rfl
  | assigning | bitNotting | boundary | forBoundary | matching => cases complete
  | initialized _ _ _ _ _ _ _ _ _ ih | absent _ _ _ _ _ _ ih
  | assigned _ _ _ _ _ _ ih | projectedAssigned _ _ _ _ _ _ ih | bitNotted _ _ _ _ _ _ ih | projectedBitNotted _ _ _ _ _ _ ih | discard _ _ _ _ _ _ ih => exact ih complete
  | valueDiscard read form notTail child generated statementType remaining ih =>
    simp only [Tree.complete, Bool.and_eq_true] at complete
    exact and_true ⟨complete.1, ih complete.2⟩
  | block read form inner remaining innerIH _ =>
    simp only [Tree.complete, Bool.and_eq_true] at complete
    exact and_true ⟨innerIH complete.1.1, complete.1.2⟩
  | conditional read form child generated conditionType left right remaining leftIH rightIH _ =>
    simp only [Tree.complete, Bool.and_eq_true] at complete
    exact and_true ⟨and_true ⟨leftIH complete.1.1.1, rightIH complete.1.1.2⟩, complete.1.2⟩
  | matched read form receipt branches remaining branchIH _ =>
    simp only [Tree.complete, Bool.and_eq_true] at complete
    exact and_true ⟨all_map complete.1.1 (fun request _ => branchIH request.val request.property), complete.1.2⟩
  | whileLoop read form statementType child generated conditionType inner remaining innerIH tailIH =>
    simp only [Tree.complete, Bool.and_eq_true] at complete
    exact and_true ⟨innerIH complete.1, tailIH complete.2⟩
  | forLoop read form statementType child generated conditionType initial inner after remaining innerIH tailIH =>
    simp only [Tree.complete, Bool.and_eq_true] at complete
    exact and_true ⟨and_true ⟨and_true
      ⟨complete.1.1.1, innerIH complete.1.1.2⟩, complete.1.2⟩, tailIH complete.2⟩

theorem Tree.closed_complete {mode : Bool} {escaped : Word} {fuel scope statements code}
    (tree : Tree policy source result reasonAt mode escaped fuel scope statements code)
    (closed : tree.closed = true) (expected : TypeSystem.Ty) : tree.complete expected = true := by
  induction tree with
  | nil =>
    simp only [Tree.closed] at closed
    simp [Tree.complete, closed]
  | returning | returnUnit | breaking | continuing => rfl
  | tailValue | assigning | bitNotting | boundary | forBoundary | matching => cases closed
  | initialized _ _ _ _ _ _ _ _ _ ih | absent _ _ _ _ _ _ ih
  | assigned _ _ _ _ _ _ ih | projectedAssigned _ _ _ _ _ _ ih | bitNotted _ _ _ _ _ _ ih | projectedBitNotted _ _ _ _ _ _ ih | discard _ _ _ _ _ _ ih => exact ih closed
  | valueDiscard read form notTail child generated statementType remaining ih =>
    simp only [Tree.closed, Bool.and_eq_true] at closed
    exact and_true ⟨closed.1, ih closed.2⟩
  | block read form inner remaining innerIH tailIH =>
    simp only [Tree.closed, Bool.and_eq_true] at closed
    have tail := tailIH closed.2
    simp only [Tree.complete, innerIH closed.1, tail, remaining.complete_formed tail, Bool.true_and, Bool.true_or]
  | conditional read form child generated conditionType left right remaining leftIH rightIH tailIH =>
    simp only [Tree.closed, Bool.and_eq_true] at closed
    have tail := tailIH closed.2
    simp only [Tree.complete, leftIH closed.1.1, rightIH closed.1.2, tail,
      remaining.complete_formed tail, Bool.true_and, Bool.true_or]
  | matched read form receipt branches remaining branchIH tailIH =>
    simp only [Tree.closed, Bool.and_eq_true] at closed
    have tail := tailIH closed.2
    have heads := all_map closed.1 (fun request _ => branchIH request.val request.property)
    simp only [Tree.complete, heads, tail, remaining.complete_formed tail, Bool.true_and, Bool.true_or]
  | whileLoop read form statementType child generated conditionType inner remaining innerIH tailIH =>
    simp only [Tree.closed, Bool.and_eq_true] at closed
    exact and_true ⟨innerIH closed.1, tailIH closed.2⟩
  | forLoop read form statementType child generated conditionType initial inner after remaining innerIH tailIH =>
    simp only [Tree.closed, Bool.and_eq_true] at closed
    exact and_true ⟨and_true ⟨and_true
      ⟨closed.1.1.1, innerIH closed.1.1.2⟩, closed.1.2⟩, tailIH closed.2⟩

end Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodyFlow
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodyFinish
/-! Original completion receipts select the reachable suffix of the actual
compiler tree. All nested bodies keep their existing scoped evaluation mode. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodyFlow
open Core Frontend SourceInference AcceptedCompilerBodyCompletion

private theorem original_read {checked : SourceCoreCompatibleCatalog.Checked} {source : TypedSource}
    {id : StatementId} {node : StatementNode} {type : Ty}
    (accepted : SourceCoreCompatibleDataExpressions.readStatement checked source id = .ok (node, type)) :
    source.lookupStatement? id = some node := by
  unfold SourceCoreCompatibleDataExpressions.readStatement at accepted
  by_cases owner : id.occurrence.owner ≠ source.owner
  · simp [owner, throw, bind, Except.bind] at accepted
  · simp only [owner, ↓reduceIte, bind, Except.bind, pure, Except.pure] at accepted
    cases found : source.lookupStatement? id with
    | none => simp [found] at accepted
    | some actual =>
      simp only [found] at accepted
      obtain ⟨projected, _, same⟩ := CompatibleEncoding.bind_ok accepted
      cases same
      rfl

private def FinishAt (source : TypedSource) (expected : TypeSystem.Ty)
    (mode : Bool) (node : StatementNode) (rest : List StatementId) : Prop :=
  match node.form with
  | .returnStmt _ | .breakStmt | .continueStmt => True
  | .expression _ false => mode = false ∨ (rest = [] ∧ node.type = expected)
  | .block body => Finish source expected mode rest ∨ Stops source body
  | .ifThen _ left right => Finish source expected mode rest ∨
      (Stops source left ∧ Stops source (right.getD []))
  | .matchWith resolution => Finish source expected mode rest ∨ matchStops source resolution = true
  | _ => Finish source expected mode rest

private theorem finish_at {source expected mode id node rest}
    (finish : Finish source expected mode (id :: rest))
    (found : source.lookupStatement? id = some node) : FinishAt source expected mode node rest := by
  cases finish with
  | nested =>
    cases form : node.form <;> simp only [FinishAt, form]
    all_goals first | exact True.intro | exact Finish.nested _ | exact Or.inl (Finish.nested _) | exact Or.inl rfl | skip
    rename_i expression semicolon
    cases semicolon with
    | false => exact Or.inl True.intro
    | true => exact Finish.nested _
  | returning actual form =>
    cases Option.some.inj (actual.symm.trans found)
    simp only [FinishAt, form]
  | tail actual form type =>
    cases Option.some.inj (actual.symm.trans found)
    simp only [FinishAt, form]
    exact .inr ⟨True.intro, type⟩
  | «prefix» actual continuing remaining =>
    cases Option.some.inj (actual.symm.trans found)
    cases form : node.form <;> simp only [FinishAt, form]
    all_goals first | exact True.intro | exact remaining | exact Or.inl remaining | skip
    rename_i expression semicolon
    cases semicolon with
    | true => exact remaining
    | false => simp [form, notTail] at continuing
  | block actual form stopped _ =>
    cases Option.some.inj (actual.symm.trans found)
    simp only [FinishAt, form]
    exact .inr stopped
  | conditional actual form first second _ =>
    cases Option.some.inj (actual.symm.trans found)
    simp only [FinishAt, form, Option.getD_some]
    exact .inr ⟨first, second⟩
  | matching actual form present arms default _ =>
    cases Option.some.inj (actual.symm.trans found)
    simp only [FinishAt, form]
    exact .inr (by simp [matchStops, present, arms, Stops] at default ⊢; exact default)

/-- A formed tree retains every emitted child. Original completion determines
which continuation can be reached, without supplying a Source execution law. -/
theorem Tree.complete_of_formed {policy : SourceCoreLoops.Policy}
    {checked : SourceCoreCompatibleCatalog.Checked} {source : TypedSource} {result : Ty}
    {reasonAt : ExpressionId → Word} {mode : Bool} {escaped : Word}
    {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {statements : List StatementId} {code : Expr}
    (tree : Tree policy source result reasonAt mode escaped fuel scope statements code)
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement checked)
    (formed : tree.formed = true) {expected : TypeSystem.Ty}
    (finish : Finish source expected mode statements) : tree.complete expected = true := by
  induction tree generalizing expected with
  | nil => cases finish <;> simp_all [Tree.complete]
  | returning | returnUnit | breaking | continuing => rfl
  | assigning | bitNotting | boundary | forBoundary | matching => cases formed
  | tailValue read form _ _ _ _ =>
    have atHead := finish_at finish (original_read (readPolicy ▸ read))
    simp only [FinishAt, form, Bool.true_eq_false, false_or] at atHead
    simp only [Tree.complete, atHead.2, decide_true]
  | initialized read form _ _ _ _ _ _ _ ih =>
    have next := finish_at finish (original_read (readPolicy ▸ read))
    simp only [FinishAt, form] at next
    exact ih formed next
  | absent read form _ _ _ _ ih =>
    have next := finish_at finish (original_read (readPolicy ▸ read))
    simp only [FinishAt, form] at next
    exact ih formed next
  | assigned read form _ _ _ _ ih | projectedAssigned read form _ _ _ _ ih =>
    have next := finish_at finish (original_read (readPolicy ▸ read))
    simp only [FinishAt, form] at next
    exact ih formed next
  | bitNotted read form _ _ _ _ ih | projectedBitNotted read form _ _ _ _ ih =>
    have next := finish_at finish (original_read (readPolicy ▸ read))
    simp only [FinishAt, form] at next
    exact ih formed next
  | discard read form _ _ _ _ ih =>
    have next := finish_at finish (original_read (readPolicy ▸ read))
    simp only [FinishAt, form] at next
    exact ih formed next
  | @valueDiscard mode escaped fuel scope id rest node stored expression tail read form notTail child generated statementType remaining ih =>
    simp only [Tree.formed, Bool.and_eq_true] at formed
    have nested : mode = false := by simpa using formed.1
    cases nested
    simpa only [Tree.complete, Bool.not_false, Bool.true_and] using ih (expected := expected) formed.2 (.nested _)
  | block read form inner remaining innerIH tailIH =>
    simp only [Tree.formed, Bool.and_eq_true] at formed
    have child := innerIH (expected := expected) formed.1 (.nested _)
    have next := finish_at finish (original_read (readPolicy ▸ read))
    simp only [FinishAt, form] at next
    rcases next with next | stopped
    · simp only [Tree.complete, child, formed.2, tailIH formed.2 next, Bool.true_and, Bool.true_or]
    · simp only [Stops] at stopped
      simp only [Tree.complete, child, formed.2, stopped, Bool.true_and, Bool.or_true]
  | conditional read form _ _ _ left right remaining leftIH rightIH tailIH =>
    simp only [Tree.formed, Bool.and_eq_true] at formed
    have first := leftIH (expected := expected) formed.1.1 (.nested _)
    have second := rightIH (expected := expected) formed.1.2 (.nested _)
    have next := finish_at finish (original_read (readPolicy ▸ read))
    simp only [FinishAt, form] at next
    rcases next with next | stopped
    · simp only [Tree.complete, first, second, formed.2, tailIH formed.2 next, Bool.true_and, Bool.true_or]
    · simp only [Stops] at stopped
      simp only [Tree.complete, first, second, formed.2, stopped.1, stopped.2, Bool.true_and, Bool.or_true]
  | whileLoop read form _ _ _ _ inner remaining innerIH tailIH =>
    simp only [Tree.formed, Bool.and_eq_true] at formed
    have next := finish_at finish (original_read (readPolicy ▸ read))
    simp only [FinishAt, form] at next
    simp only [Tree.complete, innerIH (expected := expected) formed.1 (.nested _), tailIH formed.2 next, Bool.true_and]
  | matched read form receipt branches remaining branchIH tailIH =>
    simp only [Tree.formed, Bool.and_eq_true] at formed
    have children : receipt.requests.attach.all (fun request =>
        (branches request.val request.property).complete expected) = true := by
      apply List.all_eq_true.mpr
      intro request member
      exact branchIH request.val request.property
        (List.all_eq_true.mp formed.1 request member) (.nested _)
    have next := finish_at finish (original_read (readPolicy ▸ read))
    simp only [FinishAt, form] at next
    rcases next with next | stopped
    · simp only [Tree.complete, children, formed.2, tailIH formed.2 next, Bool.true_and, Bool.true_or]
    · simp only [Tree.complete, children, formed.2, stopped, Bool.true_and, Bool.or_true]
  | forLoop read form _ _ _ _ initial inner after remaining innerIH tailIH =>
    simp only [Tree.formed, Bool.and_eq_true] at formed
    have next := finish_at finish (original_read (readPolicy ▸ read))
    simp only [FinishAt, form] at next
    simp only [Tree.complete, formed.1.1.1, innerIH (expected := expected) formed.1.1.2 (.nested _),
      formed.1.2, tailIH formed.2 next, Bool.true_and]

theorem Tree.complete_of_formed_nested {policy : SourceCoreLoops.Policy}
    {checked : SourceCoreCompatibleCatalog.Checked} {source : TypedSource} {result : Ty}
    {reasonAt : ExpressionId → Word} {escaped : Word}
    {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {statements : List StatementId} {code : Expr}
    (tree : Tree policy source result reasonAt false escaped fuel scope statements code)
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement checked)
    (formed : tree.formed = true) (expected : TypeSystem.Ty) : tree.complete expected = true :=
  tree.complete_of_formed readPolicy formed (.nested statements)

end Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodyFlow
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodyShape
/-! Statement shape follows the actual compiler tree, including retained dead
suffixes. It does not assign a result type or a source context to those suffixes. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodyFlow
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedStagedBranchingTree
open CompatibleMatchCertificates GenericMatchChildren SourceCoreCompatibleDataMatches

/-- Actual header receipts already distinguish bare equal writes. -/
theorem Items.closed_shape {policy : SourceCoreLoops.Policy} {source : TypedSource}
    {site : SourceCoreElaboration.ErrorSite} {result : Ty} {reasonAt : ExpressionId → Word}
    {next : SourceCoreLocalCell.Scope → Except SourceCoreBasic.Error Expr}
    {finalScope : SourceCoreLocalCell.Scope} {finish : Expr} {fuel scope items code}
    (tree : Items policy source site result reasonAt next finalScope finish fuel scope items code)
    (closed : tree.closed = true) : ItemShape items := by
  induction tree with
  | nil => exact .nil
  | absent _ _ _ ih => exact .absent (ih closed)
  | initialized _ _ _ _ _ _ ih => exact .initialized (ih closed)
  | discard _ _ _ ih => exact .discard (ih closed)
  | assigning | bitNotting => cases closed
  | assigned _ receipt _ ih => exact .assign receipt.sourceProfile receipt.bare (ih closed)
  | projectedAssigned _ receipt _ ih => exact .assignProjected receipt.sourceProfile receipt.projected (ih closed)
  | bitNotted _ receipt _ ih => exact .bitNot receipt.sourceProfile receipt.bare (ih closed)
  | projectedBitNotted _ receipt _ ih => exact .bitNotProjected receipt.sourceProfile receipt.projected (ih closed)

private theorem arm_shapes {compilation : SourceCoreCompatibleDataMatches.Context}
    {source : TypedSource} {id : StatementId} {scope : SourceCoreLocalCell.Scope} {type : TypeSystem.Ty}
    {requests : List Request} {cases : List TypedMatchCase} {native : List (Pattern × Expr)}
    (certificate : Arms compilation source id scope type (Occurs requests) cases native)
    (children : ∀ request ∈ requests, Shape source false request.statements) :
    ∀ arm ∈ cases, Shape source false arm.body := by
  induction certificate with
  | nil => intro arm member; cases member
  | cons pattern typed body tail ih =>
    intro arm member
    rcases List.mem_cons.mp member with rfl | member
    · exact children _ body
    · exact ih arm member

private theorem match_shapes {compilation : SourceCoreCompatibleDataMatches.Context}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : StatementId}
    {resolution : MatchResolution} {result : Ty} {reason : Word}
    {expressions : ExpressionCertificate} {requests : List Request} {code : Expr}
    (certificate : Certificate compilation source scope id resolution result reason
      expressions (Occurs requests) code)
    (children : ∀ request ∈ requests, Shape source false request.statements) :
    (∀ arm ∈ resolution.cases, Shape source false arm.body) ∧
    (∀ statements, resolution.defaultBody = some statements → Shape source false statements) := by
  cases certificate with
  | matchWith _ _ _ _ _ _ _ _ _ _ _ arms fallback _ _ =>
    refine ⟨arm_shapes arms children, ?_⟩
    intro statements present
    rw [present] at fallback
    cases fallback with
    | some body => exact children _ body

/-- Each emitted branch and retained suffix supplies its own original shape.
Only the genuine compatible statement reader is needed beyond the formed tree. -/
theorem Tree.formed_shape {policy : SourceCoreLoops.Policy} {checked : SourceCoreCompatibleCatalog.Checked}
    {source : TypedSource} {result : Ty} {reasonAt : ExpressionId → Word} {mode : Bool} {escaped : Word}
    {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {statements : List StatementId} {code : Expr}
    (tree : Tree policy source result reasonAt mode escaped fuel scope statements code)
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement checked)
    (formed : tree.formed = true) : Shape source mode statements := by
  induction tree with
  | nil => exact .nil
  | returning read form _ _ _ _ => exact .returnValue _ (original_read (readPolicy ▸ read)) form
  | returnUnit read form _ _ => exact .returnUnit _ (original_read (readPolicy ▸ read)) form
  | breaking read form _ => exact .breaking _ (original_read (readPolicy ▸ read)) form
  | continuing read form _ => exact .continuing _ (original_read (readPolicy ▸ read)) form
  | tailValue read form _ _ _ _ => exact .tail (original_read (readPolicy ▸ read)) form
  | initialized read form _ _ _ _ _ _ _ ih =>
    exact .initialized (original_read (readPolicy ▸ read)) form (ih formed)
  | absent read form _ _ _ _ ih =>
    exact .absent (original_read (readPolicy ▸ read)) form (ih formed)
  | assigned read form _ _ receipt _ ih =>
    exact .assign (original_read (readPolicy ▸ read)) form receipt.sourceProfile receipt.bare (ih formed)
  | projectedAssigned read form _ _ receipt _ ih =>
    exact .assignProjected (original_read (readPolicy ▸ read)) form receipt.sourceProfile receipt.projected (ih formed)
  | bitNotted read form _ _ receipt _ ih =>
    exact .bitNot (original_read (readPolicy ▸ read)) form receipt.sourceProfile receipt.bare (ih formed)
  | projectedBitNotted read form _ _ receipt _ ih =>
    exact .bitNotProjected (original_read (readPolicy ▸ read)) form receipt.sourceProfile receipt.projected (ih formed)
  | discard read form _ _ _ _ ih =>
    exact .discard (original_read (readPolicy ▸ read)) form (.inl rfl) (ih formed)
  | valueDiscard read form _ _ _ _ remaining ih =>
    simp only [Tree.formed, Bool.and_eq_true] at formed
    exact .discard (original_read (readPolicy ▸ read)) form (.inr (by simpa using formed.1)) (ih formed.2)
  | block read form inner remaining innerIH tailIH =>
    simp only [Tree.formed, Bool.and_eq_true] at formed
    exact .block (original_read (readPolicy ▸ read)) form (innerIH formed.1) (tailIH formed.2)
  | conditional read form _ _ _ left right remaining leftIH rightIH tailIH =>
    simp only [Tree.formed, Bool.and_eq_true] at formed
    exact .conditional (original_read (readPolicy ▸ read)) form
      (leftIH formed.1.1) (rightIH formed.1.2) (tailIH formed.2)
  | whileLoop read form _ _ _ _ inner remaining innerIH tailIH =>
    simp only [Tree.formed, Bool.and_eq_true] at formed
    exact .whileLoop (original_read (readPolicy ▸ read)) form (innerIH formed.1) (tailIH formed.2)
  | matched read form receipt branches remaining branchIH tailIH =>
    simp only [Tree.formed, Bool.and_eq_true] at formed
    have children : ∀ request ∈ receipt.requests, Shape source false request.statements := by
      intro request member
      exact branchIH request member (List.all_eq_true.mp formed.1 ⟨request, member⟩ (by simp))
    obtain ⟨arms, fallback⟩ := match_shapes receipt.certificate children
    exact .matchWith (original_read (readPolicy ▸ read)) form arms fallback (tailIH formed.2)
  | forLoop read form _ _ _ _ initial inner after remaining innerIH tailIH =>
    simp only [Tree.formed, Bool.and_eq_true] at formed
    exact .forLoop (original_read (readPolicy ▸ read)) form
      (initial.closed_shape formed.1.1.1) (after.closed_shape formed.1.2)
      (innerIH formed.1.1.2) (tailIH formed.2)
  | boundary | assigning | bitNotting | forBoundary | matching => cases formed

end Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodyFlow
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.AcceptedNamedForItemsSyntax
/-! Genuine header actions and original typing recover each finite item receipt. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodyFlow
open Core Frontend SourceInference

theorem Items.scan {policy : SourceCoreLoops.Policy} {source : TypedSource}
    {site : SourceCoreElaboration.ErrorSite} {result : Ty} {reasonAt : ExpressionId → Word}
    {next : SourceCoreLocalCell.Scope → Except SourceCoreBasic.Error Expr}
    {finalScope : SourceCoreLocalCell.Scope} {finish : Expr}
    {fuel scope items code}
    (tree : Items policy source site result reasonAt next finalScope finish fuel scope items code)
    (closed : tree.closed = true) (unique : NodeOccurrencesUnique source)
    {approved : ExpressionId → Prop}
    (children : ∀ child ∈ tree.children, approved child.expression)
    (bindings : ∀ binding ∈ tree.bindings, RecursiveNamedStatementSyntaxFacts.BinderReceipt source binding.binder)
    {control : ControlContext} {context final : SourceSemantics.Context}
    (typed : ForItemsHaveType source control context items final) :
    ScopedSourceForItemsAdmission.Scan source approved items := by
  induction tree generalizing context final with
  | nil => exact .nil
  | absent projected remaining allocated ih =>
      have binder := bindings ⟨_, _, _, projected⟩ (by simp [Items.bindings])
      cases typed with
      | cons head tail =>
        exact .absent binder.1 binder.2.1 binder.2.2
          (ih closed (fun child member => children child (by simpa [Items.children] using member))
            (fun binding member => bindings binding (by simp [Items.bindings, member])) tail)
  | initialized projected child generated childType remaining allocated ih =>
      have binder := bindings ⟨_, _, _, projected⟩ (by simp [Items.bindings])
      cases typed with
      | cons head tail =>
        cases head with
        | letInitialized value _ _ _ =>
          obtain ⟨node, contains, same⟩ := value.stored_type
          exact .initialized binder.1 binder.2.1 binder.2.2
            (lookupExpression?_complete unique contains) same
            (children ⟨_, _, _, child, generated⟩ (by simp [Items.children]))
            (ih closed (fun child member => children child (by simp [Items.children, member]))
              (fun binding member => bindings binding (by simp [Items.bindings, member])) tail)
        | letInitializedGeneralized poly _ _ _ _ => exact False.elim (poly binder.2.1)
  | discard child generated remaining ih =>
      cases typed with
      | cons head tail =>
        cases head with
        | expression value =>
          obtain ⟨node, contains, same⟩ := value.stored_type
          exact .discard (lookupExpression?_complete unique contains)
            (children ⟨_, _, _, child, generated⟩ (by simp [Items.children]))
            (ih closed (fun child member => children child (by simp [Items.children, member]))
              (fun binding member => bindings binding (by simpa [Items.bindings] using member)) tail)
  | assigning => cases closed
  | assigned remaining receipt targetType ih =>
      cases typed with
      | cons head tail =>
        cases head with
        | assignValue assignment =>
          obtain ⟨_, _, value, _⟩ :=
            ScopedSourceForItemsAdmission.assignment_facts receipt.declaration targetType receipt.bare assignment
          obtain ⟨node, contains, same⟩ := value.stored_type
          exact .assign receipt.declaration targetType receipt.sourceProfile receipt.bare
            (lookupExpression?_complete unique contains) same
            (children ⟨_, _, _, receipt.child, receipt.generated⟩ (by simp [Items.children]))
            (ih closed (fun child member => children child (by simp [Items.children, member]))
              (fun binding member => bindings binding (by simpa only [Items.bindings] using member)) tail)

  | projectedAssigned remaining receipt route ih =>
      cases typed with
      | cons head tail =>
        cases head with
        | assignValue assignment =>
          obtain ⟨_, _, value, _⟩ :=
            ScopedSourceForItemsAdmission.projected_assignment_facts unique receipt.description.binding route assignment
          obtain ⟨node, contains, same⟩ := value.stored_type
          refine .assignProjected receipt.description.binding route receipt.sourceProfile receipt.projected ?_
            (lookupExpression?_complete unique contains) same
            (children ⟨_, _, _, receipt.child, receipt.generated⟩ (by simp [Items.children]))
            (ih closed (fun child member => children child (by simp [Items.children, member]))
              (fun binding member => bindings binding (by simpa only [Items.bindings] using member)) tail)
          intro key member
          rw [← receipt.keyIds, ← keyChildren_ids receipt.keysGenerated] at member
          obtain ⟨child, present, same⟩ := List.mem_map.mp member
          subst key
          exact children child (by simp [Items.children, present])

  | projectedBitNotted remaining receipt route ih =>
      cases typed with
      | cons head tail =>
        refine .bitNotProjected receipt.description.binding route receipt.sourceProfile receipt.projected ?_
          (ih closed (fun child member => children child (by simp [Items.children, member]))
            (fun binding member => bindings binding (by simpa only [Items.bindings] using member)) tail)
        intro key member
        rw [← receipt.keyIds, ← keyChildren_ids receipt.keysGenerated] at member
        obtain ⟨child, present, same⟩ := List.mem_map.mp member
        subst key
        exact children child (by simp [Items.children, present])

  | bitNotting => cases closed
  | bitNotted remaining receipt targetType ih =>
      cases typed with
      | cons head tail =>
        exact .bitNot receipt.declaration targetType receipt.sourceProfile receipt.bare
          (ih closed (fun child member => children child (by simpa only [Items.children] using member))
            (fun binding member => bindings binding (by simpa only [Items.bindings] using member)) tail)

end Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodyFlow
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodySyntax
/-! The compiler-issued tree supplies statement shape. Independent original
Source typing supplies annotations and lexical context changes. The remaining
inputs concern actual expression children and allocated binder declarations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodyFlow
open Core Frontend SourceInference
open CompatibleEncoding (bind_ok)

/-- The real compatible reader returns the original stored node. -/
theorem read_found {checked : SourceCoreCompatibleCatalog.Checked} {source : TypedSource}
    {id : StatementId} {node : StatementNode} {type : Ty}
    (accepted : SourceCoreCompatibleDataExpressions.readStatement checked source id = .ok (node, type)) :
    source.lookupStatement? id = some node := by
  unfold SourceCoreCompatibleDataExpressions.readStatement at accepted
  by_cases owner : id.occurrence.owner ≠ source.owner
  · simp [owner, throw, bind, Except.bind] at accepted
  · simp only [owner, ↓reduceIte, bind, Except.bind, pure, Except.pure] at accepted
    cases found : source.lookupStatement? id with
    | none => simp [found] at accepted
    | some actual =>
        simp only [found] at accepted
        obtain ⟨projected, _, same⟩ := bind_ok accepted
        cases same
        rfl

private theorem head_tail {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {rest : List StatementId} {facts : BodyFacts}
    (typed : StatementsHaveType source control context (id :: rest) final facts) :
    ∃ middle headFacts tailFacts, StatementHasType source control context id middle headFacts ∧
      StatementsHaveType source control middle rest final tailFacts := by
  cases typed with
  | singleton head => exact ⟨_, _, _, head, .nil _ _⟩
  | cons head tail => exact ⟨_, _, _, head, tail⟩

private theorem form_at {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {facts : StatementFacts} {node : StatementNode}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (typed : StatementHasType source control context id final facts) :
    Dynamic.StatementHasType.FormTyping source control context node.form final := by
  obtain ⟨actual, contains, original⟩ := Dynamic.StatementHasType.formTyping typed
  cases Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  exact original

private theorem returned_annotation {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {facts : StatementFacts}
    {node : StatementNode} {expression : Option ExpressionId}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (form : node.form = .returnStmt expression)
    (typed : StatementHasType source control context id final facts) : node.type = control.returnType := by
  cases typed
  all_goals
    have same := Option.some.inj ((lookupStatement?_complete unique (by assumption)).symm.trans found)
    cases same
    simp_all

private theorem discard_annotation {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {facts : StatementFacts}
    {node : StatementNode} {expression : ExpressionId}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (form : node.form = .expression expression true)
    (typed : StatementHasType source control context id final facts) : node.type = .unit := by
  cases typed
  all_goals
    have same := Option.some.inj ((lookupStatement?_complete unique (by assumption)).symm.trans found)
    cases same
    simp_all

private theorem value_annotation {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {facts : StatementFacts}
    {node : StatementNode} {expression : ExpressionId}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (form : node.form = .expression expression false)
    (typed : StatementHasType source control context id final facts) :
    ExpressionHasType source context expression node.type := by
  cases typed
  all_goals
    have same := Option.some.inj ((lookupStatement?_complete unique (by assumption)).symm.trans found)
    cases same
    simp_all

private theorem conditional_annotation {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {facts : StatementFacts}
    {node : StatementNode} {condition : ExpressionId}
    {left : List StatementId} {right : Option (List StatementId)}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (form : node.form = .ifThen condition left right)
    (typed : StatementHasType source control context id final facts) :
    node.type = .unit ∨ node.type = control.returnType := by
  cases typed
  all_goals
    have same := Option.some.inj ((lookupStatement?_complete unique (by assumption)).symm.trans found)
    cases same
    simp_all
  all_goals
    split at * <;> simp_all

private theorem for_annotation {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {facts : StatementFacts}
    {node : StatementNode} {initializer post : List ForItemForm} {condition : ExpressionId} {body : List StatementId}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (form : node.form = .forLoop initializer condition post body)
    (typed : StatementHasType source control context id final facts) : node.type = .unit := by
  cases typed
  all_goals
    have same := Option.some.inj ((lookupStatement?_complete unique (by assumption)).symm.trans found)
    cases same
    simp_all

/-- The support boundary is tested on the issued compiler tree. No separate
statement recognizer result or preconstructed body shape occurs here. -/
theorem Tree.scan_complete {policy : SourceCoreLoops.Policy} {checked : SourceCoreCompatibleCatalog.Checked}
    {source : TypedSource} {result : Ty} {reasonAt : ExpressionId → Word} {mode : Bool} {escaped : Word}
    {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {statements : List StatementId} {code : Expr}
    (tree : Tree policy source result reasonAt mode escaped fuel scope statements code)
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement checked)
    {control : ControlContext}
    (closed : tree.complete control.returnType = true) (unique : NodeOccurrencesUnique source)
    (ownership : LocalIdentityOwnership source)
    {approved : ExpressionId → Prop}
    (children : ∀ child ∈ tree.children, approved child.expression)
    (bindings : ∀ binding ∈ tree.bindings, RecursiveNamedStatementSyntaxFacts.BinderReceipt source binding.binder)
    {context final : SourceSemantics.Context} {facts : BodyFacts}
    (typed : StatementsHaveType source control context statements final facts) :
    ScopedSourceBodyAdmission.Scan source approved control.returnType mode statements := by
  induction tree generalizing control context final facts with
  | @nil actualMode _ _ _ =>
      cases actualMode with
      | false => exact .nil (.inl rfl)
      | true => exact .nil (.inr (by simpa [Tree.complete] using closed))
  | breaking read form _ => exact .breaking _ (read_found (readPolicy ▸ read)) form
  | continuing read form _ => exact .continuing _ (read_found (readPolicy ▸ read)) form
  | boundary | assigning | bitNotting | forBoundary | matching => cases closed
  | returning read form statementType child generated childType =>
      have found := read_found (readPolicy ▸ read)
      obtain ⟨_, _, _, head, _⟩ := head_tail typed
      have annotation := returned_annotation unique found form head
      have original := form_at unique found head
      rw [form] at original
      cases original with
      | returnValue value =>
          obtain ⟨node, contains, same⟩ := value.stored_type
          exact .returning _ found form annotation (lookupExpression?_complete unique contains) same
            (children ⟨_, _, _, child, generated⟩ (by simp [Tree.children]))
  | returnUnit read form statementType unitType =>
      have found := read_found (readPolicy ▸ read)
      obtain ⟨_, _, _, head, _⟩ := head_tail typed
      have annotation := returned_annotation unique found form head
      have original := form_at unique found head
      rw [form] at original
      cases original with
      | returnUnit result => exact .returnUnit _ found form (annotation.trans result) result
  | initialized read form statementType projected child generated childType remaining allocated ih =>
      have found := read_found (readPolicy ▸ read)
      have binder := bindings ⟨_, _, _, projected⟩ (by simp [Tree.bindings])
      obtain ⟨_, _, _, head, tail⟩ := head_tail typed
      have original := form_at unique found head
      rw [form] at original
      cases original with
      | letInitialized value _ _ =>
          obtain ⟨node, contains, same⟩ := value.stored_type
          exact .initialized found form binder.1 binder.2.1 binder.2.2
            (lookupExpression?_complete unique contains) same
            (children ⟨_, _, _, child, generated⟩ (by simp [Tree.children]))
            (ih closed (fun child member => children child (by simp [Tree.children, member]))
              (fun binding member => bindings binding (by simp [Tree.bindings, member])) tail)
      | letInitializedGeneralized poly _ _ _ _ => exact False.elim (poly binder.2.1)
  | absent read form statementType projected remaining allocated ih =>
      have found := read_found (readPolicy ▸ read)
      have binder := bindings ⟨_, _, _, projected⟩ (by simp [Tree.bindings])
      obtain ⟨_, _, _, head, tail⟩ := head_tail typed
      have original := form_at unique found head
      rw [form] at original
      cases original with
      | letUninitialized _ _ =>
          exact .absent found form binder.1 binder.2.1 binder.2.2
            (ih closed (fun child member => children child (by simpa [Tree.children] using member))
              (fun binding member => bindings binding (by simp [Tree.bindings, member])) tail)

  | assigned read form statementType remaining receipt targetType ih =>
      have found := read_found (readPolicy ▸ read)
      obtain ⟨_, _, _, head, tail⟩ := head_tail typed
      have original := form_at unique found head
      rw [form] at original
      cases original with
      | assignValue assignment =>
        obtain ⟨_, _, value, _⟩ :=
          ScopedSourceForItemsAdmission.assignment_facts receipt.declaration targetType receipt.bare assignment
        obtain ⟨node, contains, same⟩ := value.stored_type
        exact .assign found form receipt.declaration targetType receipt.sourceProfile receipt.bare
          (lookupExpression?_complete unique contains) same
          (children ⟨_, _, _, receipt.child, receipt.generated⟩ (by simp [Tree.children]))
          (ih closed (fun child member => children child (by simp [Tree.children, member]))
            (fun binding member => bindings binding (by simpa only [Tree.bindings] using member)) tail)
  | projectedAssigned read form statementType remaining receipt route ih =>
      have found := read_found (readPolicy ▸ read)
      obtain ⟨_, _, _, head, tail⟩ := head_tail typed
      have original := form_at unique found head
      rw [form] at original
      cases original with
      | assignValue assignment =>
        obtain ⟨_, _, value, _⟩ :=
          ScopedSourceForItemsAdmission.projected_assignment_facts unique receipt.description.binding route assignment
        obtain ⟨node, contains, same⟩ := value.stored_type
        refine .assignProjected found form receipt.description.binding route receipt.sourceProfile receipt.projected ?_
          (lookupExpression?_complete unique contains) same
          (children ⟨_, _, _, receipt.child, receipt.generated⟩ (by simp [Tree.children]))
          (ih closed (fun child member => children child (by simp [Tree.children, member]))
            (fun binding member => bindings binding (by simpa only [Tree.bindings] using member)) tail)
        intro key member
        rw [← receipt.keyIds, ← keyChildren_ids receipt.keysGenerated] at member
        obtain ⟨child, present, same⟩ := List.mem_map.mp member
        subst key
        exact children child (by simp [Tree.children, present])
  | projectedBitNotted read form statementType remaining receipt route ih =>
      have found := read_found (readPolicy ▸ read)
      obtain ⟨_, _, _, head, tail⟩ := head_tail typed
      have original := form_at unique found head
      rw [form] at original
      cases original with
      | assignBitNot assignment =>
        refine .bitNotProjected found form receipt.description.binding route receipt.sourceProfile receipt.projected ?_
          (ih closed (fun child member => children child (by simp [Tree.children, member]))
            (fun binding member => bindings binding (by simpa only [Tree.bindings] using member)) tail)
        intro key member
        rw [← receipt.keyIds, ← keyChildren_ids receipt.keysGenerated] at member
        obtain ⟨child, present, same⟩ := List.mem_map.mp member
        subst key
        exact children child (by simp [Tree.children, present])

  | bitNotted read form statementType remaining receipt targetType ih =>
      have found := read_found (readPolicy ▸ read)
      obtain ⟨_, _, _, head, tail⟩ := head_tail typed
      have original := form_at unique found head
      rw [form] at original
      cases original with
      | assignBitNot assignment =>
        exact .bitNot found form receipt.declaration targetType receipt.sourceProfile receipt.bare
          (ih closed (fun child member => children child (by simpa only [Tree.children] using member))
            (fun binding member => bindings binding (by simpa only [Tree.bindings] using member)) tail)
  | discard read form child generated statementType remaining ih =>
      have found := read_found (readPolicy ▸ read)
      obtain ⟨_, _, _, head, tail⟩ := head_tail typed
      have annotation := discard_annotation unique found form head
      have original := form_at unique found head
      rw [form] at original
      cases original with
      | expressionDiscard value =>
          obtain ⟨node, contains, same⟩ := value.stored_type
          exact .discard found form (.inl rfl) (by simpa only [Bool.true_eq, ↓reduceIte] using annotation)
            (lookupExpression?_complete unique contains)
            (children ⟨_, _, _, child, generated⟩ (by simp [Tree.children]))
            (ih closed (fun child member => children child (by simp [Tree.children, member]))
              (fun binding member => bindings binding (by simpa only [Tree.bindings] using member)) tail)
  | tailValue read form child generated statementType childType =>
      have found := read_found (readPolicy ▸ read)
      have raw : _ = control.returnType := of_decide_eq_true closed
      obtain ⟨_, _, _, head, _⟩ := head_tail typed
      have value := value_annotation unique found form head
      obtain ⟨node, contains, same⟩ := value.stored_type
      exact .tail found form raw (lookupExpression?_complete unique contains) (same.trans raw)
        (children ⟨_, _, _, child, generated⟩ (by simp [Tree.children]))
  | valueDiscard read form notTail child generated statementType remaining ih =>
      have found := read_found (readPolicy ▸ read)
      have both := closed
      simp only [Tree.complete, Bool.and_eq_true] at both
      obtain ⟨_, _, _, head, tail⟩ := head_tail typed
      have value := value_annotation unique found form head
      obtain ⟨node, contains, same⟩ := value.stored_type
      exact .discard found form (.inr (by simpa using both.1)) (by simpa using same.symm)
        (lookupExpression?_complete unique contains)
        (children ⟨_, _, _, child, generated⟩ (by simp [Tree.children]))
        (ih both.2 (fun child member => children child (by simp [Tree.children, member]))
          (fun binding member => bindings binding (by simpa only [Tree.bindings] using member)) tail)
  | block read form inner remaining innerIH tailIH =>
      have found := read_found (readPolicy ▸ read)
      have both := closed
      simp only [Tree.complete, Bool.and_eq_true, Bool.or_eq_true] at both
      obtain ⟨_, _, _, head, tail⟩ := head_tail typed
      have original := form_at unique found head
      rw [form] at original
      cases original with
      | block body =>
          have innerScan := innerIH both.1.1
            (fun child member => children child (by simp [Tree.children, member]))
            (fun binding member => bindings binding (by simp [Tree.bindings, member])) body
          rcases both.2 with tailComplete | stopped
          · exact .block found form innerScan
              (tailIH tailComplete
                (fun child member => children child (by simp [Tree.children, member]))
                (fun binding member => bindings binding (by simp [Tree.bindings, member])) tail)
          · have stop := AcceptedCompilerBodyCompletion.Stops.original stopped
            exact .terminalBlock found form
              (ScopedSourceBodyAdmission.stopped_statement_result unique found (.block found form stop) head)
              innerScan stop (remaining.formed_shape readPolicy both.1.2)
  | conditional read form child generated conditionType left right remaining leftIH rightIH tailIH =>
      have found := read_found (readPolicy ▸ read)
      have allComplete := closed
      simp only [Tree.complete, Bool.and_eq_true, Bool.or_eq_true] at allComplete
      obtain ⟨_, _, _, head, tail⟩ := head_tail typed
      have annotation := conditional_annotation unique found form head
      have original := form_at unique found head
      rw [form] at original
      cases original with
      | ifWithoutElse condition body =>
          obtain ⟨node, contains, same⟩ := condition.stored_type
          have tailComplete := allComplete.2.resolve_right (by
            intro stopped
            have impossible := (AcceptedCompilerBodyCompletion.Stops.original stopped.2).nonempty
            exact impossible rfl)
          exact .conditional found form annotation (lookupExpression?_complete unique contains) same
            (children ⟨_, _, _, child, generated⟩ (by simp [Tree.children]))
            (leftIH allComplete.1.1.1
              (fun child member => children child (by simp [Tree.children, member]))
              (fun binding member => bindings binding (by simp [Tree.bindings, member])) body)
            (rightIH allComplete.1.1.2
              (fun child member => children child (by simp [Tree.children, member]))
              (fun binding member => bindings binding (by simp [Tree.bindings, member])) (.nil control context))
            (tailIH tailComplete
              (fun child member => children child (by simp [Tree.children, member]))
              (fun binding member => bindings binding (by simp [Tree.bindings, member])) tail)
      | ifWithElse condition first second =>
          obtain ⟨node, contains, same⟩ := condition.stored_type
          have firstScan := leftIH allComplete.1.1.1
            (fun child member => children child (by simp [Tree.children, member]))
            (fun binding member => bindings binding (by simp [Tree.bindings, member])) first
          have secondScan := rightIH allComplete.1.1.2
            (fun child member => children child (by simp [Tree.children, member]))
            (fun binding member => bindings binding (by simp [Tree.bindings, member])) second
          rcases allComplete.2 with tailComplete | stopped
          · exact .conditional found form annotation (lookupExpression?_complete unique contains) same
              (children ⟨_, _, _, child, generated⟩ (by simp [Tree.children])) firstScan secondScan
              (tailIH tailComplete
                (fun child member => children child (by simp [Tree.children, member]))
                (fun binding member => bindings binding (by simp [Tree.bindings, member])) tail)
          · have firstStop := AcceptedCompilerBodyCompletion.Stops.original stopped.1
            have secondStop := AcceptedCompilerBodyCompletion.Stops.original stopped.2
            exact .terminalConditional found form
              (ScopedSourceBodyAdmission.stopped_statement_result unique found
                (.conditional found form firstStop secondStop) head)
              (lookupExpression?_complete unique contains) same
              (children ⟨_, _, _, child, generated⟩ (by simp [Tree.children])) firstScan secondScan
              firstStop secondStop (remaining.formed_shape readPolicy allComplete.1.2)
  | whileLoop read form statementType child generated conditionType inner remaining innerIH tailIH =>
      have found := read_found (readPolicy ▸ read)
      have both : inner.complete control.returnType = true ∧ remaining.complete control.returnType = true := by simpa only [Tree.complete, Bool.and_eq_true_iff] using closed
      obtain ⟨innerClosed, tailClosed⟩ := both
      obtain ⟨_, _, _, head, tail⟩ := head_tail typed
      have original := form_at unique found head
      rw [form] at original
      cases original with
      | whileLoop condition body =>
        obtain ⟨node, contains, same⟩ := condition.stored_type
        exact .whileLoop found form (lookupExpression?_complete unique contains) same
          (children ⟨_, _, _, child, generated⟩ (by simp [Tree.children]))
          (innerIH (control := control.enterLoop) innerClosed
            (fun child member => children child (by simp [Tree.children, member]))
            (fun binding member => bindings binding (by simp [Tree.bindings, member])) body)
          (tailIH tailClosed
            (fun child member => children child (by simp [Tree.children, member]))
            (fun binding member => bindings binding (by simp [Tree.bindings, member])) tail)

  | matched read form receipt branches remaining branchIH tailIH =>
      have found := read_found (readPolicy ▸ read)
      have allComplete := closed
      simp only [Tree.complete, Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true] at allComplete
      obtain ⟨scrutinee, scrutineeFound⟩ := ScopedSourceMatchAdmission.scrutinee_found receipt.certificate
      obtain ⟨_, _, _, head, tail⟩ := head_tail typed
      obtain ⟨same, caseFacts, _, caseTyped, defaultTyped⟩ :=
        ScopedSourceMatchAdmission.statement_sites unique found form scrutineeFound head
      subst_vars
      have childScans : ∀ request ∈ receipt.requests,
          ScopedSourceBodyAdmission.Scan source approved control.returnType false request.statements := by
        intro request member
        obtain ⟨child, last, bodyFacts, _, body⟩ := ScopedSourceMatchAdmission.original_context
          caseTyped defaultTyped (receipt.original request member)
        exact branchIH request member (allComplete.1.1 ⟨request, member⟩ (List.mem_attach _ _))
          (fun entry present => children entry (by
            simp only [Tree.children, List.mem_cons, List.mem_append]
            exact .inr (.inl (List.mem_flatMap.mpr ⟨⟨request, member⟩, List.mem_attach _ _, present⟩))))
          (fun entry present => bindings entry (by
            simp only [Tree.bindings, List.mem_append]
            exact .inl (List.mem_flatMap.mpr ⟨⟨request, member⟩, List.mem_attach _ _, present⟩))) body
      rcases allComplete.2 with tailComplete | stopped
      · exact ScopedSourceMatchAdmission.matching_scan receipt.certificate ownership found form scrutineeFound
          (children ⟨_, _, _, receipt.child, receipt.generated⟩ (by simp [Tree.children])) childScans
          (tailIH tailComplete
            (fun entry present => children entry (by simp [Tree.children, present]))
            (fun entry present => bindings entry (by simp [Tree.bindings, present])) tail)
      · simp only [AcceptedCompilerBodyCompletion.matchStops, Bool.and_eq_true] at stopped
        obtain ⟨defaultBody, present, defaultStops⟩ := (Option.any_eq_true _ _).mp stopped.2
        have stoppedArms := fun arm member => AcceptedCompilerBodyCompletion.Stops.original
          (List.all_eq_true.mp stopped.1 arm member)
        have stoppedDefault := AcceptedCompilerBodyCompletion.Stops.original defaultStops
        obtain ⟨hiddenOrdinary, armsOrdinary⟩ := ScopedSourceMatchAdmission.ordinary_bindings ownership found form
        apply ScopedSourceBodyAdmission.Scan.terminalMatch found form
          (ScopedSourceBodyAdmission.stopped_statement_result unique found
            (.matching found form present stoppedArms stoppedDefault) head)
          scrutineeFound (children ⟨_, _, _, receipt.child, receipt.generated⟩ (by simp [Tree.children]))
          hiddenOrdinary armsOrdinary
        · intro arm member
          obtain ⟨request, member, same⟩ := ScopedSourceMatchAdmission.arm_request receipt.certificate member
          exact same ▸ childScans request member
        · intro statements present
          obtain ⟨request, member, same⟩ := ScopedSourceMatchAdmission.default_request receipt.certificate present
          exact same ▸ childScans request member
        · exact present
        · exact stoppedArms
        · exact stoppedDefault
        · exact remaining.formed_shape readPolicy allComplete.1.2

  | forLoop read form statementType child generated conditionType initial inner after remaining innerIH tailIH =>
      have found := read_found (readPolicy ▸ read)
      have allClosed := closed
      simp only [Tree.complete, Bool.and_eq_true_iff] at allClosed
      obtain ⟨_, _, _, head, tail⟩ := head_tail typed
      have nodeUnit := for_annotation unique found form head
      have original := form_at unique found head
      rw [form] at original
      cases original with
      | forLoop initTyped condition body postTyped =>
        obtain ⟨node, contains, same⟩ := condition.stored_type
        exact .forLoop found form nodeUnit
          (initial.scan allClosed.1.1.1 unique
            (fun child member => children child (by simp [Tree.children, member]))
            (fun binding member => bindings binding (by simp [Tree.bindings, member])) initTyped)
          (lookupExpression?_complete unique contains) same
          (children ⟨_, _, _, child, generated⟩ (by simp [Tree.children]))
          (innerIH (control := control.enterLoop) allClosed.1.1.2
            (fun child member => children child (by simp [Tree.children, member]))
            (fun binding member => bindings binding (by simp [Tree.bindings, member])) body)
          (after.scan allClosed.1.2 unique
            (fun child member => children child (by simp [Tree.children, member]))
            (fun binding member => bindings binding (by simp [Tree.bindings, member])) postTyped)
          (tailIH allClosed.2
            (fun child member => children child (by simp [Tree.children, member]))
            (fun binding member => bindings binding (by simp [Tree.bindings, member])) tail)

theorem Tree.scan {policy : SourceCoreLoops.Policy} {checked : SourceCoreCompatibleCatalog.Checked}
    {source : TypedSource} {result : Ty} {reasonAt : ExpressionId → Word} {mode : Bool} {escaped : Word}
    {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {statements : List StatementId} {code : Expr}
    (tree : Tree policy source result reasonAt mode escaped fuel scope statements code)
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement checked)
    (closed : tree.closed = true) (unique : NodeOccurrencesUnique source)
    (ownership : LocalIdentityOwnership source)
    {approved : ExpressionId → Prop}
    (children : ∀ child ∈ tree.children, approved child.expression)
    (bindings : ∀ binding ∈ tree.bindings, RecursiveNamedStatementSyntaxFacts.BinderReceipt source binding.binder)
    {control : ControlContext} {context final : SourceSemantics.Context} {facts : BodyFacts}
    (typed : StatementsHaveType source control context statements final facts) :
    ScopedSourceBodyAdmission.Scan source approved control.returnType mode statements := by
  exact tree.scan_complete readPolicy (tree.closed_complete closed control.returnType)
    unique ownership children bindings typed

/-- A returned compiler branch has exactly its original expression child and
no executed suffix, even if the source root list retains dead statements. -/
theorem Tree.at_return {policy : SourceCoreLoops.Policy} {checked : SourceCoreCompatibleCatalog.Checked}
    {source : TypedSource} {result : Ty} {reasonAt : ExpressionId → Word} {mode : Bool} {escaped : Word}
    {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {id : StatementId} {rest : List StatementId}
    {code : Expr} {node : StatementNode} {expression : ExpressionId}
    (tree : Tree policy source result reasonAt mode escaped fuel scope (id :: rest) code)
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement checked)
    (found : source.lookupStatement? id = some node) (form : node.form = .returnStmt (some expression)) :
    tree.closed = true ∧ tree.bindings = [] ∧
      ∀ child ∈ tree.children, child.expression = expression := by
  cases tree with
  | returning read original statementType child generated childType =>
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      cases same
      simp_all [Tree.closed, Tree.bindings, Tree.children]
  | returnUnit read original statementType unitType =>
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      cases same
      simp_all
  | initialized read original statementType projected child generated childType tail allocated =>
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      cases same
      simp_all
  | absent read original statementType projected tail allocated =>
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      cases same
      simp_all
  | assigning read original _ _ _ | assigned read original _ _ _ _ | projectedAssigned read original _ _ _ _ | bitNotting read original _ _ _ | bitNotted read original _ _ _ _ | projectedBitNotted read original _ _ _ _ | whileLoop read original _ _ _ _ _ _
      | discard read original _ _ _ _ | valueDiscard read original _ _ _ _ _ | tailValue read original _ _ _ _ | block read original _ _ | conditional read original _ _ _ _ _ _ =>
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      cases same
      simp_all
  | forLoop read original _ _ _ _ _ _ _ _ | forBoundary read original _ _
      | matching read original _ _ _ | matched read original _ _ _ =>
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      cases same
      simp_all
  | breaking read original _ | continuing read original _ =>
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      cases same
      simp_all
  | boundary read outside accepted =>
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      cases same
      simp only [form, expanded] at outside
      cases outside


theorem Tree.at_return_list {policy : SourceCoreLoops.Policy} {checked : SourceCoreCompatibleCatalog.Checked}
    {source : TypedSource} {result : Ty} {reasonAt : ExpressionId → Word} {mode : Bool} {escaped : Word}
    {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {statements : List StatementId}
    {id : StatementId} {rest : List StatementId} {code : Expr} {node : StatementNode} {expression : ExpressionId}
    (tree : Tree policy source result reasonAt mode escaped fuel scope statements code)
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement checked)
    (same : statements = id :: rest)
    (found : source.lookupStatement? id = some node) (form : node.form = .returnStmt (some expression)) :
    tree.closed = true ∧ tree.bindings = [] ∧
      ∀ child ∈ tree.children, child.expression = expression := by
  subst statements
  exact tree.at_return readPolicy found form

end Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodyFlow
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodyBindings
/-! Original source ownership and statement typing authenticate binders in the
accepted compiler flow. Generalized locals remain an explicit retained boundary. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodyBindings
open Core Frontend SourceInference
open AcceptedNamedBodyFlow

private theorem instruction_ids (instructions : List MatchPatternInstruction) :
    (SourceCoreDataPlaces.instructionBinders instructions).map (·.id) =
      patternInstructionBinderIds instructions := by
  induction instructions with
  | nil => rfl
  | cons item rest ih => cases item <;> simp [SourceCoreDataPlaces.instructionBinders,
      patternInstructionBinderIds] at ih ⊢ <;> exact ih

private theorem pattern_ids (pattern : TypedMatchPattern) :
    (SourceCoreDataPlaces.patternBinders pattern).map (·.id) = patternBinderIds pattern := by
  cases pattern with
  | mk source type resolution requirements =>
    cases resolution <;> simp [SourceCoreDataPlaces.patternBinders, patternBinderIds, instruction_ids]

private theorem for_ids (items : List ForItemForm) :
    (items.filterMap fun | .letDecl binder _ => some binder | _ => none).map (·.id) =
      items.flatMap forItemDefinedLocalIds := by
  induction items with
  | nil => rfl
  | cons item rest ih => cases item <;> simp [forItemDefinedLocalIds, ih]

private def nodeBinders (node : Node) : List TypedBinder :=
  match node with
  | .expression node => match node.form with
      | .lambda parameters _ _ => parameters
      | _ => []
  | .statement node => match node.form with
      | .letDecl binder _ => [binder]
      | .forLoop initial _ post _ => (initial ++ post).filterMap fun
          | .letDecl binder _ => some binder | _ => none
      | .matchWith resolution => resolution.cases.flatMap (fun arm => SourceCoreDataPlaces.patternBinders arm.pattern)
      | _ => []

private theorem node_ids (node : Node) :
    ((nodeBinders node).map (·.id)).Sublist node.definedLocalIds := by
  cases node with
  | expression node => cases form : node.form <;>
      simp [nodeBinders, form, Node.definedLocalIds, ExpressionForm.definedLocalIds]
  | statement node =>
      cases form : node.form <;>
        simp [nodeBinders, form, Node.definedLocalIds, StatementForm.definedLocalIds,
          for_ids]
      case matchWith resolution =>
        have same : (resolution.cases.flatMap (fun arm => SourceCoreDataPlaces.patternBinders arm.pattern)).map (·.id) =
            resolution.cases.flatMap (fun arm => arm.pattern.binderIds) := by
          simp [List.map_flatMap, pattern_ids]
        rw [same]
        exact List.sublist_cons_self _ _

private theorem nodes_ids (nodes : List Node) :
    ((nodes.flatMap nodeBinders).map (·.id)).Sublist (nodes.flatMap Node.definedLocalIds) := by
  induction nodes with
  | nil => exact .refl _
  | cons node rest ih =>
    simpa only [List.flatMap_cons, List.map_append] using (node_ids node).append ih

private theorem declared_ids (source : TypedSource) :
    ((SourceCoreDataPlaces.declaredBinders source).map (·.id)).Sublist (definedLocalIds source) := by
  have same : SourceCoreDataPlaces.declaredBinders source = source.inputs ++ source.nodes.flatMap nodeBinders := rfl
  rw [same, List.map_append, ← typedSourceDefinedLocalIds_eq_carrier]
  exact (List.Sublist.refl _).append (nodes_ids source.nodes)

private theorem filter_self {binders : List TypedBinder} {binder : TypedBinder}
    (unique : (binders.map (·.id)).Nodup) (member : binder ∈ binders) :
    binders.filter (fun other => decide (other.id = binder.id)) = [binder] := by
  induction binders with
  | nil => cases member
  | cons first rest ih =>
    obtain ⟨absent, restUnique⟩ := List.nodup_cons.mp unique
    rcases List.mem_cons.mp member with rfl | member
    · have none : rest.filter (fun other => decide (other.id = binder.id)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro other found
        simp only [decide_eq_true_eq]
        intro equal
        exact absent (List.mem_map.mpr ⟨other, found, equal⟩)
      simp [none]
    · have different : first.id ≠ binder.id := by
        intro same
        exact absent (List.mem_map.mpr ⟨binder, member, same.symm⟩)
      simp [different, ih restUnique member]

private theorem node_receipt {source : TypedSource} {node : StatementNode}
    {binder : TypedBinder}
    (ownership : LocalIdentityOwnership source)
    (member : Node.statement node ∈ source.nodes)
    (defined : binder ∈ nodeBinders (.statement node))
    (mono : binder.scheme.quantified = []) (requirements : binder.schemeRequirements = []) :
    RecursiveNamedStatementSyntaxFacts.BinderReceipt source binder := by
  have declared : binder ∈ SourceCoreDataPlaces.declaredBinders source := by
    apply List.mem_append_right
    exact List.mem_flatMap.mpr ⟨.statement node, member, defined⟩
  have idMem : binder.id ∈ definedLocalIds source :=
    (declared_ids source).subset (List.mem_map.mpr ⟨binder, declared, rfl⟩)
  have owned := ownership.owned binder.id idMem
  have filtered := filter_self ((declared_ids source).nodup ownership.unique) declared
  have inNodes : binder.id ∈ source.nodes.flatMap Node.definedLocalIds := by
    exact List.mem_flatMap.mpr ⟨.statement node, member, (node_ids (.statement node)).subset (List.mem_map.mpr ⟨binder, defined, rfl⟩)⟩
  have disjoint := (List.nodup_append.mp (show
    (source.inputs.map (·.id) ++ source.nodes.flatMap Node.definedLocalIds).Nodup from
    by simpa only [definedLocalIds, ← flatMapNodeDefinedLocalIds_eq_carrier] using ownership.unique)).2.2
  refine ⟨?_, mono, ?_⟩
  · simp [SourceCoreDataPlaces.rootBinder, owned, filtered, mono, requirements, pure, Except.pure]
  · apply Bool.eq_false_iff.mpr
    intro found
    obtain ⟨input, present, same⟩ := List.any_eq_true.mp found
    exact disjoint input.id (List.mem_map.mpr ⟨input, present, rfl⟩)
      binder.id inNodes (of_decide_eq_true same)

private theorem let_receipt {source : TypedSource} {node : StatementNode}
    {binder : TypedBinder} {initializer : Option ExpressionId}
    (ownership : LocalIdentityOwnership source) (member : Node.statement node ∈ source.nodes)
    (form : node.form = .letDecl binder initializer)
    (mono : binder.scheme.quantified = []) (requirements : binder.schemeRequirements = []) :
    RecursiveNamedStatementSyntaxFacts.BinderReceipt source binder :=
  node_receipt ownership member (by simp [nodeBinders, form]) mono requirements

private theorem items_receipts {policy : SourceCoreLoops.Policy} {source : TypedSource}
    {site : SourceCoreElaboration.ErrorSite} {result : Ty} {reasonAt : ExpressionId → Word}
    {next : SourceCoreLocalCell.Scope → Except SourceCoreBasic.Error Expr} {finalScope : SourceCoreLocalCell.Scope}
    {finish : Expr} {fuel scope items code} {node : StatementNode}
    (tree : Items policy source site result reasonAt next finalScope finish fuel scope items code)
    (ownership : LocalIdentityOwnership source) (member : Node.statement node ∈ source.nodes)
    (defined : ∀ binder initializer, ForItemForm.letDecl binder initializer ∈ items → binder ∈ nodeBinders (.statement node))
    {control : ControlContext} {context final : SourceSemantics.Context}
    (typed : ForItemsHaveType source control context items final)
    (monomorphic : ∀ binding ∈ tree.bindings, binding.binder.scheme.quantified = []) :
    ∀ binding ∈ tree.bindings, RecursiveNamedStatementSyntaxFacts.BinderReceipt source binding.binder := by
  induction tree generalizing context final with
  | nil => simp [Items.bindings]
  | absent projected remaining allocated ih =>
    cases typed with
    | cons head tail =>
      cases head with
      | letUninitialized mono _ extension =>
        have receipt := node_receipt ownership member (defined _ _ List.mem_cons_self) mono
          (by cases extension with | intro wellFormed _ => exact wellFormed.monomorphic_requirements_empty mono)
        intro binding present
        rcases List.mem_cons.mp present with rfl | present
        · exact receipt
        · exact ih (fun b e p => defined b e (List.mem_cons_of_mem _ p)) tail
            (fun b p => monomorphic b (List.mem_cons_of_mem _ p)) binding present
  | initialized projected child generated childType remaining allocated ih =>
    have mono := monomorphic ⟨_, _, _, projected⟩ (by simp [Items.bindings])
    cases typed with
    | cons head tail =>
      cases head with
      | letInitialized value _ _ extension =>
        have receipt := node_receipt ownership member (defined _ _ List.mem_cons_self) mono
          (by cases extension with | intro wellFormed _ => exact wellFormed.monomorphic_requirements_empty mono)
        intro binding present
        rcases List.mem_cons.mp present with rfl | present
        · exact receipt
        · exact ih (fun b e p => defined b e (List.mem_cons_of_mem _ p)) tail
            (fun b p => monomorphic b (List.mem_cons_of_mem _ p)) binding present
      | letInitializedGeneralized poly _ _ _ _ => exact False.elim (poly mono)
  | discard _ _ remaining ih | assigning remaining _ ih | assigned remaining _ _ ih | projectedAssigned remaining _ _ ih | bitNotting remaining _ ih | bitNotted remaining _ _ ih | projectedBitNotted remaining _ _ ih =>
    cases typed with
    | cons head tail =>
      exact ih (fun b e p => defined b e (List.mem_cons_of_mem _ p)) tail monomorphic

private theorem head_tail {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {rest : List StatementId} {facts : BodyFacts}
    (typed : StatementsHaveType source control context (id :: rest) final facts) :
    ∃ middle headFacts tailFacts, StatementHasType source control context id middle headFacts ∧
      StatementsHaveType source control middle rest final tailFacts := by
  cases typed with
  | singleton head => exact ⟨_, _, _, head, .nil _ _⟩
  | cons head tail => exact ⟨_, _, _, head, tail⟩

private theorem form_at {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {facts : StatementFacts} {node : StatementNode}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (typed : StatementHasType source control context id final facts) :
    Dynamic.StatementHasType.FormTyping source control context node.form final := by
  obtain ⟨actual, contains, original⟩ := Dynamic.StatementHasType.formTyping typed
  cases Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  exact original

/-- Every actual monomorphic let in the accepted flow has one original declaration.
The source typing derivation supplies its binder requirements; whole-source
ownership prevents any collision with inputs or another retained declaration. -/
theorem of_monomorphic {policy : SourceCoreLoops.Policy} {checked : SourceCoreCompatibleCatalog.Checked}
    {source : TypedSource} {result : Ty} {reasonAt : ExpressionId → Word} {mode : Bool} {escaped : Word}
    {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {statements : List StatementId} {code : Expr}
    (tree : Tree policy source result reasonAt mode escaped fuel scope statements code)
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement checked)
    (unique : NodeOccurrencesUnique source) (ownership : LocalIdentityOwnership source)
    {control : ControlContext} {context final : SourceSemantics.Context} {facts : BodyFacts}
    (typed : StatementsHaveType source control context statements final facts)
    (monomorphic : ∀ binding ∈ tree.bindings, binding.binder.scheme.quantified = []) :
    ∀ binding ∈ tree.bindings, RecursiveNamedStatementSyntaxFacts.BinderReceipt source binding.binder := by
  induction tree generalizing control context final facts with
  | nil | returning | returnUnit | boundary | forBoundary | breaking | continuing | tailValue =>
      intro binding member
      simp only [Tree.bindings, List.not_mem_nil] at member
  | initialized read form statementType projected child generated childType remaining allocated ih =>
      have found := read_found (readPolicy ▸ read)
      obtain ⟨_, _, _, head, tail⟩ := head_tail typed
      have original := form_at unique found head
      rw [form] at original
      have mono := monomorphic ⟨_, _, _, projected⟩ (by simp [Tree.bindings])
      have requirements : _ := original
      cases requirements with
      | letInitialized _ _ extension =>
        have receipt := let_receipt ownership (lookupStatement?_sound found).1 form mono
          (by cases extension with | intro wellFormed _ => exact wellFormed.monomorphic_requirements_empty mono)
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · exact receipt
        · exact ih tail (fun next present => monomorphic next (List.mem_cons_of_mem _ present)) binding member
      | letInitializedGeneralized poly _ _ _ _ => exact False.elim (poly mono)
  | absent read form statementType projected remaining allocated ih =>
      have found := read_found (readPolicy ▸ read)
      obtain ⟨_, _, _, head, tail⟩ := head_tail typed
      have original := form_at unique found head
      rw [form] at original
      cases original with
      | letUninitialized mono extension =>
        have receipt := let_receipt ownership (lookupStatement?_sound found).1 form mono
          (by cases extension with | intro wellFormed _ => exact wellFormed.monomorphic_requirements_empty mono)
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · exact receipt
        · exact ih tail (fun next present => monomorphic next (List.mem_cons_of_mem _ present)) binding member

  | assigning _ _ _ _ _ ih | assigned _ _ _ _ _ _ ih | projectedAssigned _ _ _ _ _ _ ih | bitNotting _ _ _ _ _ ih | bitNotted _ _ _ _ _ _ ih | projectedBitNotted _ _ _ _ _ _ ih | discard _ _ _ _ _ _ ih
      | matching _ _ _ _ _ ih | valueDiscard _ _ _ _ _ _ _ ih =>
      obtain ⟨_, _, _, _, tail⟩ := head_tail typed
      exact ih tail monomorphic
  | block read form inner remaining innerIH tailIH =>
      have found := read_found (readPolicy ▸ read)
      obtain ⟨_, _, _, head, tail⟩ := head_tail typed
      have original := form_at unique found head
      rw [form] at original
      cases original with
      | block body =>
        intro binding member
        rcases List.mem_append.mp member with member | member
        · exact innerIH body
            (fun next present => monomorphic next (List.mem_append_left _ present)) binding member
        · exact tailIH tail
            (fun next present => monomorphic next (List.mem_append_right _ present)) binding member
  | conditional read form _ _ _ left right remaining leftIH rightIH tailIH =>
      have found := read_found (readPolicy ▸ read)
      obtain ⟨_, _, _, head, tail⟩ := head_tail typed
      have original := form_at unique found head
      rw [form] at original
      cases original with
      | ifWithoutElse condition body =>
        have first := leftIH body
          (fun binding member => monomorphic binding (by simp [Tree.bindings, member]))
        have second := rightIH (.nil control context)
          (fun binding member => monomorphic binding (by simp [Tree.bindings, member]))
        have next := tailIH tail
          (fun binding member => monomorphic binding (by simp [Tree.bindings, member]))
        intro binding member
        simp only [Tree.bindings, List.mem_append] at member
        rcases member with (member | member) | member
        · exact first binding member
        · exact second binding member
        · exact next binding member
      | ifWithElse condition firstBody secondBody =>
        have first := leftIH firstBody
          (fun binding member => monomorphic binding (by simp [Tree.bindings, member]))
        have second := rightIH secondBody
          (fun binding member => monomorphic binding (by simp [Tree.bindings, member]))
        have next := tailIH tail
          (fun binding member => monomorphic binding (by simp [Tree.bindings, member]))
        intro binding member
        simp only [Tree.bindings, List.mem_append] at member
        rcases member with (member | member) | member
        · exact first binding member
        · exact second binding member
        · exact next binding member
  | whileLoop read form _ _ _ _ inner remaining innerIH tailIH =>
      have found := read_found (readPolicy ▸ read)
      obtain ⟨_, _, _, head, tail⟩ := head_tail typed
      have original := form_at unique found head
      rw [form] at original
      cases original with
      | whileLoop _ body =>
        intro binding member
        rcases List.mem_append.mp member with member | member
        · exact innerIH (control := control.enterLoop) body
            (fun next present => monomorphic next (List.mem_append_left _ present)) binding member
        · exact tailIH tail
            (fun next present => monomorphic next (List.mem_append_right _ present)) binding member

  | matched read form receipt branches remaining branchIH tailIH =>
      have found := read_found (readPolicy ▸ read)
      obtain ⟨scrutinee, scrutineeFound⟩ := ScopedSourceMatchAdmission.scrutinee_found receipt.certificate
      obtain ⟨_, _, _, head, tail⟩ := head_tail typed
      obtain ⟨same, caseFacts, _, caseTyped, defaultTyped⟩ :=
        ScopedSourceMatchAdmission.statement_sites unique found form scrutineeFound head
      subst_vars
      intro binding member
      rcases List.mem_append.mp member with member | member
      · obtain ⟨request, _, present⟩ := List.mem_flatMap.mp member
        obtain ⟨child, last, bodyFacts, _, body⟩ := ScopedSourceMatchAdmission.original_context
          caseTyped defaultTyped (receipt.original request.val request.property)
        exact branchIH request.val request.property body
          (fun entry member => monomorphic entry (List.mem_append_left _
            (List.mem_flatMap.mpr ⟨request, List.mem_attach _ _, member⟩))) binding present
      · exact tailIH tail
          (fun entry present => monomorphic entry (List.mem_append_right _ present)) binding member

  | forLoop read form _ _ _ _ initial inner after remaining innerIH tailIH =>
      have found := read_found (readPolicy ▸ read)
      obtain ⟨_, _, _, head, tail⟩ := head_tail typed
      have original := form_at unique found head
      rw [form] at original
      cases original with
      | forLoop initTyped condition body postTyped =>
        have initialBindings := items_receipts initial ownership (lookupStatement?_sound found).1
          (fun binder expression present => by
            simp only [nodeBinders, form, List.filterMap_append, List.mem_append]
            exact .inl (List.mem_filterMap.mpr ⟨_, present, rfl⟩)) initTyped
          (fun binding member => monomorphic binding (by simp [Tree.bindings, member]))
        have inside := innerIH body
          (fun binding member => monomorphic binding (by simp [Tree.bindings, member]))
        have postBindings := items_receipts after ownership (lookupStatement?_sound found).1
          (fun binder expression present => by
            simp only [nodeBinders, form, List.filterMap_append, List.mem_append]
            exact .inr (List.mem_filterMap.mpr ⟨_, present, rfl⟩)) postTyped
          (fun binding member => monomorphic binding (by simp [Tree.bindings, member]))
        have next := tailIH tail
          (fun binding member => monomorphic binding (by simp [Tree.bindings, member]))
        intro binding member
        simp only [Tree.bindings, List.mem_append] at member
        rcases member with ((member | member) | member) | member
        · exact initialBindings binding member
        · exact inside binding member
        · exact postBindings binding member
        · exact next binding member

/-- The only unresolved binding condition is exposed on an actual accepted
binding, retaining its original scope, payload and contextual projection. -/
theorem of_tree {policy : SourceCoreLoops.Policy} {checked : SourceCoreCompatibleCatalog.Checked}
    {source : TypedSource} {result : Ty} {reasonAt : ExpressionId → Word} {mode : Bool} {escaped : Word}
    {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {statements : List StatementId} {code : Expr}
    (tree : Tree policy source result reasonAt mode escaped fuel scope statements code)
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement checked)
    (unique : NodeOccurrencesUnique source) (ownership : LocalIdentityOwnership source)
    {control : ControlContext} {context final : SourceSemantics.Context} {facts : BodyFacts}
    (typed : StatementsHaveType source control context statements final facts) :
    (∀ binding ∈ tree.bindings, RecursiveNamedStatementSyntaxFacts.BinderReceipt source binding.binder) ∨
      ∃ binding ∈ tree.bindings, binding.binder.scheme.quantified ≠ [] := by
  classical
  by_cases mono : ∀ binding ∈ tree.bindings, binding.binder.scheme.quantified = []
  · exact .inl (of_monomorphic tree readPolicy unique ownership typed mono)
  · apply Or.inr
    apply Classical.byContradiction
    intro none
    apply mono
    intro binding member
    apply Classical.byContradiction
    intro quantified
    exact none ⟨binding, member, quantified⟩

/-- Header attribution supplies the genuine instantiated source ownership and
statement typing. No declaration, statement-shape or body-execution callback
is an input to the binding extraction. -/
theorem of_header {compiled : SourceCoreUnifiedCompilation.Compiled}
    {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    {instantiation : DeclarationInstantiation}
    {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    {flow : Expr}
    (tree : Tree header.policy header.function.source header.output header.reasonAt true header.escaped
      header.fuel (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body flow) :
    (∀ binding ∈ tree.bindings, RecursiveNamedStatementSyntaxFacts.BinderReceipt header.function.source binding.binder) ∨
      ∃ binding ∈ tree.bindings, binding.binder.scheme.quantified ≠ [] := by
  obtain ⟨facts, certified⟩ := RecursiveNamedHeaderSourceTyping.certificate header wellFormed
  have ownership : LocalIdentityOwnership header.function.source := by
    rw [header.frame.source]
    exact certified.local_identity_ownership
  obtain ⟨final, facts, typed, _⟩ := RecursiveNamedHeaderSourceTyping.statements header wellFormed
  exact of_tree tree (RecursiveNamedPreparedHeaderPolicies.Prepared.header_read prepared aligned)
    header.unique ownership typed

end Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodyBindings
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodySupport
/-! The actual named body action selects its structural branch. The supported
branch feeds the current physical scoped Support collector; the other branch
retains a concrete compiler frontier. There is no body-recognizer premise. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodySupport
open Core Frontend SourceInference
open AcceptedNamedBodyFlow
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)
open CallableIndexedOwnedPreparedNamedSyntaxAdmission (DirectSite TableAligned)
open CallableIndexedOwnedFunctionValues (Header)

theorem of_actual {compiled : SourceCoreUnifiedCompilation.Compiled}
    {recipe : SourceCoreIndexedSession.Recipe}
    {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    {instantiation : DeclarationInstantiation}
    {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
    {inputs : List (Input compiled)} (rows : Inventory inputs)
    {directRows : List SourceSpecialization.SpecializedFunction}
    (table : TableAligned inputs directRows)
    (metadata : CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
      compiled.indexed prepared.named header.function.source (DirectSite directRows))
    (children : ∀ receipt : Body header.policy header.fuel header.function.source
      (CallableIndexedOwnedPreparedStagedNamedBranchingReceipts.parameterScope header)
      header.function.body header.output header.reasonAt header.fellThrough header.escaped header.body,
      ∀ child ∈ receipt.tree.children,
        GeneralSyntax header.function.source child.expression (DirectSite directRows))
    (bindings : ∀ receipt : Body header.policy header.fuel header.function.source
      (CallableIndexedOwnedPreparedStagedNamedBranchingReceipts.parameterScope header)
      header.function.body header.output header.reasonAt header.fellThrough header.escaped header.body,
      ∀ binding ∈ receipt.tree.bindings,
        RecursiveNamedStatementSyntaxFacts.BinderReceipt header.function.source binding.binder)
    (ready : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
        (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
    (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
    (methods : CallableIndexedOwnedPreparedStagedMethodSelectionIssuer.Catalog compiled)
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : entry ∈ compiled.indexed.entries)
    (actual : RecursiveNamedPreparedStageContracts.Prepared compiled compiled.indexed.ancestry.graph.inputs.callable)
    {bodyRegistry : SourceCoreRawMetadata.Registry} :
    Nonempty (Σ body : CallableIndexedOwnedPreparedStagedNamedBodies.Body header,
      CallableIndexedOwnedPreparedStagedPhysicalNamedBodySupport.Support
        (headers := headers rows) (bodyRegistry := bodyRegistry)
        (stages := RecursiveNamedPreparedStageScopes.registry actual)
        (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
        header body) ∨ Nonempty (Incomplete header.policy header.fuel header.function.source
      (CallableIndexedOwnedPreparedStagedNamedBranchingReceipts.parameterScope header)
      header.function.body header.output header.reasonAt header.fellThrough header.escaped header.body) := by
  obtain ⟨receipt⟩ := body_of_accepted aligned.accepted
  cases closed : receipt.tree.closed with
  | false => exact .inr ⟨⟨receipt, closed⟩⟩
  | true =>
      obtain ⟨final, facts, typed, _complete⟩ := RecursiveNamedHeaderSourceTyping.statements header wellFormed
      have scan := receipt.tree.scan
        (RecursiveNamedPreparedHeaderPolicies.Prepared.header_read prepared aligned)
        closed header.unique (by
          obtain ⟨_, certificate⟩ := RecursiveNamedHeaderSourceTyping.certificate header wellFormed
          rw [header.frame.source]
          exact certificate.local_identity_ownership) (children receipt) (bindings receipt) typed
      exact .inl (CallableIndexedOwnedPreparedNamedScopedAdmission.of_actual
        prepared aligned rows table ⟨metadata, scan⟩ ready diagnostic receiver wellFormed
        checked catalog methods member actual)


/-- Return selection uses the stored original head and the actual compiler receipt. -/
theorem of_returning {compiled : SourceCoreUnifiedCompilation.Compiled}
    {recipe : SourceCoreIndexedSession.Recipe}
    {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    {instantiation : DeclarationInstantiation}
    {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
    {inputs : List (Input compiled)} (rows : Inventory inputs)
    {directRows : List SourceSpecialization.SpecializedFunction}
    (table : TableAligned inputs directRows)
    (metadata : CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
      compiled.indexed prepared.named header.function.source (DirectSite directRows))
    {id : StatementId} {rest : List StatementId} {node : StatementNode} {expression : ExpressionId}
    (statements : header.function.body = id :: rest)
    (found : header.function.source.lookupStatement? id = some node)
    (form : node.form = .returnStmt (some expression))
    (child : GeneralSyntax header.function.source expression (DirectSite directRows))
    (ready : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
        (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
    (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
    (methods : CallableIndexedOwnedPreparedStagedMethodSelectionIssuer.Catalog compiled)
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : entry ∈ compiled.indexed.entries)
    (actual : RecursiveNamedPreparedStageContracts.Prepared compiled compiled.indexed.ancestry.graph.inputs.callable)
    {bodyRegistry : SourceCoreRawMetadata.Registry} :
    Nonempty (Σ body : CallableIndexedOwnedPreparedStagedNamedBodies.Body header,
      CallableIndexedOwnedPreparedStagedPhysicalNamedBodySupport.Support
        (headers := headers rows) (bodyRegistry := bodyRegistry)
        (stages := RecursiveNamedPreparedStageScopes.registry actual)
        (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
        header body) := by
  obtain ⟨receipt⟩ := body_of_accepted aligned.accepted
  have details := receipt.tree.at_return_list
    (RecursiveNamedPreparedHeaderPolicies.Prepared.header_read prepared aligned) statements found form
  obtain ⟨final, facts, typed, _complete⟩ := RecursiveNamedHeaderSourceTyping.statements header wellFormed
  have scan := receipt.tree.scan
    (RecursiveNamedPreparedHeaderPolicies.Prepared.header_read prepared aligned)
    details.1 header.unique (by
      obtain ⟨_, certificate⟩ := RecursiveNamedHeaderSourceTyping.certificate header wellFormed
      rw [header.frame.source]
      exact certificate.local_identity_ownership)
    (fun actual member => (details.2.2 actual member).symm ▸ child)
    (fun binding member => False.elim (by simp only [details.2.1, List.not_mem_nil] at member)) typed
  exact CallableIndexedOwnedPreparedNamedScopedAdmission.of_actual
    prepared aligned rows table ⟨metadata, scan⟩ ready diagnostic receiver wellFormed
    checked catalog methods member actual

end Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodySupport
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodyAdmission
/-! The accepted body action supplies statement structure. Original Source typing
supplies binding ownership; only expression certificates remain explicit.
Unsupported structure and generalized locals retain their actual compiled body. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodyAdmission
open Core Frontend SourceInference
open AcceptedNamedBodyFlow
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedNamedScopedAdmission (SourceAdmission Admission)
open CallableIndexedOwnedPreparedNamedSyntaxAdmission (DirectSite TableAligned)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)
open CallableIndexedOwnedPreparedNamedSourceAdmissionTransport (statements)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {row : SourceSpecialization.SpecializedFunction}
  (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
  {instantiation : DeclarationInstantiation}
  {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
  (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)

abbrev BodyAt (header : Header compiled (Program.ofChecked compiled.sourceProgram)) :=
  Body header.policy header.fuel header.function.source
    (CallableIndexedOwnedPreparedStagedNamedBranchingReceipts.parameterScope header)
    header.function.body header.output header.reasonAt header.fellThrough header.escaped header.body

/-- Each alternative retains the exact accepted body, including its actual
children, binding projections, statement roots and emitted code. -/
inductive Unsupported (header : Header compiled (Program.ofChecked compiled.sourceProgram)) where
  | structure (receipt : BodyAt header) (openBranch : receipt.tree.closed = false)
  | generalized (receipt : BodyAt header) (binding : Binding header.policy header.function.source)
      (member : binding ∈ receipt.tree.bindings) (quantified : binding.binder.scheme.quantified ≠ [])

include aligned

/-- No statement-shape or binder callback is required by this producer. -/
theorem of_actual {directRows : List SourceSpecialization.SpecializedFunction}
    (metadata : CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
      compiled.indexed prepared.named header.function.source (DirectSite directRows))
    (children : ∀ receipt : BodyAt header, ∀ child ∈ receipt.tree.children,
      GeneralSyntax header.function.source child.expression (DirectSite directRows))
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    Admission prepared header directRows ∨ Nonempty (Unsupported header) := by
  obtain ⟨receipt⟩ := body_of_accepted aligned.accepted
  cases closed : receipt.tree.closed with
  | false => exact .inr ⟨.structure receipt closed⟩
  | true =>
    rcases AcceptedNamedBodyBindings.of_header prepared aligned wellFormed receipt.tree with binders | generalized
    · obtain ⟨final, facts, typed, _complete⟩ := RecursiveNamedHeaderSourceTyping.statements header wellFormed
      exact .inl ⟨metadata, receipt.tree.scan
        (RecursiveNamedPreparedHeaderPolicies.Prepared.header_read prepared aligned)
        closed header.unique (by
          obtain ⟨_, certificate⟩ := RecursiveNamedHeaderSourceTyping.certificate header wellFormed
          rw [header.frame.source]
          exact certificate.local_identity_ownership) (children receipt) binders typed⟩
    · obtain ⟨binding, member, quantified⟩ := generalized
      exact .inr ⟨.generalized receipt binding member quantified⟩

/-- A stored return head selects the actual accepted return branch. The rest of
its Source statement list is preserved; the lowerer terminates at that head. -/
theorem of_returning {directRows : List SourceSpecialization.SpecializedFunction}
    (metadata : CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
      compiled.indexed prepared.named header.function.source (DirectSite directRows))
    {id : StatementId} {rest : List StatementId} {node : StatementNode} {expression : ExpressionId}
    (roots : header.function.body = id :: rest)
    (found : header.function.source.lookupStatement? id = some node)
    (form : node.form = .returnStmt (some expression))
    (child : GeneralSyntax header.function.source expression (DirectSite directRows))
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    Admission prepared header directRows := by
  obtain ⟨receipt⟩ := body_of_accepted aligned.accepted
  have details := receipt.tree.at_return_list
    (RecursiveNamedPreparedHeaderPolicies.Prepared.header_read prepared aligned) roots found form
  obtain ⟨final, facts, typed, _complete⟩ := RecursiveNamedHeaderSourceTyping.statements header wellFormed
  exact ⟨metadata, receipt.tree.scan
    (RecursiveNamedPreparedHeaderPolicies.Prepared.header_read prepared aligned)
    details.1 header.unique (by
      obtain ⟨_, certificate⟩ := RecursiveNamedHeaderSourceTyping.certificate header wellFormed
      rw [header.frame.source]
      exact certificate.local_identity_ownership)
    (fun actual member => (details.2.2 actual member).symm ▸ child)
    (fun binding member => False.elim (by simp only [details.2.1, List.not_mem_nil] at member)) typed⟩

/-- Reverse transport uses the same cache identity and accepted root equation
as the existing source-to-Header adapter. -/
theorem source_of_header {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : compiled.indexed.base.functions[index]? = some named)
    (same : named.specialized = row)
    {directRows : List SourceSpecialization.SpecializedFunction}
    (admission : Admission prepared header directRows) :
    SourceAdmission compiled named named.specialized.function.typedBody
      (statements named.specialized.function.typedBody)
      named.specialized.function.inferredBodyType directRows := by
  have namedEq := CallableIndexedOwnedPreparedNamedSourceAdmissionTransport.cached_named prepared selected same
  obtain ⟨source, body, result⟩ := CallableIndexedOwnedPreparedNamedSourceAdmissionTransport.header_data prepared aligned
  change SourceAdmission compiled prepared.named header.function.source header.function.body
    header.function.resultType directRows at admission
  rw [source, body, result, namedEq] at admission
  exact admission

omit aligned

/-- The current physical scoped collector consumes the derived admission. -/
theorem support {compiled : SourceCoreUnifiedCompilation.Compiled}
    {recipe : SourceCoreIndexedSession.Recipe}
    {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    {instantiation : DeclarationInstantiation}
    {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
    {inputs : List (Input compiled)} (rows : Inventory inputs)
    {directRows : List SourceSpecialization.SpecializedFunction}
    (table : TableAligned inputs directRows)
    (metadata : CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
      compiled.indexed prepared.named header.function.source (DirectSite directRows))
    (children : ∀ receipt : Body header.policy header.fuel header.function.source
      (CallableIndexedOwnedPreparedStagedNamedBranchingReceipts.parameterScope header)
      header.function.body header.output header.reasonAt header.fellThrough header.escaped header.body,
      ∀ child ∈ receipt.tree.children,
        GeneralSyntax header.function.source child.expression (DirectSite directRows))
    (ready : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
        (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
    (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
    (methods : CallableIndexedOwnedPreparedStagedMethodSelectionIssuer.Catalog compiled)
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : entry ∈ compiled.indexed.entries)
    (actual : RecursiveNamedPreparedStageContracts.Prepared compiled compiled.indexed.ancestry.graph.inputs.callable)
    {bodyRegistry : SourceCoreRawMetadata.Registry} :
    Nonempty (Σ body : CallableIndexedOwnedPreparedStagedNamedBodies.Body header,
      CallableIndexedOwnedPreparedStagedPhysicalNamedBodySupport.Support
        (headers := headers rows) (bodyRegistry := bodyRegistry)
        (stages := RecursiveNamedPreparedStageScopes.registry actual)
        (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
        header body) ∨ Nonempty (Unsupported header) := by
  rcases of_actual prepared aligned metadata children wellFormed with admission | unsupported
  · exact .inl (CallableIndexedOwnedPreparedNamedScopedAdmission.of_actual
      prepared aligned rows table admission ready diagnostic receiver wellFormed
      checked catalog methods member actual)
  · exact .inr unsupported

end Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodyAdmission
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodyRefinement
/-! The aligned Header identifies the actual assignment callbacks. Refinement
retains the same accepted body, source, scope, fuel and emitted result. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodyRefinement
open Core Frontend SourceInference
open AcceptedNamedBodyFlow
open AcceptedNamedBodyAdmission (BodyAt)

/-- The assignment profile comes from the same genuine named compiler Header. -/
theorem of_header {compiled : SourceCoreUnifiedCompilation.Compiled}
    {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    {instantiation : DeclarationInstantiation}
    {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header) :
    ∃ receipt : BodyAt header, receipt.tree.Ready := by
  obtain ⟨actual⟩ := body_of_accepted aligned.accepted
  have matched : CompatibleAssignmentStatements.AssignmentPolicy header.policy
      (.initial compiled.compatible.checked)
      (RecursiveNamedPreparedHeaderPolicies.Prepared.invalidProjection prepared)
      (RecursiveNamedPreparedHeaderPolicies.Prepared.invalidOperand prepared)
      (RecursiveNamedPreparedHeaderPolicies.Prepared.missingDefault prepared) := by
    rw [aligned.policy]
    exact RecursiveNamedPreparedHeaderPolicies.Prepared.assignments prepared
  have unary : CompatibleBitNotStatements.Policy header.policy
      (.initial compiled.compatible.checked)
      (RecursiveNamedPreparedHeaderPolicies.Prepared.invalidProjection prepared)
      (RecursiveNamedPreparedHeaderPolicies.Prepared.invalidUnary prepared)
      (RecursiveNamedPreparedHeaderPolicies.Prepared.missingDefault prepared) := by
    rw [aligned.policy]
    exact RecursiveNamedPreparedHeaderPolicies.Prepared.unary prepared
  obtain ⟨tree, ready⟩ := actual.tree.refine matched unary
    (RecursiveNamedPreparedHeaderPolicies.Prepared.header_match prepared aligned)
  exact ⟨⟨actual.flow, tree, actual.emitted⟩, ready⟩

end Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodyRefinement
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ActualBodyInvocationInputIdentities
/-! Input identities come from the actual named seed and compiler plan row.
Arbitrary later substitutions preserve them, including a larger read context.
No equality of input types or of complete source tables is needed. The same
holds for the identifiers a closure copies. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ActualBodyInvocation
open Core Frontend SourceInference TypeSystem
open SourceCoreCallableAncestryReadRecipes
open SourceSemantics.CaptureBinders (copiedBinder? copied_isSome_applySubstitution)

private theorem inputs_substitution (source : TypedSource) (substitution : Substitution) :
    (source.applySubstitution substitution).inputs.map TypedBinder.id =
      source.inputs.map TypedBinder.id := by
  simp only [TypedSource.applySubstitution, List.map_map, Function.comp_def, TypedBinder.applySubstitution]

theorem paired_input_origin {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {frame : SourceCoreCallablePairedFrames.Frame} {state : SourceCoreCallableAncestryReadRecipes.State} {source : TypedSource}
    (paired : CallableAppliedDynamicSourceMaterialization.Pair inputs frame state source) :
    ∃ original, SourceCompilationPlan.exactSpecialization base.plan state.metadata.owner = .ok original ∧
      source.inputs.map TypedBinder.id = original.function.typedBody.inputs.map TypedBinder.id := by
  induction paired with
  | @named id state selected =>
    unfold SourceCoreCallableAncestryPairedPreparation.named? at selected
    cases found : SourceCoreCallableAncestryPreparation.named? inputs id with
    | none => simp [found] at selected
    | some metadata =>
      simp only [found, Option.map_some, Option.some.injEq] at selected
      subst state
      obtain ⟨original, selected, source, _⟩ :=
        CallableAncestryPairedProfiles.named_source inputs found
      exact ⟨original, selected, congrArg (fun source : TypedSource =>
        source.inputs.map TypedBinder.id) source⟩
  | lambda _ _ ih => exact ih
  | @applied callerFrame lexicalFrame caller lexical source id target _ recipe ih =>
    obtain ⟨original, selected, same⟩ := ih
    exact ⟨original, selected, (inputs_substitution source recipe.read.substitution).trans same⟩

theorem paired_copied_origin {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {frame : SourceCoreCallablePairedFrames.Frame} {state : SourceCoreCallableAncestryReadRecipes.State} {source : TypedSource}
    (paired : CallableAppliedDynamicSourceMaterialization.Pair inputs frame state source) :
    ∃ original, SourceCompilationPlan.exactSpecialization base.plan state.metadata.owner = .ok original ∧
      ∀ id, (copiedBinder? source id).isSome = (copiedBinder? original.function.typedBody id).isSome := by
  induction paired with
  | @named id state selected =>
    unfold SourceCoreCallableAncestryPairedPreparation.named? at selected
    cases found : SourceCoreCallableAncestryPreparation.named? inputs id with
    | none => simp [found] at selected
    | some metadata =>
      simp only [found, Option.map_some, Option.some.injEq] at selected
      subst state
      obtain ⟨original, selected, source, _⟩ :=
        CallableAncestryPairedProfiles.named_source inputs found
      exact ⟨original, selected, fun id => congrArg (fun source : TypedSource =>
        (copiedBinder? source id).isSome) source⟩
  | lambda _ _ ih => exact ih
  | @applied callerFrame lexicalFrame caller lexical source id target _ recipe ih =>
    obtain ⟨original, selected, same⟩ := ih
    exact ⟨original, selected, fun id =>
      (copied_isSome_applySubstitution recipe.read.substitution source id).trans (same id)⟩

private theorem compiler_input_origin {program : CheckedProgram} {plan : SourceCompilationPlan.Plan}
    {owner : SourceCompilationPlan.Key} {active : Substitution} {source : TypedSource}
    (receipt : LambdaSourceAlignment.SourceReceipt program plan owner active source) :
    ∃ original, SourceCompilationPlan.exactSpecialization plan owner = .ok original ∧
      source.inputs.map TypedBinder.id = original.function.typedBody.inputs.map TypedBinder.id := by
  cases receipt with
  | original selected => exact ⟨_, selected, rfl⟩
  | contextual accepted =>
    obtain ⟨original, selected, _, _, source⟩ := LambdaSourceAlignment.prepared_source accepted
    exact ⟨original, selected, by rw [source]; exact inputs_substitution _ _⟩

private theorem compiler_copied_origin {program : CheckedProgram} {plan : SourceCompilationPlan.Plan}
    {owner : SourceCompilationPlan.Key} {active : Substitution} {source : TypedSource}
    (receipt : LambdaSourceAlignment.SourceReceipt program plan owner active source) :
    ∃ original, SourceCompilationPlan.exactSpecialization plan owner = .ok original ∧
      ∀ id, (copiedBinder? source id).isSome = (copiedBinder? original.function.typedBody id).isSome := by
  cases receipt with
  | original selected => exact ⟨_, selected, fun _ => rfl⟩
  | contextual accepted =>
    obtain ⟨original, selected, _, _, source⟩ := LambdaSourceAlignment.prepared_source accepted
    exact ⟨original, selected, fun id => by rw [source]; exact copied_isSome_applySubstitution _ _ _⟩

/-- Both paths select the same actual plan row. This works for every carried
paired source, independently of the view relation chosen for its code. -/
theorem Index.input_ids {compiled : SourceCoreUnifiedCompilation.Compiled}
    {bodyRelation : BodyRelation} (index : Index compiled bodyRelation) :
    index.source.inputs.map TypedBinder.id = index.compilerSource.inputs.map TypedBinder.id := by
  cases index with
  | named _ _ => rfl
  | contextual material view =>
    obtain ⟨original, selected, source⟩ := paired_input_origin view.materialized_pair
    obtain ⟨compiler, compiled, target⟩ := compiler_input_origin material.compiler_source_receipt
    have owner := view_metadata_owner view
    rw [owner] at selected
    have same := Except.ok.inj (selected.symm.trans compiled)
    subst compiler
    exact source.trans target.symm

/-- Both paths copy the same identifiers, since both are substitution
instances of the same plan row. -/
theorem Index.copied_ids {compiled : SourceCoreUnifiedCompilation.Compiled}
    {bodyRelation : BodyRelation} (index : Index compiled bodyRelation) (id : Resolved.LocalId) :
    (copiedBinder? index.source id).isSome = (copiedBinder? index.compilerSource id).isSome := by
  cases index with
  | named _ _ => rfl
  | contextual material view =>
    obtain ⟨original, selected, source⟩ := paired_copied_origin view.materialized_pair
    obtain ⟨compiler, compiled, target⟩ := compiler_copied_origin material.compiler_source_receipt
    have owner := view_metadata_owner view
    rw [owner] at selected
    have same := Except.ok.inj (selected.symm.trans compiled)
    subst compiler
    exact (source id).trans (target id).symm

theorem Index.compiler_source_receipt {compiled : SourceCoreUnifiedCompilation.Compiled}
    {bodyRelation : BodyRelation} (index : Index compiled bodyRelation) :
    LambdaSourceAlignment.SourceReceipt compiled.indexed.base.sourceProgram compiled.indexed.base.plan
      index.owner index.active index.compilerSource := by
  cases index with
  | named _ selected => exact .original selected
  | contextual material _ => exact material.compiler_source_receipt

theorem materialized_input_ids {compiled : SourceCoreUnifiedCompilation.Compiled}
    {mapping : GeneralHeap.LocationMap} {world : StoreTyping} {function : Dynamic.Closure}
    {viewRelation : TypedSource → TypedSource → Prop}
    (material : GeneralizedLocalAcceptedMaterialization.Materialization compiled mapping world function viewRelation)
    (view : GeneralizedLocalAcceptedMaterialization.View material) :
    function.source.inputs.map TypedBinder.id = material.code.view.inputs.map TypedBinder.id :=
  (Index.contextual (bodyRelation := fun source target _ => viewRelation source target) material view).input_ids

theorem materialized_copied_ids {compiled : SourceCoreUnifiedCompilation.Compiled}
    {mapping : GeneralHeap.LocationMap} {world : StoreTyping} {function : Dynamic.Closure}
    {viewRelation : TypedSource → TypedSource → Prop}
    (material : GeneralizedLocalAcceptedMaterialization.Materialization compiled mapping world function viewRelation)
    (view : GeneralizedLocalAcceptedMaterialization.View material) (id : Resolved.LocalId) :
    (copiedBinder? function.source id).isSome = (copiedBinder? material.code.view id).isSome :=
  (Index.contextual (bodyRelation := fun source target _ => viewRelation source target) material view).copied_ids id

end Solcore.SourceSemantics.CoreLowering.ActualBodyInvocation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ActualBodyInvocationReads
/-! The real named or contextual compiler statement reader retains the Source
statement selected by the same invocation. Terminal heads come from that read. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.ActualBodyInvocation
open Core Frontend SourceInference
open CallableIndexedOwnedAdmittedStagedTerminalStatements (Head)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}

theorem Index.statement_reader {bodyRelation : BodyRelation} (index : Index compiled bodyRelation) : index.policy.readStatement =
    SourceCoreCompatibleDataExpressions.readStatement compiled.compatible.checked := by
  cases index with
  | named => rfl
  | contextual material _ => exact GeneralizedLocalAcceptedBodyCompiler.statement_reader material

private theorem read_found {checked : SourceCoreCompatibleCatalog.Checked} {source : TypedSource}
    {id : StatementId} {node : StatementNode} {type : Ty}
    (accepted : SourceCoreCompatibleDataExpressions.readStatement checked source id = .ok (node, type)) :
    source.lookupStatement? id = some node := by
  unfold SourceCoreCompatibleDataExpressions.readStatement at accepted
  by_cases owner : id.occurrence.owner ≠ source.owner
  · simp [owner, throw, bind, Except.bind] at accepted
  · simp only [owner, ↓reduceIte, bind, Except.bind, pure, Except.pure] at accepted
    cases found : source.lookupStatement? id with
    | none => simp [found] at accepted
    | some actual =>
      simp only [found] at accepted
      obtain ⟨_, _, same⟩ := CompatibleEncoding.bind_ok accepted
      cases same
      rfl

theorem Index.statement_read (index : Index compiled) {id : StatementId}
    {node : StatementNode} {type : Ty}
    (accepted : index.policy.readStatement index.compilerSource id = .ok (node, type)) :
    index.source.lookupStatement? id = some node := by
  rw [index.statement_reader] at accepted
  exact index.source_view.statement (read_found accepted)

theorem Index.return_head (index : Index compiled) {invocation : Staging.Recursive.Scope}
    (source : invocation.source = index.source) {id : StatementId} {node : StatementNode}
    {type : Ty} {expression : ExpressionId} (rest : List StatementId)
    (accepted : index.policy.readStatement index.compilerSource id = .ok (node, type))
    (form : node.form = .returnStmt (some expression)) : Head invocation expression (id :: rest) := by
  exact .returning rest (source ▸ lookupStatement?_sound (index.statement_read accepted)) form

theorem Index.tail_head (index : Index compiled) {invocation : Staging.Recursive.Scope}
    (source : invocation.source = index.source) {id : StatementId} {node : StatementNode}
    {type : Ty} {expression : ExpressionId}
    (accepted : index.policy.readStatement index.compilerSource id = .ok (node, type))
    (form : node.form = .expression expression false) : Head invocation expression [id] := by
  exact .tail (source ▸ lookupStatement?_sound (index.statement_read accepted)) form

end Solcore.SourceSemantics.CoreLowering.ActualBodyInvocation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ActualBodyInvocationReachedReads
/-! Actual body roots supply lookup correspondence only where the compiler
descends. The root receipt and each child edge retain the same invocation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ActualBodyInvocation
open Core Frontend SourceInference CallableLambdaBodyReachability
open CallableIndexedOwnedAdmittedStagedTerminalStatements (Head)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}

def Index.Reached {bodyRelation : BodyRelation} (index : Index compiled bodyRelation)
    (id : NodeId) : Prop :=
  Reaches index.compilerSource (index.statements.map NodeId.statement) id

theorem Index.body_root {bodyRelation : BodyRelation} (index : Index compiled bodyRelation)
    {id : StatementId} (member : id ∈ index.statements) : index.Reached (.statement id) :=
  .root (List.mem_map.mpr ⟨id, member, rfl⟩)

/-- This carries the actual full compiler receipt and the roots it compiled.
No independently chosen statement list enters the reached-body interface. -/
theorem Index.body_root_receipt (index : Index compiled ReachedView) :
    Nonempty (AcceptedNamedBodyFlow.Body index.policy index.fuel index.compilerSource index.scope
      index.statements index.result index.reasonAt index.fellThrough index.escaped index.body) ∧
    (∀ id ∈ index.statements, index.Reached (.statement id)) :=
  ⟨index.body_receipt, fun _ member => index.body_root member⟩

theorem Index.statement_read_reached (index : Index compiled ReachedView) {id : StatementId}
    (reached : index.Reached (.statement id)) {node : StatementNode} {type : Ty}
    (accepted : index.policy.readStatement index.compilerSource id = .ok (node, type)) :
    index.source.lookupStatement? id = some node := by
  rw [index.statement_reader] at accepted
  exact (index.reached_view.statement (.inr reached)).trans (read_found accepted)

theorem Index.expression_read_reached (index : Index compiled ReachedView) {id : ExpressionId}
    (reached : index.Reached (.expression id)) {node : ExpressionNode}
    (found : index.compilerSource.lookupExpression? id = some node) :
    ∃ original, index.source.lookupExpression? id = some original ∧
      original.id = node.id ∧ original.form = node.form :=
  index.reached_view.expression (.inr reached) found

theorem Index.statement_child {bodyRelation : BodyRelation} (index : Index compiled bodyRelation)
    {id : StatementId} (reached : index.Reached (.statement id))
    {node : StatementNode} {type : Ty}
    (accepted : index.policy.readStatement index.compilerSource id = .ok (node, type))
    {child : NodeId} (edge : child ∈ node.form.references) : index.Reached child := by
  rw [index.statement_reader] at accepted
  exact .statement reached (read_found accepted) edge

theorem Index.expression_child {bodyRelation : BodyRelation} (index : Index compiled bodyRelation)
    {id : ExpressionId} (reached : index.Reached (.expression id))
    {node : ExpressionNode} (found : index.compilerSource.lookupExpression? id = some node)
    {child : NodeId} (edge : child ∈ node.form.references) : index.Reached child :=
  .expression reached found edge

theorem Index.return_head_reached (index : Index compiled ReachedView)
    {invocation : Staging.Recursive.Scope} (source : invocation.source = index.source)
    {id : StatementId} (reached : index.Reached (.statement id))
    {node : StatementNode} {type : Ty} {expression : ExpressionId} (rest : List StatementId)
    (accepted : index.policy.readStatement index.compilerSource id = .ok (node, type))
    (form : node.form = .returnStmt (some expression)) : Head invocation expression (id :: rest) :=
  .returning rest (source ▸ lookupStatement?_sound (index.statement_read_reached reached accepted)) form

theorem Index.tail_head_reached (index : Index compiled ReachedView)
    {invocation : Staging.Recursive.Scope} (source : invocation.source = index.source)
    {id : StatementId} (reached : index.Reached (.statement id))
    {node : StatementNode} {type : Ty} {expression : ExpressionId}
    (accepted : index.policy.readStatement index.compilerSource id = .ok (node, type))
    (form : node.form = .expression expression false) : Head invocation expression [id] :=
  .tail (source ▸ lookupStatement?_sound (index.statement_read_reached reached accepted)) form

theorem Index.return_child (index : Index compiled ReachedView)
    {id : StatementId} (reached : index.Reached (.statement id))
    {node : StatementNode} {type : Ty} {expression : ExpressionId}
    (accepted : index.policy.readStatement index.compilerSource id = .ok (node, type))
    (form : node.form = .returnStmt (some expression)) : index.Reached (.expression expression) := by
  apply index.statement_child reached accepted
  simp [form, StatementForm.references]

theorem Index.tail_child (index : Index compiled ReachedView)
    {id : StatementId} (reached : index.Reached (.statement id))
    {node : StatementNode} {type : Ty} {expression : ExpressionId} {discard : Bool}
    (accepted : index.policy.readStatement index.compilerSource id = .ok (node, type))
    (form : node.form = .expression expression discard) : index.Reached (.expression expression) := by
  apply index.statement_child reached accepted
  simp [form, StatementForm.references]

end Solcore.SourceSemantics.CoreLowering.ActualBodyInvocation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ActualBodyInvocationAllocationReceipt
/-! Actual body policies retain their marked allocator. Receipts are indexed
by the compiler's concrete request source, independently of runtime Source.
Only the genuine body owner and input identifiers are related here. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.ActualBodyInvocation
open Core Frontend SourceInference

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {bodyRelation : BodyRelation}

def Index.allocationCallback (index : Index compiled bodyRelation) : SourceCoreSourceCells.Allocator :=
  SourceCoreCallableIndexedAllocationFrames.allocator compiled.indexed.ancestry.layout.frame
    compiled.indexed.base.globals.length
    (compiled.indexed.layouts.allocatorAt index.owner index.active
      (fun error => .sourceAllocation (reprStr error)))

theorem Index.sourceCells (index : Index compiled bodyRelation) :
    index.policy.sourceCells = some index.allocationCallback := by
  cases index with
  | named receipt selected => rfl
  | contextual material view =>
    change (material.inputs.representation.atContext material.inputs.current.owner
      material.packet.original.emission.prepared.substitution).expressions.sourceCells = _
    rw [material.indexed.represented]
    change some (SourceCoreCallableIndexedAllocationFrames.allocator _ _
      (compiled.indexed.layouts.allocatorAt material.inputs.current.owner
        material.packet.original.emission.prepared.substitution
        (fun error => .sourceAllocation (reprStr error)))) = _
    simp only [Index.allocationCallback, Index.owner, Index.active, material.compilation,
      material.active, GeneralizedLocalLambdaCompilation.context]

theorem Index.compiler_owner (index : Index compiled ReachedView) :
    index.compilerSource.owner = index.source.owner := index.reached_view.owner.symm

theorem Index.compiler_inputs (index : Index compiled ReachedView) :
    index.compilerSource.inputs.map (·.id) = index.source.inputs.map (·.id) :=
  index.reached_view.inputs.symm

theorem Index.compiler_noninput (index : Index compiled ReachedView)
    {binder : Resolved.LocalId}
    (ordinary : index.source.inputs.any (fun input => decide (input.id = binder)) = false) :
    index.compilerSource.inputs.any (fun input => decide (input.id = binder)) = false := by
  have same := congrArg (fun inputs : List Resolved.LocalId => inputs.any (fun input => decide (input = binder))) index.compiler_inputs
  simp only [List.any_map, Function.comp_def] at same
  exact same.trans ordinary

/-- The annotation and marked allocation are returned by their original
factories at exactly the request passed by the accepted body policy. -/
theorem Index.allocation_receipt (index : Index compiled bodyRelation)
    {request : SourceCoreSourceCells.Request} {code : Expr}
    (accepted : index.allocationCallback request = .ok code) :
    ∃ allocation : SourceCoreAllocationLayouts.Allocation compiled.indexed.layouts
        index.owner index.active request,
      ∃ annotation : SourceCoreCallableIndexedAllocationFrames.Annotated
          compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
          (compiled.indexed.layouts.allocatorAt index.owner index.active
            (fun error => .sourceAllocation (reprStr error))) request,
        annotation.original = allocation.expression ∧ annotation.expression = code := by
  unfold Index.allocationCallback at accepted
  obtain ⟨annotation, created, exact⟩ := CallableIndexedAllocation.allocator_receipt _ _ _ _ accepted
  have allocated := annotation.allocated
  unfold SourceCoreAllocationLayouts.Prepared.allocatorAt at allocated
  cases actual : SourceCoreAllocationLayouts.allocate compiled.indexed.layouts index.owner index.active request with
  | error error => simp only [actual, Except.mapError, reduceCtorEq] at allocated
  | ok output =>
    have same : output = annotation.original := by simpa only [actual, Except.mapError, Except.ok.injEq] using allocated
    obtain ⟨allocation, result⟩ := SourceCoreAllocationLayouts.allocate_receipt actual
    exact ⟨allocation, annotation, same.symm.trans result.symm, annotation.exact.trans exact.symm⟩

/-- A successful initialized let exposes its actual marked callback and its
literal continuation; no metadata equality of the two source tables is used. -/
theorem Index.let_initialized_receipt (index : Index compiled bodyRelation)
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {binder : TypedBinder}
    {output payload : Ty} {initializer body code : Expr}
    (accepted : SourceCoreSourceCells.letInitialized index.policy.sourceCells source scope Renaming.id
      binder (LocalLoop.controlType output) payload initializer body = .ok code) :
    ∃ allocation : SourceCoreAllocationLayouts.Allocation compiled.indexed.layouts
        index.owner index.active (TypedLexicalWhile.initializedRequest source scope binder payload),
      ∃ annotation : SourceCoreCallableIndexedAllocationFrames.Annotated
          compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
          (compiled.indexed.layouts.allocatorAt index.owner index.active
            (fun error => .sourceAllocation (reprStr error)))
          (TypedLexicalWhile.initializedRequest source scope binder payload),
        annotation.original = allocation.expression ∧
        code = TypedLexicalWhile.sequence output initializer annotation.expression body := by
  rw [index.sourceCells] at accepted
  unfold SourceCoreSourceCells.letInitialized at accepted
  cases allocated : index.allocationCallback (TypedLexicalWhile.initializedRequest source scope binder payload) with
  | error error =>
    simp only [TypedLexicalWhile.initializedRequest, CompatibleStatementInitialized.request] at allocated
    simp only [allocated, bind, Except.bind, reduceCtorEq] at accepted
  | ok allocationCode =>
    have emitted : code = TypedLexicalWhile.sequence output initializer allocationCode body := by
      simp only [TypedLexicalWhile.initializedRequest, CompatibleStatementInitialized.request] at allocated
      simpa only [allocated, bind, Except.bind, pure, Except.pure, Except.ok.injEq,
        TypedLexicalWhile.sequence, CompatibleStatementInitialized.sequence] using accepted.symm
    obtain ⟨allocation, annotation, same, codeEq⟩ := index.allocation_receipt allocated
    exact ⟨allocation, annotation, same, emitted.trans (by rw [codeEq])⟩

/-- The absent payload branch uses the same concrete indexed allocator. -/
theorem Index.let_uninitialized_receipt (index : Index compiled bodyRelation)
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {binder : TypedBinder}
    {payload : Ty} {body code : Expr}
    (accepted : SourceCoreSourceCells.letUninitialized index.policy.sourceCells source scope Renaming.id
      binder payload body = .ok code) :
    ∃ allocation : SourceCoreAllocationLayouts.Allocation compiled.indexed.layouts
        index.owner index.active (TypedLexicalWhile.absentRequest source scope binder payload),
      ∃ annotation : SourceCoreCallableIndexedAllocationFrames.Annotated
          compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
          (compiled.indexed.layouts.allocatorAt index.owner index.active
            (fun error => .sourceAllocation (reprStr error)))
          (TypedLexicalWhile.absentRequest source scope binder payload),
        annotation.original = allocation.expression ∧ code = .letE annotation.expression body := by
  rw [index.sourceCells] at accepted
  unfold SourceCoreSourceCells.letUninitialized at accepted
  cases allocated : index.allocationCallback (TypedLexicalWhile.absentRequest source scope binder payload) with
  | error error =>
    simp only [TypedLexicalWhile.absentRequest] at allocated
    simp only [allocated, bind, Except.bind, reduceCtorEq] at accepted
  | ok allocationCode =>
    have emitted : code = .letE allocationCode body := by
      simp only [TypedLexicalWhile.absentRequest] at allocated
      simpa only [allocated, bind, Except.bind, pure, Except.pure, Except.ok.injEq] using accepted.symm
    obtain ⟨allocation, annotation, same, codeEq⟩ := index.allocation_receipt allocated
    exact ⟨allocation, annotation, same, emitted.trans (by rw [codeEq])⟩

end Solcore.SourceSemantics.CoreLowering.ActualBodyInvocation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ActualBodyInvocationAssignmentPolicy
/-! Each actual named or contextual body policy has the shared compatible
assignment callbacks, with the diagnostic words of its own fault tables. An
accepted value assignment is therefore the shared place lowering. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.ActualBodyInvocation
open Core Frontend SourceInference
open CompatibleAssignmentStatements (AssignmentPolicy)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {bodyRelation : BodyRelation}

/-- The assignment fault table compiled with this body. -/
def Index.assignmentTable : Index compiled bodyRelation → SourceCoreAssignmentFaultSites.Table
  | .named receipt _ => receipt.own.assignments
  | .contextual material _ => material.inputs.assignments

/-- The place-fault program and owner used by this body's assignment callbacks. -/
def Index.placeDiagnostics : Index compiled bodyRelation → SourceCoreDataPlaceFaultSites.Program
  | @Index.named _ _ _ diagnostics _ _ _ => diagnostics
  | .contextual material _ => material.inputs.diagnostics

def Index.placeOwner : Index compiled bodyRelation → SourceSpecialization.SpecializationKey
  | @Index.named _ _ callable _ _ _ _ => callable.signature.key
  | .contextual material _ => material.inputs.current.owner

def Index.invalidProjection (index : Index compiled bodyRelation)
    (site : SourceCoreElaboration.ErrorSite) (root : Resolved.LocalId) : Word :=
  index.placeDiagnostics.placeReason index.placeOwner site root none

def Index.invalidOperand (index : Index compiled bodyRelation)
    (site : SourceCoreElaboration.ErrorSite) (root : Resolved.LocalId) (operator : Syntax.ValueAssignOp) : Word :=
  if operator = .equal then Word.zero else index.assignmentTable.reasonAt site root (.value operator)

def Index.missingDefault (index : Index compiled bodyRelation)
    (site : SourceCoreElaboration.ErrorSite) (root : Resolved.LocalId) (type : TypeSystem.Ty) : Word :=
  index.placeDiagnostics.placeReason index.placeOwner site root (some type)

theorem Index.assignment_policy (index : Index compiled bodyRelation) :
    AssignmentPolicy index.policy (.initial compiled.compatible.checked) index.invalidProjection
      index.invalidOperand index.missingDefault := by
  cases index with
  | named receipt selected =>
    refine ⟨rfl, rfl, ?_⟩
    change some _ = some _
    apply congrArg some
    funext expression fuel source scope site assignment operator rhs output next reasonAt
    cases operator <;> rfl
  | contextual material view =>
    change AssignmentPolicy (GeneralizedLocalAcceptedBodyCompiler.policy material) _ _ _ _
    unfold GeneralizedLocalAcceptedBodyCompiler.policy GeneralizedLocalLambdaCompilation.representation
    rw [material.indexed.represented]
    refine ⟨rfl, rfl, ?_⟩
    change some _ = some _
    apply congrArg some
    funext expression fuel source scope site assignment operator rhs output next reasonAt
    cases operator <;> rfl

/-- An accepted value assignment is the shared place lowering at the initial
values context, with this body's diagnostic words. -/
theorem Index.assignment_lowered (index : Index compiled bodyRelation) {fuel : Nat} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {site : SourceCoreElaboration.ErrorSite}
    {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    {output : Ty} {next code : Expr} {reasonAt : ExpressionId → Word}
    (accepted : SourceCoreLoops.assignValue index.policy fuel source scope site assignment operator rhs
      output next reasonAt = .ok code) :
    SourceCoreCompatibleDataPlaces.lower (.initial compiled.compatible.checked)
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).checked.signatures
      index.policy.lowerExpression fuel source scope site assignment operator (some rhs) output next reasonAt
      (index.invalidProjection site assignment.target.root) (index.invalidOperand site assignment.target.root operator)
      (index.missingDefault site assignment.target.root) = .ok code := by
  have matched := index.assignment_policy
  cases operator <;> simpa only [SourceCoreLoops.assignValue, matched.equal, matched.value] using accepted

def Index.invalidUnary (index : Index compiled bodyRelation)
    (site : SourceCoreElaboration.ErrorSite) (root : Resolved.LocalId) : Word :=
  index.assignmentTable.reasonAt site root .bitNot

theorem Index.bitNot_policy (index : Index compiled bodyRelation) :
    CompatibleBitNotStatements.Policy index.policy (.initial compiled.compatible.checked) index.invalidProjection
      index.invalidUnary index.missingDefault := by
  cases index with
  | named receipt selected => rfl
  | contextual material view =>
    change CompatibleBitNotStatements.Policy (GeneralizedLocalAcceptedBodyCompiler.policy material) _ _ _ _
    unfold GeneralizedLocalAcceptedBodyCompiler.policy GeneralizedLocalLambdaCompilation.representation
    rw [material.indexed.represented]
    rfl

/-- An accepted bit-not update is the shared absent-operand place lowering. -/
theorem Index.bitNot_lowered (index : Index compiled bodyRelation) {fuel : Nat} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {site : SourceCoreElaboration.ErrorSite}
    {assignment : AssignmentResolution} {output : Ty} {next code : Expr} {reasonAt : ExpressionId → Word}
    {callback : SourceCoreCompatibleDataPlaces.ExpressionLowerer → Nat → TypedSource → SourceCoreLocalCell.Scope →
      SourceCoreElaboration.ErrorSite → AssignmentResolution → Ty → Expr →
      (ExpressionId → Word) → Except SourceCoreBasic.Error Expr}
    (selected : index.policy.assignBitNotWithExpression = some callback)
    (accepted : callback index.policy.lowerExpression fuel source scope site assignment output next reasonAt = .ok code) :
    SourceCoreCompatibleDataPlaces.lower (.initial compiled.compatible.checked)
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).checked.signatures
      index.policy.lowerExpression fuel source scope site assignment .equal none output next reasonAt
      (index.invalidProjection site assignment.target.root) (index.invalidUnary site assignment.target.root)
      (index.missingDefault site assignment.target.root) = .ok code := by
  have same := Option.some.inj (selected.symm.trans index.bitNot_policy)
  subst same
  exact accepted

end Solcore.SourceSemantics.CoreLowering.ActualBodyInvocation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ActualBodyInvocationSnapshotReceipt
/-! A generalized declaration of an actual body policy snapshots its scope. Its
marked descriptor allocation has the same receipt as an ordinary initialized
let; the scope copies around the bundle initializer and that allocation are
returned with the literal continuation. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.ActualBodyInvocation
open Core Frontend SourceInference
open CellAwareGeneralizedSnapshotCode (snapshotInner snapshotSequence)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {bodyRelation : BodyRelation}

/-- A successful snapshot declaration exposes its actual marked callback, the
scope copies it emits around the bundle and its allocation, and its literal
continuation. -/
theorem Index.let_initialized_snapshot_receipt (index : Index compiled bodyRelation)
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {binder : TypedBinder}
    {output payload : Ty} {initializer body code : Expr}
    (accepted : SourceCoreSourceCells.letInitializedSnapshot index.policy.sourceCells source scope binder
      (LocalLoop.controlType output) payload initializer body = .ok code) :
    ∃ allocation : SourceCoreAllocationLayouts.Allocation compiled.indexed.layouts
        index.owner index.active (TypedLexicalWhile.initializedRequest source scope binder payload),
      ∃ annotation : SourceCoreCallableIndexedAllocationFrames.Annotated
          compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
          (compiled.indexed.layouts.allocatorAt index.owner index.active
            (fun error => .sourceAllocation (reprStr error)))
          (TypedLexicalWhile.initializedRequest source scope binder payload),
        annotation.original = allocation.expression ∧
        ∃ captured, SourceCoreSourceCells.copyScope (some index.allocationCallback) source scope
            (fun index => index) (snapshotInner payload initializer annotation.expression) = .ok captured ∧
          code = snapshotSequence output captured body := by
  rw [index.sourceCells] at accepted
  simp only [SourceCoreSourceCells.letInitializedSnapshot] at accepted
  obtain ⟨allocationCode, generated, accepted⟩ := CompatibleEncoding.bind_ok accepted
  obtain ⟨captured, copied, accepted⟩ := CompatibleEncoding.bind_ok accepted
  cases accepted
  obtain ⟨allocation, annotation, same, codeEq⟩ :=
    index.allocation_receipt (request := TypedLexicalWhile.initializedRequest source scope binder payload) generated
  subst codeEq
  exact ⟨allocation, annotation, same, captured, copied, rfl⟩

end Solcore.SourceSemantics.CoreLowering.ActualBodyInvocation
end
