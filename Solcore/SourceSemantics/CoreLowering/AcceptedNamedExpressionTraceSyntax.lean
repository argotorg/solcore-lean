import Solcore.SourceSemantics.CoreLowering.AcceptedNamedExpressionTree

/-! The compiler trace supplies original expression syntax or an exact path to
an unexpanded action. Successful traversal covers every ordered argument. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.AcceptedNamedExpressionFlow
open Core Frontend SourceInference
open CallableIndexedNamedGeneration
open CallableIndexedOwnedContextualCompilerPolicyProfiles (RootPolicyReceipt)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : Compilation compiled.indexed named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  {root : RootPolicyReceipt (compiled := compiled) named diagnostics namedCode compilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered}
  {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Word}
  {fuel : Nat} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  {directSites : DeclarationInstantiation → Prop}

/-- The residual names the same trace and follows its actual child positions.
Argument coverage uses accepted map traversal, including repeated occurrences. -/
theorem Trace.syntax_or_boundary
    (trace : Trace root source scope reasonAt fuel id lowered)
    (covered : ∀ child node, source.lookupExpression? child = some node →
      ∀ callee args instantiation, node.form = .call callee args (.declaration instantiation) →
        directSites instantiation) :
    GeneralSyntax source id directSites ∨ Nonempty (Boundary trace) := by
  classical
  induction trace with
  | @step fuel id lowered actual children ih =>
    by_cases all : ∀ entry ∈ actual.children, GeneralSyntax source entry.1 directSites
    · cases actual with
      | leaf head plain form =>
        rcases form.view with atomic | ⟨name, binder, localForm⟩
        · exact .inl (.leaf (.literal head.found atomic))
        · exact .inl (.leaf (.read head.found localForm))
      | boundary head cause => exact .inr ⟨.here head cause children⟩
      | ordinary head plain receipt =>
        refine .inl (.direct receipt.metadata.found receipt.form
          (covered id receipt.node receipt.metadata.found _ _ _ receipt.form) ?_)
        intro argument member
        obtain ⟨code, present⟩ := (mapM_receipt receipt.generated).2.2 argument member
        exact all (argument, code) present
      | evidence head selected receipt =>
        refine .inl (.direct receipt.found receipt.form
          (covered id head.node receipt.found _ _ _ receipt.form) ?_)
        intro argument member
        obtain ⟨code, present⟩ := (mapM_receipt receipt.argumentsAccepted).2.2 argument member
        exact all (argument, code) present
    · obtain ⟨entry, absent⟩ := Classical.not_forall.mp all
      have member : entry ∈ actual.children := Classical.byContradiction fun missing =>
        absent (fun present => False.elim (missing present))
      have missing : ¬ GeneralSyntax source entry.1 directSites :=
        fun grammar => absent (fun _ => grammar)
      cases ih entry member with
      | inl grammar => exact False.elim (missing grammar)
      | inr boundary => exact .inr ⟨.child actual children entry member (Classical.choice boundary)⟩

end Solcore.SourceSemantics.CoreLowering.AcceptedNamedExpressionFlow
