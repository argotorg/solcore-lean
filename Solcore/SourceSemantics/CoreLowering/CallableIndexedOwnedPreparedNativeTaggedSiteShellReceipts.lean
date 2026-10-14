import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeSiteShellReceipts

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
        cases compiled.indexed.base.callableContext <;> rfl⟩
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
