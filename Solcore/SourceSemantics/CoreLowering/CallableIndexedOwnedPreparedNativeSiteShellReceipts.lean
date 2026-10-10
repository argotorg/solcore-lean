import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeCompilerChildren
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeSitePolicies
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLocalIdentityFreshness
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSelectedDiagnosticIssuerReceipts
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedImperativeMatchSyntaxFactory

/-! One selected compilation, its positive issuer, and the actual lambda Site
construct the native child collector's static shell. Finite Source body receipts,
parent declarations, and the same solved requirement ledger remain explicit.
Entry, frame, freshness, policy, projection, and diagnostic providers are built
internally. There is no body execution premise or completed JointBody input. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeSiteShellReceipts
open Core Frontend SourceInference
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration CallableIndexedLambdaValues
open CallableIndexedOwnedContextualCompilerPolicyProfiles
open CallableIndexedOwnedContextualLambdaJointStaticReceipts
open CallableIndexedOwnedContextualLambdaSourceDiagnostics
open CallableIndexedOwnedSelectedDiagnosticIssuerReceipts
open RecursiveNamedStatementSyntaxFacts

/-- A finite receipt retains the genuine Source parameter fold and its body
judgment. It authorizes only these parameters and statements at this context;
the original syntax factory still performs the finite body induction. -/
inductive FiniteBodyReceipts (source : TypedSource) (expressionSyntax : ExpressionId → Prop)
    (context : SourceSemantics.Context) (parameters : List TypedBinder)
    (result : TypeSystem.Ty) (statements : List StatementId) : Prop where
  | intro {entryContext finalContext : SourceSemantics.Context}
      {parameterTypes : List TypeSystem.Ty} {facts : BodyFacts} {ready : Bool}
      (extended : MonoBindersExtend source.owner context parameters parameterTypes entryContext)
      (typed : StatementsHaveType source {returnType := result} entryContext statements finalContext facts)
      (receipt : BodyReceipts source expressionSyntax typed ready)
      (annotation : facts.type = result) :
      FiniteBodyReceipts source expressionSyntax context parameters result statements

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

/-- This issuer is transported only along the actual Site's owning compilation.
Its first token, table, selected assignment row, and full Source are unchanged. -/
def issued_at_site : IssuedSource compiled site.code.compilation.owner (source named) := by
  refine {
    first := selected.issued.first
    assignments := selected.issued.assignments
    assignmentsPrepared := selected.issued.assignmentsPrepared
    typing := selected.issued.typing
    plan := selected.issued.plan
    root := selected.issued.root
    extra := selected.issued.extra
    diagnostics := selected.issued.diagnostics
    prepared := selected.issued.prepared
    collected := ?_ }
  rw [site.compilation]
  exact selected.issued.collected

/-- Every shell field is derived at the literal Site and selected compilation.
An ordinary Header or selected Principal may supply this same genuine Named;
no ordinary Header is manufactured for a method. -/
theorem of_selected
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
    Nonempty (CallableIndexedOwnedPreparedNativeCompilerChildren.SiteShell
      (compilation := selected.compilation) expressionSyntax site) := by
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
        ledger := ?_ } }⟩
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
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeSiteShellReceipts
