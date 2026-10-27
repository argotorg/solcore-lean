import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedDirectSites
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedExpressionTrees
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDirectCallAuthority
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedExpressionSequence

/-! Direct calls at the expression roots of named-row bodies. `CallSubset`
adds to the first subset the direct calls whose arguments are first-subset
sites and whose instantiation the caller's family admits (`called`).
`CallTree` keeps, at such a call, the compiler's direct-call receipt at the
body's compile context, the authority of the selected header and the subset
receipt tree of every argument. A call nested inside another expression is
not covered yet. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedCallTrees
open Core Frontend SourceInference DataPatternValues
open CallableIndexedNamedGeneration (Prepared Compilation context)
open GeneralizedLocalInitializerCompilation (namedPolicy namedLowerBody)
open CellAwareNamedExpressionSyntax (Site)
open CellAwareInvocationAcceptedExpressionTrees (Subset Tree)
open CellAwareInvocationAcceptedDirectSites (DirectSite)
open CallableIndexedOwnedPreparedStagedDirectCallCertificates (Receipt Monomorphic)
open CallableIndexedOwnedPreparedStagedDirectCallAuthority (Port)

/-- Expression roots of the extended subset: first-subset sites, and direct
calls whose arguments are first-subset sites and whose instantiation the
caller's family admits. -/
inductive CallSubset {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function)
    (source : TypedSource) (called : DeclarationInstantiation → Prop) : ExpressionId → Prop where
  | subset {id} (subset : Subset prepared named source id) : CallSubset prepared named source called id
  | call {id callee ids instantiation} (site : DirectSite prepared named source id callee ids instantiation)
      (selected : called instantiation) (arguments : ∀ argument ∈ ids, Subset prepared named source argument) :
      CallSubset prepared named source called id

/-- Static receipts at extended roots. The certificate of the argument
sequence is the first-subset receipt tree at every scope. -/
inductive CallTree (whole : SourceCoreUnifiedCompilation.Compiled)
    (headers : List (CallableIndexedOwnedFunctionValues.Header whole (Program.ofChecked whole.sourceProgram)))
    (called : DeclarationInstantiation → Prop) (compilation : SourceCoreFunctions.Context)
    (readFuel : Nat) (solved : List SolvedRequirement) (source : TypedSource)
    (sourceContext : SourceSemantics.Context) (reasonAt : ExpressionId → Word) (scope : SourceCoreLocalCell.Scope) :
    ExpressionId → SourceCoreBasic.LoweredExpr → Prop where
  | tree {id lowered}
      (tree : Tree whole.compatible.checked readFuel solved source sourceContext reasonAt scope id lowered) :
      CallTree whole headers called compilation readFuel solved source sourceContext reasonAt scope id lowered
  | call {policy body fuel id callee ids instantiation lowered types}
      (receipt : Receipt policy body fuel compilation (.initial whole.compatible.checked) source scope id callee ids
        instantiation reasonAt lowered)
      (port : Port receipt headers)
      (requirements : receipt.node.requirements = [])
      (monomorphic : Monomorphic instantiation)
      (selected : called instantiation)
      (arguments : DataExpressionSequence.Tree source
        (fun current child code => Tree whole.compatible.checked readFuel solved source sourceContext reasonAt
          current child code)
        scope ids types receipt.codes) :
      CallTree whole headers called compilation readFuel solved source sourceContext reasonAt scope id lowered

section Embedding
variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
  {named : SourceCoreGeneralFunctions.Function} {source : TypedSource}

theorem subset_found {id : ExpressionId} (subset : Subset prepared named source id) :
    ∃ node, source.lookupExpression? id = some node := by
  cases subset with
  | literal site _ | read site _ | unary site _ _ | binary site _ _ _ | conditional site _ _ _ _
  | group site _ _ | pair site _ _ _ => exact ⟨_, site.found⟩

end Embedding

variable {whole : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole (Program.ofChecked whole.sourceProgram))}
  {called : DeclarationInstantiation → Prop}
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
  (generation : Compilation whole.indexed named diagnostics code) (rootFuel : Nat)
  {source : TypedSource} {sourceContext : SourceSemantics.Context}
  {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Word}

private theorem special {id callee : ExpressionId} {ids : List ExpressionId} {instantiation : DeclarationInstantiation}
    (site : DirectSite whole.indexed named source id callee ids instantiation) :
    ∀ child budget, (match (namedPolicy generation rootFuel).lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower (context whole.indexed named) child budget source scope id reasonAt) = .ok none :=
  fun child budget => CellAwareInvocationAcceptedDirectSites.special generation site rootFuel child budget scope reasonAt

private theorem argument_rel {lower : ExpressionId → Except SourceCoreBasic.Error SourceCoreBasic.LoweredExpr}
    {relation : ExpressionId → SourceCoreBasic.LoweredExpr → Prop} :
    ∀ {ids : List ExpressionId} {codes : List SourceCoreBasic.LoweredExpr},
      (∀ argument ∈ ids, ∀ {lowered}, lower argument = .ok lowered → relation argument lowered) →
      ids.mapM lower = .ok codes → ListRel relation ids codes := by
  intro ids
  induction ids with
  | nil =>
    intro codes _ generated
    simp at generated
    subst codes
    exact .nil
  | cons argument rest ih =>
    intro codes each generated
    cases head : lower argument with
    | error reason => simp [List.mapM_cons, head, bind, Except.bind] at generated
    | ok lowered =>
      cases tail : rest.mapM lower with
      | error reason => simp [List.mapM_cons, head, tail, bind, Except.bind] at generated
      | ok restCodes =>
        simp only [List.mapM_cons, head, tail, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at generated
        subst codes
        exact .cons (each argument List.mem_cons_self head)
          (ih (fun other member => each other (List.mem_cons_of_mem _ member)) tail)

/-- The accepted named compiler yields the extended receipt tree at every
extended root. A call's authority is the input `ports`, as the older direct
families take theirs. -/
theorem of_call_subset {id : ExpressionId}
    (subset : CallSubset whole.indexed named source called id)
    (unique : NodeOccurrencesUnique source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope sourceContext)
    {node : ExpressionNode} (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source sourceContext id node.type)
    {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy (namedPolicy generation rootFuel)
      (namedLowerBody generation) fuel (context whole.indexed named) source scope id reasonAt = .ok lowered)
    (ports : ∀ {fuel : Nat} {callScope : SourceCoreLocalCell.Scope} {callId callee : ExpressionId}
      {ids : List ExpressionId} {instantiation : DeclarationInstantiation} {callCode : SourceCoreBasic.LoweredExpr}
      (receipt : Receipt (namedPolicy generation rootFuel) (namedLowerBody generation) fuel
        (context whole.indexed named) (.initial whole.compatible.checked) source callScope callId callee ids
        instantiation reasonAt callCode),
      Nonempty (Port receipt headers)) :
    CallTree whole headers called (context whole.indexed named) whole.indexed.fuel
      (context whole.indexed named).solvedRequirements source sourceContext reasonAt scope id lowered := by
  cases subset with
  | subset subset =>
    exact .tree (CellAwareInvocationAcceptedExpressionTrees.of_subset generation rootFuel subset unique declarations
      found typed accepted)
  | @call callee ids instantiation site selected arguments =>
    have same := Option.some.inj (site.found.symm.trans found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      obtain ⟨receipt⟩ := CallableIndexedOwnedPreparedStagedDirectCallCertificates.of_supported
        (policy := namedPolicy generation rootFuel) (body := namedLowerBody generation) (fuel := fuel)
        (compilation := context whole.indexed named) (values := .initial whole.compatible.checked)
        (scope := scope) (reasonAt := reasonAt) site.found site.form
        ((site.monomorphic.ordinary _).supported) (special generation rootFuel site)
        (CellAwareInvocationAcceptedDirectSites.read generation site rootFuel) accepted
      obtain ⟨port⟩ := ports receipt
      have nodeEq : receipt.node = site.node := Option.some.inj (receipt.metadata.found.symm.trans site.found)
      obtain ⟨_types, _calleeValid, _application, typing⟩ :=
        CallableIndexedOwnedPreparedStagedDirectCallCertificates.source_types unique site.found site.form
          site.coercions typed
      have relation := argument_rel
        (relation := fun argument lowered => ∃ node, source.lookupExpression? argument = some node ∧
          Tree whole.compatible.checked whole.indexed.fuel (context whole.indexed named).solvedRequirements source
            sourceContext reasonAt scope argument lowered)
        (fun argument member {lowered} generated => by
          obtain ⟨argumentNode, argumentFound⟩ := subset_found (arguments argument member)
          exact ⟨argumentNode, argumentFound,
            CellAwareInvocationAcceptedExpressionTrees.of_subset generation rootFuel (arguments argument member)
              unique declarations argumentFound
              (CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique typing member
                argumentFound) generated⟩)
        receipt.generated
      obtain ⟨_storedTypes, sequence⟩ := DataExpressionSequence.Tree.of_children relation
      exact .call receipt port (nodeEq ▸ site.requirements) site.monomorphic selected sequence

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedCallTrees
