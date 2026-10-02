import Solcore.SourceSemantics.CoreLowering.CallableCallEvidenceCertificates
import Solcore.Frontend.SourceCoreLocalEvidence
import Solcore.Test.SourceCompilerFeatureSupport

/-! Accepted outer evidence lowering supplies full selected metadata and the
independent ordered dictionary. None delegates ordinary lowering and does not
certify a target. Actual closed and contextual-local callers share the receipt. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.SourceSemantics.CoreLowering.CallableCallEvidenceCertificates.Selection.mk
set_option autoImplicit false
namespace Tests.SourceCoreCallableCallEvidenceCertificates
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CallableCallEvidenceCertificates
open CallableNamedMetadata (environment)

/-- The final consumer assumes one actual compiler action, rather than its
resolver, materializer, authenticator or target-predicate subresults. -/
theorem direct_from_outer {program : CheckedProgram} {projectType : SourceCoreEvidence.Projector}
    {caller : Specialized} {compilation : SourceCoreFunctions.Context} {child : SourceCoreEvidence.Child}
    {fuel : Nat} {source : TypedSource} {scope : SourceCoreEvidence.Scope} {id callee : ExpressionId}
    {reasonAt : ExpressionId → Word} {callables : SourceCoreFunctions.CallablePolicy}
    {node : ExpressionNode} {arguments : List ExpressionId} {instantiation : DeclarationInstantiation}
    {lowered : SourceCoreEvidence.Lowered} {context : SourceSemantics.Context}
    (found : source.lookupExpression? id = some node)
    (form : node.form = .call callee arguments (.declaration instantiation))
    (accepted : SourceCoreEvidence.lowerWithProjector program projectType caller compilation child fuel source scope id reasonAt callables = .ok (some lowered))
    (signatures : context.signatures = program.signatures)
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (assumptions : ∀ goal, goal ∈ caller.assumptions → goal ∈ context.assumptions)
    (unique : RequirementIdsUnique context) :
    ∃ receipt : Selection program caller compilation node instantiation false,
      CallableNamedMetadata.Matches receipt.specialized instantiation ∧
      (∃ calleeNode name, source.lookupExpression? callee = some calleeNode ∧
        calleeNode.form = .reference name (.declaration instantiation) ∧ calleeNode.type = instantiation.type) ∧
      arguments.length = receipt.specialized.function.typedBody.inputs.length ∧
      Dynamic.DirectCallProducesEvidence context (environment receipt.available) node.requirements node.coercions
        instantiation.predicates (environment receipt.actual) ∧
      ∀ semantic, Dynamic.DirectCallProducesEvidence context (environment receipt.available) node.requirements node.coercions
        instantiation.predicates semantic → semantic = environment receipt.actual := by
  obtain ⟨receipt, validated, arity⟩ := direct_of_accepted found form accepted
  exact ⟨receipt, receipt.metadata, callee_metadata validated, arity, receipt.direct_produces signatures ledger assumptions,
    fun _ produced => receipt.direct_agrees ledger (CallableCallRequirementLayouts.singletons_of_unique ledger unique) produced⟩

theorem reference_from_outer {program : CheckedProgram} {projectType : SourceCoreEvidence.Projector}
    {caller : Specialized} {compilation : SourceCoreFunctions.Context} {child : SourceCoreEvidence.Child}
    {fuel : Nat} {source : TypedSource} {scope : SourceCoreEvidence.Scope} {id : ExpressionId}
    {reasonAt : ExpressionId → Word} {callables : SourceCoreFunctions.CallablePolicy}
    {node : ExpressionNode} {name : String} {instantiation : DeclarationInstantiation}
    {lowered : SourceCoreEvidence.Lowered} {context : SourceSemantics.Context}
    (found : source.lookupExpression? id = some node)
    (form : node.form = .reference name (.declaration instantiation))
    (accepted : SourceCoreEvidence.lowerWithProjector program projectType caller compilation child fuel source scope id reasonAt callables = .ok (some lowered))
    (signatures : context.signatures = program.signatures)
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (assumptions : ∀ goal, goal ∈ caller.assumptions → goal ∈ context.assumptions) :
    ∃ receipt : Selection program caller compilation node instantiation true,
      CallableNamedMetadata.Matches receipt.specialized instantiation ∧
      (∃ ids, Dynamic.OrdinaryRequirementLayout node.requirements node.coercions ids ∧
        Dynamic.RequirementsProduceEnvironment context (environment receipt.available) ids instantiation.predicates (environment receipt.actual)) ∧
      ∀ ids semantic, Dynamic.OrdinaryRequirementLayout node.requirements node.coercions ids →
        Dynamic.RequirementsProduceEnvironment context (environment receipt.available) ids instantiation.predicates semantic →
          semantic = environment receipt.actual := by
  obtain ⟨receipt⟩ := reference_of_accepted found form accepted
  exact ⟨receipt, receipt.metadata, receipt.reference_produces signatures ledger assumptions,
    fun _ _ layout produced => receipt.reference_agrees ledger layout produced⟩

/-- Authenticated local preparation supplies the actual rewritten caller. The
same outer declaration branch determines the returned dictionary inside it. -/
theorem prepared_local_direct {program : CheckedProgram} {projectType : SourceCoreEvidence.Projector}
    {parent : SourceCoreLocalEvidence.Prepared} {compilation : SourceCoreFunctions.Context}
    {child : SourceCoreEvidence.Child} {fuel : Nat} {scope : SourceCoreEvidence.Scope} {id callee : ExpressionId}
    {reasonAt : ExpressionId → Word} {callables : SourceCoreFunctions.CallablePolicy}
    {node : ExpressionNode} {arguments : List ExpressionId} {instantiation : DeclarationInstantiation}
    {lowered : SourceCoreEvidence.Lowered}
    (found : parent.source.lookupExpression? id = some node)
    (form : node.form = .call callee arguments (.declaration instantiation))
    (accepted : SourceCoreEvidence.lowerWithProjector program projectType parent.caller compilation child fuel parent.source scope id reasonAt callables = .ok (some lowered)) :
    ∃ receipt : Selection program parent.caller compilation node instantiation false,
      CallableNamedMetadata.Matches receipt.specialized instantiation ∧
      receipt.specialized.assumptions = instantiation.predicates := by
  obtain ⟨receipt, _, _⟩ := direct_of_accepted found form accepted
  exact ⟨receipt, receipt.metadata, receipt.metadata.predicates⟩

private def emptyPlan : SourceCompilationPlan.Plan := ⟨[], [], [], []⟩

/-- Even a missing declaration target is compatible with none: the evidence
pass has delegated, and the ordinary traversal must still check this call. -/
theorem bypass_is_not_selection {program : CheckedProgram} {projectType : SourceCoreEvidence.Projector}
    {caller : Specialized} {compilation : SourceCoreFunctions.Context} {child : SourceCoreEvidence.Child}
    {fuel : Nat} {source : TypedSource} {scope : SourceCoreEvidence.Scope} {id callee : ExpressionId}
    {reasonAt : ExpressionId → Word} {callables : SourceCoreFunctions.CallablePolicy}
    {node : ExpressionNode} {arguments : List ExpressionId} {instantiation : DeclarationInstantiation}
    (found : source.lookupExpression? id = some node)
    (form : node.form = .call callee arguments (.declaration instantiation))
    (requirements : node.requirements = []) (coercions : node.coercions = []) (assumptions : caller.assumptions = []) :
    SourceCoreEvidence.lowerWithProjector program projectType caller {compilation with plan := emptyPlan}
      child fuel source scope id reasonAt callables = .ok none ∧
    SourceCompilationPlan.exactInstantiationKey emptyPlan instantiation =
      .error (.missingInstantiationTarget instantiation.declaration instantiation.type) :=
  ⟨direct_bypass found form requirements coercions assumptions, rfl⟩

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Mark<T> {}", "impl Mark<Word> {}", "impl Mark<Bool> {}",
    "function value() returns (Word) where Word: Mark { return 4; }",
    "function empty() returns (Word) { return 5; }",
    "function direct() returns (Word) { return value(); }",
    "function inherited() returns (Word) where Word: Mark { return empty(); }",
    "function referenced() returns (Word) { let f: function() returns (Word) = value; return f(); }",
    "function keep<T>(item: T) returns (T) where T: Mark { return item; }",
    "function local(flag: Bool) returns (Word, Word) { let f = lam(item) { keep(item); return value(); }; return (f(7), f(flag)); }",
    "function failed() returns (Word) { let table: mapping(Word => Word); table[0] = value(); let absent: Word; return absent; }"
  ]}] }

private def rejectChild : SourceCoreEvidence.Child := fun _ _ _ id _ => .error (.missingExpression id)

/-- Audit only nullary named calls and retained declaration reference edges.
These use the real outer compiler without requiring any child callback. -/
private def auditSource (entry : SourceCompilerFeatureSupport.Entry) (caller : Specialized)
    (source : TypedSource) : IO (Nat × Nat × Nat) := do
  let base := entry.cached.indexed.base
  let context : SourceCoreFunctions.Context := {
    plan := base.plan
    owner := caller.key
    globals := base.globals
    administrativePrefix := 1
    solvedRequirements := caller.function.solvedRequirements
    internalReason := Word.ofNatModulo 0 }
  let mut direct := 0
  let mut reference := 0
  let mut inherited := 0
  for item in source.nodes do
    match item with
    | .expression node =>
      let relevant := match node.form with
        | .call _ [] (.declaration _) => true
        | .reference _ (.declaration _) => base.plan.referenceEdges.any (fun edge => decide (edge.caller = caller.key ∧ edge.occurrence = node.id))
        | _ => false
      if relevant then
        let output ← SourceCompilerFeatureSupport.get "actual outer evidence lowering"
          (SourceCoreEvidence.lowerWithProjector base.sourceProgram SourceCoreFunctionTypes.projectType caller context rejectChild
            100 source [] node.id (fun _ => Word.ofNatModulo 0))
        match output with
        | none => pure ()
        | some _ =>
          match node.form with
          | .call _ _ (.declaration instantiation) =>
            direct := direct + 1
            if instantiation.predicates.isEmpty && !caller.assumptions.isEmpty then inherited := inherited + 1
          | .reference _ (.declaration _) => reference := reference + 1
          | _ => throw (IO.userError "outer evidence audit changed branch")
    | _ => pure ()
  pure (direct, reference, inherited)

private def audit (entry : SourceCompilerFeatureSupport.Entry) : IO (Nat × Nat × Nat) := do
  let mut total := (0, 0, 0)
  for named in entry.cached.indexed.base.functions do
    let counts ← auditSource entry named.specialized named.specialized.function.typedBody
    total := (total.1 + counts.1, total.2.1 + counts.2.1, total.2.2 + counts.2.2)
  pure total

def run : IO Unit := do
  let program ← SourceCompilerFeatureSupport.get "outer call evidence checker" (checkProgram workspace)
  let direct ← SourceCompilerFeatureSupport.compileNamed program "direct"
  let directCounts ← audit direct
  SourceCompilerFeatureSupport.require (directCounts.1 > 0) "qualified direct branch disappeared"
  direct.checkResume [] (SourceCompilerFeatureSupport.scalar 4) 11
  let inherited ← SourceCompilerFeatureSupport.compileNamed program "inherited"
  let inheritedCounts ← audit inherited
  SourceCompilerFeatureSupport.require (inheritedCounts.2.2 > 0) "caller-only authentication did not run"
  inherited.checkResume [] (SourceCompilerFeatureSupport.scalar 5) 3
  let referenced ← SourceCompilerFeatureSupport.compileNamed program "referenced"
  let referenceCounts ← audit referenced
  SourceCompilerFeatureSupport.require (referenceCounts.2.1 > 0) "qualified reference branch disappeared"
  referenced.checkResume [] (SourceCompilerFeatureSupport.scalar 4) 19
  let localEntry ← SourceCompilerFeatureSupport.compileNamed program "local"
  let mut contextual := 0
  for binding in localEntry.cached.indexed.base.locals.bindings do
    for candidate in binding.instances do
      let parent ← SourceCompilerFeatureSupport.get "actual local preparation"
        (SourceCoreLocalEvidence.prepare program localEntry.cached.indexed.base.plan candidate)
      let counts ← auditSource localEntry parent.caller parent.source
      contextual := contextual + counts.1
  SourceCompilerFeatureSupport.require (contextual ≥ 2) "contextual lambda evidence branches disappeared"
  localEntry.checkResume [.bool true] (.product (SourceCompilerFeatureSupport.scalar 4) (SourceCompilerFeatureSupport.scalar 4)) 23
  let failed ← SourceCompilerFeatureSupport.compileNamed program "failed"
  let baseline ← failed.invoke []
  let (reason, session) ← match baseline.outcome with
    | .failed reason session => pure (reason, session)
    | _ => throw (IO.userError "outer call fixture did not reach later failure")
  let snapshot ← SourceCompilerFeatureSupport.get "outer evidence failure snapshot" (← session.snapshot 2048)
  for spent in [0, 17, 53] do
    let started ← SourceCompilerFeatureSupport.get "outer evidence suspension"
      (← baseline.initial.run baseline.key [] {SourceCompilerFeatureSupport.executionOptions with executionFuel := spent})
    let resumed ← match started with
      | .outOfFuel checkpoint => checkpoint.resume 300000 2048
      | done => pure done
    match resumed with
    | .failed actual session =>
      let observed ← SourceCompilerFeatureSupport.get "outer evidence resumed snapshot" (← session.snapshot 2048)
      SourceCompilerFeatureSupport.require (actual == reason && reprStr observed.cells == reprStr snapshot.cells)
        "outer selected call changed failure or store prefix on resume"
    | _ => throw (IO.userError "outer evidence resume changed outcome")
  IO.println "outer call evidence certificates: full selected metadata, ordered dictionaries, caller-only and contextual authentication, reference and failure/resume GREEN"

end Tests.SourceCoreCallableCallEvidenceCertificates
