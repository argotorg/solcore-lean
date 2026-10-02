import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaScalarNativeTyping
import Solcore.Test.SourceCompilerFeatureSupport

/-! The consumer creates Code and real named history without a Code or native
HasType premise. Static scalar syntax/typing and exact callback equations remain
visible. IO checks heterogeneous packed parameters, lexical captures, lazy faults
and suspension on the actual indexed execution path. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreCallableIndexedLambdaScalarNativeTyping
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CallableIndexedParameterNativeTyping CallableIndexedLambdaCertificates
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration CallableIndexedLambdaScalarNativeTyping

theorem accepted_scalar_generation {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked)
    {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    (compiled : Compilation prepared named diagnostics namedCode)
    (record : SourceCompilationPlan.exactSpecialization prepared.base.plan named.signature.key = .ok named.specialized)
    {fuel : Nat} {view : TypedSource} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {id : ExpressionId} {sourceNode node : ExpressionNode} {parameters : List TypedBinder}
    {result : TypeSystem.Ty} {body : List StatementId} {reported : Ty}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (sourceContext : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) (captured : Dynamic.Environment)
    (profile : checked.catalog.callableContracts = true)
    (viewOfSource : LambdaMetadataViews.MetadataView (source named) view)
    (sourceFound : (source named).lookupExpression? id = some sourceNode)
    (sourceForm : sourceNode.form = .lambda parameters result body)
    (found : view.lookupExpression? id = some node) (form : node.form = sourceNode.form)
    (owner : id.occurrence.owner = view.owner)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : prepared.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context prepared named).owner ∧ binding.initializer = id)) = none)
    (read : SourceCoreCompatibleDataExpressions.readExpression checked view id = .ok (node, reported))
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression prepared.base.sourceProgram
      ((representation prepared).atContext named.signature.key []) prepared.base.sourceProgram.signatures
      prepared.base.locals compiled.parents compiled.own.assignments diagnostics (context prepared named)
      prepared.base.callableContext none none (fuel + 1) view scope id reasonAt = .ok lowered)
    {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
    (receipt : Certificate policy lowerBody fuel (context prepared named) view scope id node
      parameters result body reported reasonAt lowered)
    (values : SourceCoreCompatibleValues.Context) (sameChecked : values.checked = checked)
    (scalar : ScalarBody values sameChecked receipt)
    (projector : policy.projectType = SourceCoreCompatibleDataExpressions.projectType checked)
    (allocation : policy.sourceCells = some (allocator prepared named))
    (manifest : policy.rawLambdaBody = SourceCoreLambdaTemplates.hook prepared.ancestry.templates named.signature.key [])
    (expressionHook : policy.rawLambdaExpression = SourceCoreCallableIndexedAncestry.expressionHook prepared.ancestry named.signature.key [])
    (callables : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some prepared.ancestry.graph.inputs.callable) [])
    (binderPolicy : policy.lowerBinder = SourceCoreGeneralFunctions.contextualBinder
      (representation prepared) prepared.base.locals named.signature.key [])
    (monomorphic : ∀ binder ∈ parameters, binder.scheme.quantified = [])
    (ordinaryParameters : ∀ binder ∈ parameters, view.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (scopeWF : ∀ binding : Resolved.LocalId × Ty, binding ∈ scope → binding.2.WellFormed checked.catalog.definitions)
    (current : (SourceCoreLocalCell.coreContext scope ++ administrative)[scope.length + 1 + prepared.base.globals.length]? =
      some (.cell prepared.ancestry.layout.frame.type)) :
    ∃ site : Site prepared named parameters result body sourceContext evidence captured scope administrative,
      site.code.id = id ∧ site.code.lowered = lowered ∧
      ∃ history : CallableIndexedLambdaValues.History site.code,
        history.metadata = state named ∧ history.metadata.metadata.source = source named ∧
        history.metadata.metadata.owner = named.signature.key ∧ history.metadata.nativeActive = [] := by
  obtain ⟨site, sameId, sameCode⟩ := CallableIndexedLambdaScalarNativeTyping.of_contextual prepared compiled record
    sourceContext evidence captured profile viewOfSource sourceFound sourceForm found form owner requirements coercions
    ordinary read accepted receipt values sameChecked scalar projector allocation manifest expressionHook callables binderPolicy
    monomorphic ordinaryParameters scopeWF current
  obtain ⟨_, _, history, _, _, sameState⟩ := site.history compiled record
  refine ⟨site, sameId, sameCode, history, sameState, ?_, ?_, ?_⟩ <;> rw [sameState] <;> rfl

/-- The third heterogeneous argument uses two right projections, preserving
actual packed order instead of assigning each parameter the bundle type. -/
theorem third_projection (definitions : DataEnvironment) (administrative : Core.Context) :
    HasType (.product .word (.product .bool .integer) :: administrative)
      (SourceCoreFunctions.argumentProjection 2 3 (.var 0)) .integer definitions :=
  projection_typed (types := [.word, .bool, .integer]) rfl (.var rfl)

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function make(seed: Word) returns (function(Word, Bool) returns (Word)) { let unused: Bool = true; return lam(item: Word, choose: Bool) -> Word { return choose ? seed + item : item; }; }",
    "function single(seed: Word) returns (function(Word) returns (Word)) { return lam(item: Word) -> Word { return seed + item; }; }",
    "function pair(seed: Word) returns (function(Bool, Word) returns ((Bool, Word))) { return lam(flag: Bool, item: Word) -> (Bool, Word) { return (flag, seed + item); }; }",
    "function zero(seed: Word) returns (function() returns (Word)) { return lam() -> Word { return seed; }; }",
    "function three(seed: Word) returns (function(Word, Bool, Word) returns (Word)) { return lam(first: Word, branch: Bool, last: Word) -> Word { return branch ? seed + first : last; }; }",
    "function failed(seed: Word) returns (function(Bool) returns (Word)) { let missing: Word; return lam(flag: Bool) -> Word { return flag ? seed : missing; }; }"
  ]}] }

private def exercise (program : CheckedProgram) (name : String)
    (argument expected : SourceCoreExecution.Value) : IO Unit := do
  let entry ← SourceCompilerFeatureSupport.compileNamed program name
  let created ← entry.invoke [SourceCompilerFeatureSupport.scalar 7]
  let done ← match created.outcome with
    | .succeeded done => pure done
    | _ => throw (IO.userError s!"{name}: lambda formation failed")
  let handle ← match done.value with
    | .function handle => pure handle
    | _ => throw (IO.userError s!"{name}: lambda handle missing")
  let complete ← SourceCompilerFeatureSupport.get "scalar lambda invoke"
    (← done.session.invokePacked handle argument SourceCompilerFeatureSupport.executionOptions)
  let final ← match complete with
    | .succeeded final => pure final
    | _ => throw (IO.userError s!"{name}: scalar invocation failed")
  SourceCompilerFeatureSupport.require (final.value == expected) s!"{name}: parameter order or capture changed"
  let baseline ← SourceCompilerFeatureSupport.get "scalar final snapshot" (← final.session.snapshot 2048)
  for spent in [0, 7, 43] do
    let started ← SourceCompilerFeatureSupport.get "scalar pending invocation"
      (← done.session.invokePacked handle argument {SourceCompilerFeatureSupport.executionOptions with executionFuel := spent})
    let resumed ← match started with
      | .outOfFuel pending => pending.resume 300000 2048
      | complete => pure complete
    match resumed with
    | .succeeded actual =>
      let observed ← SourceCompilerFeatureSupport.get "scalar resumed snapshot" (← actual.session.snapshot 2048)
      SourceCompilerFeatureSupport.require (actual.value == expected && reprStr observed.cells == reprStr baseline.cells)
        s!"{name}: resume changed parameter allocation or captured state"
    | _ => throw (IO.userError s!"{name}: scalar resume failed")

private def failure (program : CheckedProgram) : IO Unit := do
  let entry ← SourceCompilerFeatureSupport.compileNamed program "failed"
  let created ← entry.invoke [SourceCompilerFeatureSupport.scalar 7]
  let done ← match created.outcome with
    | .succeeded done => pure done
    | _ => throw (IO.userError "fault lambda formation failed")
  let handle ← match done.value with
    | .function handle => pure handle
    | _ => throw (IO.userError "fault lambda handle missing")
  let complete ← SourceCompilerFeatureSupport.get "scalar lambda fault"
    (← done.session.invokePacked handle (.bool false) SourceCompilerFeatureSupport.executionOptions)
  let (reason, session) ← match complete with
    | .failed reason session => pure (reason, session)
    | _ => throw (IO.userError "selected missing capture did not fail")
  let baseline ← SourceCompilerFeatureSupport.get "fault snapshot" (← session.snapshot 2048)
  for spent in [0, 11, 59] do
    let started ← SourceCompilerFeatureSupport.get "scalar pending fault"
      (← done.session.invokePacked handle (.bool false) {SourceCompilerFeatureSupport.executionOptions with executionFuel := spent})
    let resumed ← match started with
      | .outOfFuel pending => pending.resume 300000 2048
      | complete => pure complete
    match resumed with
    | .failed actual session =>
      let observed ← SourceCompilerFeatureSupport.get "fault resumed snapshot" (← session.snapshot 2048)
      SourceCompilerFeatureSupport.require (actual == reason && reprStr observed.cells == reprStr baseline.cells)
        "scalar lambda fault/resume changed first failure or allocation prefix"
    | _ => throw (IO.userError "scalar lambda fault/resume changed outcome")

def run : IO Unit := do
  let program ← SourceCompilerFeatureSupport.get "scalar lambda checker" (checkProgram workspace)
  let w := SourceCompilerFeatureSupport.scalar
  exercise program "make" (.product (w 4) (.bool true)) (w 11)
  exercise program "make" (.product (w 4) (.bool false)) (w 4)
  exercise program "single" (w 4) (w 11)
  exercise program "pair" (.product (.bool true) (w 4)) (.product (.bool true) (w 11))
  exercise program "zero" .unit (w 7)
  exercise program "three" (.product (w 4) (.product (.bool false) (w 29))) (w 29)
  exercise program "failed" (.bool true) (w 7)
  failure program
  IO.println "indexed scalar lambda native typing: actual parameter fold, captures, lazy branch/fault and resume GREEN"

end Tests.SourceCoreCallableIndexedLambdaScalarNativeTyping
