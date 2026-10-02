import Solcore.SourceSemantics.CoreLowering.BuiltinImperativeMatchPreparedDiagnostics
import Solcore.Test.SourceCompilerFeatureSupport

/-! Actual prepared diagnostics across statement, initializer and post origins.
The public compiler consumer retains native/source static inputs and residual
fault interpretation; operand laws and the match ledger are constructed here. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 65536
namespace Tests.SourceCorePreparedMatchDiagnostics
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
section FixedFactory
open BuiltinImperativeMatch
section Certificates
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource}
  {readFuel : Nat} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {definitions : DataEnvironment} {administrative : Core.Context}
  {policy : SourceCoreLoops.Policy} {parentSite : SourceCoreElaboration.ErrorSite}
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Solcore.Syntax.ValueAssignOp → Word}
  {invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}

  {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
  {signatures : ProgramSignatures} {locals : SourceCoreLocalPolymorphism.Catalog}
  {parents : List SourceCoreLocalEvidence.Prepared} {assignmentsTable : SourceCoreAssignmentFaultSites.Table}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {compilation : SourceCoreFunctions.Context}
  {native : SourceCoreGeneralFunctions.CallableContext} {parent : Option SourceCoreLocalEvidence.Prepared}
  {skipInitializer : Option ExpressionId}

theorem accepted_prepared_factory {first : Nat}
    (prepared : SourceCoreAssignmentFaultSites.prepare source first = .ok assignmentsTable)
    (operandTyping : AssignmentDiagnosticOrigins.OperandsTyped source)
    (fixedPolicy : policy = SourceCoreCompatibleDataMatches.loopPolicy values compilation.solvedRequirements
      assignmentsTable diagnostics compilation.owner policy.lowerExpression
      (some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals (layouts.allocatorAt owner active onError)))
      (some definitions))
    (hidden : GenericImperativeMatch.MatchHiddenFresh source)
    (unique : NodeOccurrencesUnique source)
    (ordinary : CompatibleExpressionBuiltins.Ordinary source locals compilation.owner)
    (expressionPolicy : policy.lowerExpression = SourceCoreGeneralFunctions.lowerContextualExpression
      program representation signatures locals parents assignmentsTable diagnostics compilation (some native) parent skipInitializer)
    (expressionRead : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerRead : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (nativeTyping : ∀ sourceContext scope fuel id lowered,
      sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = false →
      sourceContext.signatures = values.checked.signatures →
      CompatibleExpressionReads.ScopeDeclarations source scope sourceContext →
      CompatibleExpressionBuiltins.Syntax source id → ∀ node,
      source.lookupExpression? id = some node → ExpressionHasType source sourceContext id node.type →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
      HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
        (LanguageResult.resultType lowered.type) definitions)
    {context : SourceSemantics.Context} {scope : Scope} {statements : List StatementId} {expected : TypeSystem.Ty}
    (syntaxTree : Syntax source context (.statements true statements) expected)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {fuel : Nat} {type nativeType : Ty} {code : Expr} {fellThrough escaped : Word}
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope statements type reasonAt fellThrough escaped = .ok code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType definitions) :
    ∃ flow,
      SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope statements type reasonAt true escaped = .ok flow ∧
      ∃ _extracted : ExtractionFor .reachable layouts owner active frame globals onError readFuel values source compilation.solvedRequirements reasonAt definitions administrative
        context scope (.statements true statements) expected type flow,
      code = LocalControl.finish type (LocalLoop.toControl type flow escaped)
        (if type = .unit then LanguageResult.success .unit else LanguageResult.failure type (.word fellThrough)) ∧
      ∀ registry faults, _extracted.diagnostics registry faults → ∀ evidence,
        CompatibleExpressionLiterals.ContextValid compilation.solvedRequirements context evidence →
        GenericImperativeMatch.Tree.ReachableReady registry faults _extracted.tree := by
  obtain ⟨flow, generated, extracted, same⟩ := extraction_of_prepared_contextual_body prepared operandTyping (fixedPolicy := fixedPolicy) (hidden := hidden) (unique := unique) (ordinary := ordinary) (expressionPolicy := expressionPolicy) (expressionRead := expressionRead) (lowerRead := lowerRead) (leafPolicy := leafPolicy) (nativeTyping := nativeTyping) (context := context) (scope := scope) (statements := statements) (expected := expected) (syntaxTree := syntaxTree) (closed := closed) (residual := residual) (sourceSignatures := sourceSignatures) (declarations := declarations) (fuel := fuel) (type := type) (nativeType := nativeType) (code := code) (fellThrough := fellThrough) (escaped := escaped) (projection := projection) (accepted := accepted) (nativeTyped := nativeTyped)
  exact ⟨flow, generated, extracted, same, fun registry faults interpreted evidence valid =>
    extracted.ready interpreted valid sourceSignatures⟩
end Certificates
end FixedFactory
section Origins
open AssignmentDiagnosticOrigins
variable {source : TypedSource} {context : SourceSemantics.Context}
  {assignment : AssignmentResolution} {operator : Solcore.Syntax.ValueAssignOp} {rhs : ExpressionId}

theorem compound_raw_word (different : operator ≠ .equal)
    (typed : SourceAssignmentHasType source context assignment operator rhs) : assignment.target.type = .word := by
  cases typed with
  | equal => exact (different rfl).elim
  | wordCompound _ target _ _ => cases target with | intro _ _ same => exact same

/-- A normalized alias cannot silently satisfy the actual table guard. -/
theorem comptime_word_not_compound (different : operator ≠ .equal)
    (raw : assignment.target.type = .comptime .word) :
    ¬ SourceAssignmentHasType source context assignment operator rhs := by
  intro typed
  have same := compound_raw_word different typed
  rw [raw] at same
  cases same

theorem initializer_suffix_origin {id : StatementId} {node : StatementNode}
    {beforeItems rest post : List ForItemForm} {condition : ExpressionId} {body : List StatementId}
    (found : source.lookupStatement? id = some node)
    (form : node.form = .forLoop (beforeItems ++ .assignValue assignment operator rhs :: rest) condition post body) :
    Occurs source (.occurrence id.occurrence) assignment operator rhs := by
  have origin : ForOriginFor true source (.occurrence id.occurrence)
      (.assignValue assignment operator rhs :: rest) condition post body :=
    ⟨id, node, _, found, form, rfl, beforeItems, rfl⟩
  exact origin.header.operand

theorem post_suffix_origin {id : StatementId} {node : StatementNode}
    {beforeItems rest initial : List ForItemForm} {condition : ExpressionId} {body : List StatementId}
    (found : source.lookupStatement? id = some node)
    (form : node.form = .forLoop initial condition (beforeItems ++ .assignValue assignment operator rhs :: rest) body) :
    Occurs source (.occurrence id.occurrence) assignment operator rhs := by
  have origin : HeaderOriginFor true source (.occurrence id.occurrence)
      (.assignValue assignment operator rhs :: rest) :=
    .inr ⟨id, node, initial, condition, _, body, found, form, rfl, beforeItems, rfl⟩
  exact origin.operand

/-- The concrete prepared factory consumes only the remaining local laws. -/
theorem prepared_head_errors
    {values : SourceCoreCompatibleValues.Context} {certificate : GenericExpressionMeaning.Certificate}
    {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context} {definitions : DataEnvironment}
    (head : GenericAssignmentStatements.Head values source context certificate scope administrative definitions assignment operator rhs)
    {site : Site} {first : Nat} {table : SourceCoreAssignmentFaultSites.Table}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (origin : Occurs source site assignment operator rhs)
    (typed : OperandsTyped source) (prepared : SourceCoreAssignmentFaultSites.prepare source first = .ok table)
    (sameToken : head.invalid = GenericAssignmentDiagnostics.token table site assignment.target.root operator)
    (remaining : Residual head table registry faults) :
    head.ReachableErrors registry faults :=
  (Factory.prepared typed prepared).materialize head site origin sameToken registry faults remaining

end Origins

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function headers(seed: Word) returns (Word) { let out = seed; for (out += 1, out += 2; out < 9; out += 1) { match (out) { case 6 { continue; } default { if (out == 7) { break; } } } } return out; }",
    "function equalHeaders(seed: Word) returns (Word) { let out = seed; for (out = seed; out < seed + 2; out = out + 1) { match(out) { case x {} default {} } } return out; }",
    "function initialFault(seed: Word) returns (Word) { let root: Word; let seen: mapping(Bool => Word); for (root += seen[false]; false; root += seed) {} return root; }",
    "function postFault(seed: Word) returns (Word) { let root: Word; let seen: mapping(Bool => Word); for (let i = 0; i < 1; root += seen[false]) { match (seed) { case x {} default {} } } return root; }"
  ]}]
}

open Tests.SourceCompilerFeatureSupport in
private def sourceFor (entry : Entry) : IO TypedSource := do
  pure (← get "actual source" (SourceCompilationPlan.exactSpecialization entry.cached.validationPlan entry.key)).function.typedBody

open Tests.SourceCompilerFeatureSupport in
private def stable (entry : Entry) : IO Unit := do
  let complete ← entry.audit [scalar 1]
  let invocation ← entry.invoke [scalar 1]
  for fuel in [0, 7, 43] do
    let started ← entry.audit [scalar 1] fuel
    let resumed ← get "native prepared-match resume" (started.resume 300000)
    require ((← nativeObservation complete) == (← nativeObservation resumed))
      "prepared-match resume changed exact native result/store"
    let pending ← entry.invoke [scalar 1] {executionOptions with executionFuel := fuel}
    let terminal ← match pending.outcome with
      | .outOfFuel checkpoint => checkpoint.resume 300000 2048
      | done => pure done
    match invocation.outcome, terminal with
    | .succeeded expected, .succeeded actual => require (actual.value == expected.value) "prepared resume changed value"
    | .failed expected _, .failed actual session =>
      require (actual == expected) "prepared resume changed token"
      require (decide ((← get "resumed diagnostic" (session.diagnostic entry.key actual)) = (← invocation.diagnostic expected)))
        "prepared resume changed diagnostic"
    | _, _ => throw (IO.userError "prepared resume changed completion status")

open Tests.SourceCompilerFeatureSupport in
def run : IO Unit := do
  let program ← get "prepared-match fixtures" (checkProgram workspace)
  for (name, expected) in [("headers", 7), ("equalHeaders", 3)] do
    let entry ← compileNamed program name
    let source ← sourceFor entry
    let table ← get "actual operand prepare" (SourceCoreAssignmentFaultSites.prepare source 100)
    if name == "equalHeaders" then
      require table.sites.isEmpty "equal header/post allocated an unreachable operand token"
    else
      let node ← match source.nodes.findSome? fun
          | .statement node => match node.form with | .forLoop _ _ _ _ => some node | _ => none
          | _ => none with
        | some node => pure node | none => throw (IO.userError "parent for statement absent")
      require (table.sites.length == 1 && table.sites.all fun site => decide
        (site.site = .occurrence node.id.occurrence ∧ site.span = node.span ∧ site.kind = .value .add ∧ site.rhsType = .word))
        "initializer/post duplicate did not retain the same parent diagnostic"
    require ((← entry.run [scalar 1]) == scalar expected) "prepared for/match control changed"
    stable entry
  for name in ["initialFault", "postFault"] do
    let entry ← compileNamed program name
    let source ← sourceFor entry
    let table ← get "actual fault table" (SourceCoreAssignmentFaultSites.prepare source 100)
    let node ← match source.nodes.findSome? fun
        | .statement node => match node.form with | .forLoop _ _ _ _ => some node | _ => none
        | _ => none with
      | some node => pure node | none => throw (IO.userError "fault parent for absent")
    require (table.sites.length == 1 && table.sites.all fun site => decide
      (site.site = .occurrence node.id.occurrence ∧ site.kind = .value .add ∧ site.rhsType = .word))
      "fault diagnostic lost the authentic parent site"
    let result ← entry.invoke [scalar 1]
    match result.outcome with
    | .failed reason _ =>
      require (decide ((← result.diagnostic reason) = some {
        error := .invalidAssignmentOperands .add none (some .word),
        site := .occurrence node.id.occurrence, span := some node.span}))
        "header operand failure lost exact source diagnostic"
    | _ => throw (IO.userError "header operand failure did not stop")
    if name == "initialFault" then
      entry.checkCells [scalar 1] [(.word, some (scalar 1)), (.word, none),
        (.mapping .bool .word, some (.mapping .bool .word []))]
    stable entry
  IO.println "prepared match diagnostics: actual parent/suffix, header/post dedup, raw source typing, empty equal table, effects and resume GREEN"

end Tests.SourceCorePreparedMatchDiagnostics
