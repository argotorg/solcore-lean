import Solcore.SourceSemantics.CoreLowering.GenericImperativeForCertificates
import Solcore.SourceSemantics.CoreLowering.NamedForFunctionBodyMeaning
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogProfiles
import Solcore.Test.SourceCompilerFeatureSupport

/-! Actual prepared operand laws follow the existing for traversal into named
body and recursive catalog receipts. Source syntax/typing, child certificates,
native typing and non-operand fault interpretation remain explicit. No match
Tree is cast into the for grammar and no recursive callee meaning is assumed. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 65536
namespace Tests.SourceCorePreparedForDiagnostics
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CallableAncestryPairedLookup CompatiblePayload GenericImperativeFor
section Named
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {bodies : NamedCallExpressions.Bodies prepared values ambient.definitions program}
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {compilation : SourceCoreFunctions.Context} {expressionFuel : Nat}
  {source : TypedSource} {expressionSyntax : ExpressionId → Prop} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {administrative : Core.Context} {policy : SourceCoreLoops.Policy}
theorem prepared_named_body {first : Nat} {table : SourceCoreAssignmentFaultSites.Table}
    (tablePrepared : SourceCoreAssignmentFaultSites.prepare source first = .ok table)
    (operandsTyped : AssignmentDiagnosticOrigins.OperandsTyped source)
    {ledger : List SolvedRequirement} {policyOwner : SourceSpecialization.SpecializationKey}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program}
    (fixedPolicy : policy = SourceCoreCompatibleDataMatches.loopPolicy values ledger table diagnostics policyOwner policy.lowerExpression
      (some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals (layouts.allocatorAt owner active onError)))
      (some ambient.definitions))
    (expressions : ∀ sourceContext, sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = false →
      sourceContext.signatures = values.checked.signatures →
      ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations source scope sourceContext → expressionSyntax id →
      source.lookupExpression? id = some node → ExpressionHasType source sourceContext id node.type →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
      (fun context => NamedCallExpressions.Tree bodies compilation expressionFuel source context solved reasonAt) sourceContext scope id lowered)
    (unique : NodeOccurrencesUnique source)
    (assignmentExpressions : ∀ sourceContext scope fuel id lowered,
      sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = false →
      sourceContext.signatures = values.checked.signatures →
      CompatibleExpressionReads.ScopeDeclarations source scope sourceContext →
      expressionSyntax id → ∀ node, source.lookupExpression? id = some node →
      ExpressionHasType source sourceContext id node.type →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
        (fun context => NamedCallExpressions.Tree bodies compilation expressionFuel source context solved reasonAt) sourceContext scope id lowered ∧
        HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
          (LanguageResult.resultType lowered.type) ambient.definitions)
    {context : SourceSemantics.Context} {scope : Scope} {statements : List StatementId} {expected : TypeSystem.Ty}
    (syntaxTree : Syntax source expressionSyntax context (.statements true statements) expected)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {fuel : Nat} {type nativeType : Ty} {code : Expr} {fellThrough escaped : Word}
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope statements type reasonAt fellThrough escaped = .ok code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType ambient.definitions) :
    ∃ flow,
      SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope statements type reasonAt true escaped = .ok flow ∧
      ∃ _extracted : DiagnosticExtraction .reachable layouts owner active frame globals onError values source expressionSyntax (fun context => NamedCallExpressions.Tree bodies compilation expressionFuel source context solved reasonAt) ambient.definitions administrative
        context scope (.statements true statements) expected type flow,
      code = LocalControl.finish type (LocalLoop.toControl type flow escaped)
        (if type = .unit then LanguageResult.success .unit else LanguageResult.failure type (.word fellThrough)) ∧
      ∀ registry faults, _extracted.diagnostics registry faults →
        Nonempty (NamedForFunctionBody.CertificateFor .reachable bodies layouts owner active frame globals onError compilation expressionFuel
          source expressionSyntax context solved reasonAt administrative registry faults scope statements expected type policy fuel fellThrough escaped code) := by
  obtain ⟨flow, generated, extracted, same⟩ := extraction_of_prepared_policy_body tablePrepared operandsTyped fixedPolicy expressions unique assignmentExpressions syntaxTree closed residual sourceSignatures declarations projection accepted nativeTyped
  exact ⟨flow, generated, extracted, same, fun registry faults interpreted =>
    ⟨extracted.named_body accepted projection generated interpreted⟩⟩
end Named

section Catalog
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {headers : RecursiveNamedCatalog.Inventory prepared values ambient.definitions program}
  {header : RecursiveNamedCatalog.Header prepared values ambient.definitions program}
  {compilation : SourceCoreFunctions.Context} {expressionFuel : Nat}
  {expressionSyntax : ExpressionId → Prop} {administrative : Core.Context}
theorem prepared_catalog_profile {first : Nat} {table : SourceCoreAssignmentFaultSites.Table}
    (initialValid : CompatibleExpressionLiterals.ContextValid header.solved header.context header.function.evidence)
    (tablePrepared : SourceCoreAssignmentFaultSites.prepare header.function.source first = .ok table)
    (operandsTyped : AssignmentDiagnosticOrigins.OperandsTyped header.function.source)
    {ledger : List SolvedRequirement} {policyOwner : SourceSpecialization.SpecializationKey}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program}
    (fixedPolicy : header.policy = SourceCoreCompatibleDataMatches.loopPolicy values ledger table diagnostics policyOwner header.policy.lowerExpression
      (some (SourceCoreCallableIndexedAllocationFrames.allocator prepared.layout.frame header.globals (header.layouts.allocatorAt header.owner header.active header.onError)))
      (some ambient.definitions))
    (expressions : ∀ sourceContext, sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = false →
      sourceContext.signatures = values.checked.signatures →
      ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations header.function.source scope sourceContext → expressionSyntax id →
      header.function.source.lookupExpression? id = some node → ExpressionHasType header.function.source sourceContext id node.type →
      header.policy.lowerExpression fuel header.function.source scope id header.reasonAt = .ok lowered →
      (fun context => RecursiveNamedCatalog.Expressions headers compilation expressionFuel header.function.source context header.solved header.reasonAt) sourceContext scope id lowered)
    (unique : NodeOccurrencesUnique header.function.source)
    (assignmentExpressions : ∀ sourceContext scope fuel id lowered,
      sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = false →
      sourceContext.signatures = values.checked.signatures →
      CompatibleExpressionReads.ScopeDeclarations header.function.source scope sourceContext →
      expressionSyntax id → ∀ node, header.function.source.lookupExpression? id = some node →
      ExpressionHasType header.function.source sourceContext id node.type →
      header.policy.lowerExpression fuel header.function.source scope id header.reasonAt = .ok lowered →
        (fun context => RecursiveNamedCatalog.Expressions headers compilation expressionFuel header.function.source context header.solved header.reasonAt) sourceContext scope id lowered ∧
        HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
          (LanguageResult.resultType lowered.type) ambient.definitions)
    (syntaxTree : Syntax header.function.source expressionSyntax header.context (.statements true header.function.body) header.function.resultType)
    (closed : header.context.typeVariables = []) (residual : header.context.residualTypeVariables = false)
    (sourceSignatures : header.context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations header.function.source (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.context)
    {nativeType : Ty}
    (projection : values.checked.catalog.project header.function.resultType = .ok header.output)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy header.policy header.fuel header.function.source (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body header.output header.reasonAt header.fellThrough header.escaped = .ok header.body)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) ++ administrative) header.body nativeType ambient.definitions) :
    ∃ flow,
      SourceCoreLoops.lowerFlowStatementsWithPolicy header.policy header.fuel header.function.source (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body header.output header.reasonAt true header.escaped = .ok flow ∧
      ∃ _extracted : DiagnosticExtraction .reachable header.layouts header.owner header.active prepared.layout.frame header.globals header.onError values header.function.source expressionSyntax (fun context => RecursiveNamedCatalog.Expressions headers compilation expressionFuel header.function.source context header.solved header.reasonAt) ambient.definitions administrative
        header.context (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) (.statements true header.function.body) header.function.resultType header.output flow,
      header.body = LocalControl.finish header.output (LocalLoop.toControl header.output flow header.escaped)
        (if header.output = .unit then LanguageResult.success .unit else LanguageResult.failure header.output (.word header.fellThrough)) ∧
      ∀ registry faults, _extracted.diagnostics registry faults →
        Nonempty (RecursiveNamedCatalog.ProfileFor .reachable headers header compilation expressionFuel expressionSyntax administrative registry faults) := by
  obtain ⟨flow, generated, extracted, same⟩ := extraction_of_prepared_policy_body tablePrepared operandsTyped fixedPolicy expressions unique assignmentExpressions syntaxTree closed residual sourceSignatures declarations projection accepted nativeTyped
  exact ⟨flow, generated, extracted, same, fun registry faults interpreted =>
    ⟨extracted.catalog_profile initialValid accepted projection generated interpreted⟩⟩
end Catalog

open NamedForFunctionBody GeneralHeap ReadOnly CoreProof
section CompilerConsumers
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base}
  {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {bodies : NamedCallExpressions.Bodies prepared values ambient.definitions program}
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {compilation : SourceCoreFunctions.Context} {expressionFuel : Nat}
  {function : Dynamic.Closure} {expressionSyntax : ExpressionId → Prop} {context : SourceSemantics.Context} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope} {type : Ty}
  {administrative : Core.Context}
  {policy : SourceCoreLoops.Policy} {fuel : Nat} {fellThrough escaped : Word} {code : Expr}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (definitions : layouts.definitions = ambient.definitions)
  (registered : frameLayout.Registered ambient.definitions)
  (contextValid : CompatibleExpressionLiterals.ContextValid solved context function.evidence)
  (unique : NodeOccurrencesUnique function.source)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup) {faults : FunctionCalls.FaultRep}
  (escapedFault : faults .controlEscapedFunction escaped)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

  (bodyUninitialized : ∀ body, body ∈ bodies → ∀ id location,
    faults (.uninitializedLocation location) (body.reasonAt id))
  (bodyMissing : ∀ body, body ∈ bodies → ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((body.reasonAt id).add tag))
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)

include definitions registered escapedFault extension faithful functionLeaves functionTypes contextValid unique owners uninitialized missing bodyUninitialized bodyMissing in
theorem extracted_named_finite_iff
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel function.source scope
      function.body type reasonAt fellThrough escaped = .ok code)
    (projection : values.checked.catalog.project function.resultType = .ok type)
    {flow : Expr}
    (generated : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel function.source scope
      function.body type reasonAt true escaped = .ok flow)
    (extracted : GenericImperativeFor.DiagnosticExtraction .reachable layouts owner active frameLayout globals onError values
      function.source expressionSyntax
      (fun nextContext => NamedCallExpressions.Tree bodies compilation expressionFuel function.source nextContext solved reasonAt)
      ambient.definitions administrative context scope (.statements true function.body) function.resultType type flow)
    (interpreted : extracted.diagnostics registry faults)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store : Store} {ξ : Renaming}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : SourceCoreCallableIndexedFrames.Frame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping)
    (installed : NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix
      scope mapping world before store canonical)
:
    (∃ runtimeFuel value finalStore,
      Core.runStateful runtimeFuel (.initial (code.rename ξ) actual store) =
        .done value finalStore) ↔
    (∃ outcome after,
      FunctionCallBody.Trace program function context environment before outcome after) := by
  let certificate := extracted.named_body accepted projection generated interpreted
  exact certificate.finite_iff functions extension definitions registered
    contextValid unique owners escapedFault uninitialized missing bodyUninitialized bodyMissing faithful functionLeaves functionTypes
    environments heaps locals agrees actualTyped reference read unmapped installed
end CompilerConsumers

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function compound(seed: Word) returns (Word) { let result = seed; for (result += 1, result += 2; result < 9; result += 1) { if (result == 6) { continue; } if (result == 7) { break; } } return result; }",
    "function next(value: Word) returns (Word) { return value + 1; }",
    "function less(value: Word, bound: Word) returns (Bool) { return value < bound; }",
    "function bad() returns (Word) { let absent: Word; return absent; }",
    "function equalBody(seed: Word) returns (Word) { let result = seed; for (result = next(seed); less(result, 5); result = next(result)) { let inner = 0; while (less(inner, 2)) { inner = next(inner); } if (result == 3) { continue; } if (result == 4) { break; } } return result; }",
    "function unitBody(seed: Word) { let result = seed; for (result = next(seed); less(result, 3); result = next(result)) { } }",
    "function initialFault(seed: Word) returns (Word) { let result = seed; for (result = bad(); false; result = next(result)) { result = next(result); } return result; }",
    "function postFault(seed: Word) returns (Word) { let result = seed; for (result = next(seed); true; result = bad()) { result = next(result); } return result; }",
    "function bodyFault(seed: Word) returns (Word) { let result = seed; let seen: mapping(Bool => Word); for (result = next(seed); true; result = next(result)) { seen[false] = next(result); result = bad(); } return result; }",
    "function self(n: Word) returns (Word) { let result = 1; for (let i = 0; i < n; i = next(i)) { result = result + self(n - 1); } return result; }"
  ]}]
}
open Tests.SourceCompilerFeatureSupport in
private def verify_resume (entry : Entry) : IO Unit := do
  let baseline ← entry.audit [scalar 1]
  let invocation ← entry.invoke [scalar 1]
  for fuel in [0, 7, 43, 199] do
    let suspended ← entry.audit [scalar 1] fuel
    let resumed ← get "reachable body native resume" (suspended.resume 300000)
    require ((← nativeObservation resumed) == (← nativeObservation baseline))
      "reachable body resume changed native result/store"
    let pending ← entry.invoke [scalar 1] {executionOptions with executionFuel := fuel}
    let terminal ← match pending.outcome with
      | .outOfFuel checkpoint => checkpoint.resume 300000 2048
      | done => pure done
    match invocation.outcome, terminal with
    | .succeeded expected, .succeeded actual =>
      require (actual.value == expected.value) "reachable body resume changed result"
    | .failed expected _, .failed actual session =>
      require (actual == expected) "reachable body resume changed fault token"
      require (decide ((← get "resumed diagnostic" (session.diagnostic entry.key actual)) = (← invocation.diagnostic expected)))
        "reachable body resume changed exact diagnostic"
    | _, _ => throw (IO.userError "reachable body resume changed completion")

open Tests.SourceCompilerFeatureSupport in
def run : IO Unit := do
  let checked ← get "reachable named body checker" (checkProgram workspace)
  let compound ← compileNamed checked "compound"
  let source := (← get "compound actual source" (SourceCompilationPlan.exactSpecialization compound.cached.validationPlan compound.key)).function.typedBody
  let table ← get "compound actual prepare" (SourceCoreAssignmentFaultSites.prepare source 100)
  let node ← match source.nodes.findSome? fun
      | .statement node => match node.form with | .forLoop _ _ _ _ => some node | _ => none
      | _ => none with
    | some node => pure node
    | none => throw (IO.userError "compound parent for absent")
  require (table.sites.length == 1 && table.sites.all fun site => decide
    (site.site = .occurrence node.id.occurrence ∧ site.span = node.span ∧ site.kind = .value .add ∧ site.rhsType = .word))
    "parent initializer/post duplicate did not preserve first diagnostic metadata"
  require ((← compound.run [scalar 1]) == scalar 7) "compound parent loop changed"
  verify_resume compound
  for name in ["equalBody", "unitBody", "initialFault", "postFault", "bodyFault", "self"] do
    let entry ← compileNamed checked name
    let item ← get "reachable named source" (SourceCompilationPlan.exactSpecialization entry.cached.validationPlan entry.key)
    let table ← get "equal-only body table" (SourceCoreAssignmentFaultSites.prepare item.function.typedBody Core.wordModulus)
    require table.sites.isEmpty "equal-only named body requested an unreachable operand token"
    require (table.diagnostic? Word.zero == none) "empty named body table decoded a token"
    verify_resume entry
    let result ← entry.invoke [scalar 1]
    match name, result.outcome with
    | "equalBody", .succeeded completed => require (completed.value == scalar 4) "nested named loop result changed"
    | "unitBody", .succeeded completed => require (completed.value == .unit) "named Unit finish changed"
    | "self", .succeeded completed => require (completed.value == scalar 2) "recursive runtime smoke result changed"
    | _, .failed token _ =>
      require (← result.diagnostic token).isSome "named RHS fault lost its diagnostic"
      let audited ← entry.audit [scalar 1]
      let heap := (sourceState audited).heap
      let expected := if name == "initialFault" then 1 else if name == "postFault" then 3 else 2
      let raw ← get "reachable body expected write" (rawData 128 (scalar expected))
      require (reprStr heap[1]? == reprStr (some (SourceTypedRuntime.Cell.mk .word (some raw))))
        "initializer/body/post fault changed prior writes"
      if name == "bodyFault" then
        let rawMapping ← get "reachable body expected mapping write" (rawData 128
          (.mapping .bool .word [(.bool false, scalar 3)]))
        require (reprStr heap[2]? == reprStr (some (SourceTypedRuntime.Cell.mk (.mapping .bool .word) (some rawMapping))))
          "named RHS fault discarded a completed mapping write"
    | _, _ => throw (IO.userError "unexpected reachable named body completion")
  IO.println "prepared for diagnostics: actual parent origins, same for grammar to named/static catalog receipts, empty equal table, named faults/writes/resume GREEN"
end Tests.SourceCorePreparedForDiagnostics
