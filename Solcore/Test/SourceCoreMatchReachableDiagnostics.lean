import Solcore.SourceSemantics.CoreLowering.BuiltinImperativeMatchExtraction
import Solcore.SourceSemantics.CoreLowering.BuiltinImperativeMatchBodyMeaning
import Solcore.SourceSemantics.CoreLowering.GenericAssignmentDiagnosticCertificates
import Solcore.Test.SourceCompilerFeatureSupport

/-! The single match traversal preserves the selected diagnostic policy through
ordered child requests, header/post receipts and the actual function finish.
Concrete builtin Trees discharge child semantics. Equal has no operand token;
raw diagnostics interpretation and source/native static receipts remain explicit.
Named catalog profiles and preparation-to-whole-Tree laws are separate boundaries. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreMatchReachableDiagnostics
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof
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

theorem accepted_fixed_factory
    (fixedPolicy : policy = SourceCoreCompatibleDataMatches.loopPolicy values compilation.solvedRequirements
      assignmentsTable diagnostics compilation.owner policy.lowerExpression
      (some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals (layouts.allocatorAt owner active onError)))
      (some definitions))
    (hidden : GenericImperativeMatch.MatchHiddenFresh source)
    (assignments : CompatibleAssignmentStatements.AssignmentPolicy policy values invalidProjection invalidOperand missingDefault)
    (unaryPolicy : CompatibleBitNotStatements.Policy policy values invalidProjection invalidUnary missingDefault)
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
  obtain ⟨flow, generated, extracted, same⟩ := extraction_of_fixed_contextual_body_for .reachable (fixedPolicy := fixedPolicy) (hidden := hidden) (assignments := assignments) (unaryPolicy := unaryPolicy) (unique := unique) (ordinary := ordinary) (expressionPolicy := expressionPolicy) (expressionRead := expressionRead) (lowerRead := lowerRead) (leafPolicy := leafPolicy) (nativeTyping := nativeTyping) (context := context) (scope := scope) (statements := statements) (expected := expected) (syntaxTree := syntaxTree) (closed := closed) (residual := residual) (sourceSignatures := sourceSignatures) (declarations := declarations) (fuel := fuel) (type := type) (nativeType := nativeType) (code := code) (fellThrough := fellThrough) (escaped := escaped) (projection := projection) (accepted := accepted) (nativeTyped := nativeTyped)
  exact ⟨flow, generated, extracted, same, fun registry faults interpreted evidence valid =>
    extracted.ready interpreted valid sourceSignatures⟩
end Certificates
end FixedFactory
section Body
open BuiltinImperativeMatchBody
section CompilerConsumers
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {readFuel : Nat} {values : SourceCoreCompatibleValues.Context}
  {function : Dynamic.Closure} {context : SourceSemantics.Context} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope} {type : Ty}
  {administrative : Core.Context}
  {policy : SourceCoreLoops.Policy} {fuel : Nat} {fellThrough escaped : Word} {code : Expr}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (definitions : layouts.definitions = ambient.definitions)
  (registered : frameLayout.Registered ambient.definitions)
  (catalogValid : SignatureCatalogWellFormed values.checked.signatures)
  (program : SourceSemantics.Program)
  (contextValid : CompatibleExpressionLiterals.ContextValid solved context function.evidence)
  (unique : NodeOccurrencesUnique function.source) {faults : FunctionCalls.FaultRep}
  (escapedFault : faults .controlEscapedFunction escaped)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)

include definitions registered catalogValid escapedFault extension faithful functionLeaves functionTypes contextValid unique uninitialized missing in
theorem actual_compiler_body_preserves
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel function.source scope
      function.body type reasonAt fellThrough escaped = .ok code)
    (projection : values.checked.catalog.project function.resultType = .ok type)
    {flow : Expr}
    (generated : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel function.source scope
      function.body type reasonAt true escaped = .ok flow)
    (extracted : BuiltinImperativeMatch.ExtractionFor .reachable layouts owner active frameLayout globals onError readFuel
      values function.source solved reasonAt ambient.definitions administrative
      context scope (.statements true function.body) function.resultType type flow)
    (interpreted : extracted.diagnostics registry faults)
    (signatures : context.signatures = values.checked.signatures)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Dynamic.ExpressionOutcome}
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
    (trace : FunctionCallBody.Trace program function context environment before outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome := by
  let certificate := of_extracted accepted projection generated extracted.tree
  exact certificate.preserves_reachable functions extension definitions registered catalogValid program
    contextValid unique escapedFault uninitialized missing faithful functionLeaves functionTypes
    (extracted.ready interpreted contextValid signatures) environments heaps locals agrees actualTyped reference read unmapped trace

include definitions registered catalogValid escapedFault extension faithful functionLeaves functionTypes contextValid unique uninitialized missing in
theorem actual_compiler_body_reflects
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel function.source scope
      function.body type reasonAt fellThrough escaped = .ok code)
    (projection : values.checked.catalog.project function.resultType = .ok type)
    {flow : Expr}
    (generated : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel function.source scope
      function.body type reasonAt true escaped = .ok flow)
    (extracted : BuiltinImperativeMatch.ExtractionFor .reachable layouts owner active frameLayout globals onError readFuel
      values function.source solved reasonAt ambient.definitions administrative
      context scope (.statements true function.body) function.resultType type flow)
    (interpreted : extracted.diagnostics registry faults)
    (signatures : context.signatures = values.checked.signatures)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
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
    (evaluated : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      FunctionCallBody.Trace program function context environment before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome := by
  let certificate := of_extracted accepted projection generated extracted.tree
  exact certificate.reflects_reachable functions extension definitions registered catalogValid program
    contextValid unique escapedFault uninitialized missing faithful functionLeaves functionTypes
    (extracted.ready interpreted contextValid signatures) environments heaps locals agrees actualTyped reference read unmapped evaluated
end CompilerConsumers
end Body

section Receipt
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : TypedLexicalWhile.ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {definitions : DataEnvironment} {administrative : Core.Context} {scope : TypedLexicalWhile.Scope} {type : Ty}
  {assignment : AssignmentResolution} {rhs : ExpressionId}
  (head : GenericAssignmentStatements.Head values source context (certificates context) scope administrative definitions assignment .equal rhs)
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (missing : ∀ {root resolved reason token count},
    CompatibleMixedRoute.FaultToken values.checked registry root head.prepared.steps resolved reason token count → faults reason token)
  (uninitialized : ∀ location, faults (.uninitializedLocation location) head.prepared.invalidProjection)

include missing uninitialized in
/-- Equal introduces no operand-token law at a statement position. -/
theorem equal_statement_receipt {id : StatementId} {node : StatementNode} {mode : Bool}
    {statements : List StatementId} {expected : TypeSystem.Ty} {code : Expr}
    (found : source.lookupStatement? id = some node) (form : node.form = .assignValue assignment .equal rhs)
    (tail : GenericImperativeMatch.Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
      context scope (.statements mode statements) expected type code)
    (errors : GenericImperativeMatch.Tree.ReachableErrors registry faults tail) :
    GenericImperativeMatch.Tree.ReachableErrors registry faults (.assign found form head tail) :=
  .assign (found := found) (form := form) errors
    (GenericAssignmentStatements.Head.ReachableErrors.equal missing uninitialized)

include missing uninitialized in
/-- The initializer position uses exactly the same policy and static Tree. -/
theorem equal_initializer_receipt {items post : List ForItemForm} {condition : ExpressionId}
    {statements : List StatementId} {expected : TypeSystem.Ty} {code : Expr}
    (tail : GenericImperativeMatch.Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
      context scope (.initializers items condition post statements) expected type code)
    (errors : GenericImperativeMatch.Tree.ReachableErrors registry faults tail) :
    GenericImperativeMatch.Tree.ReachableErrors registry faults (.initializerAssign head tail) :=
  .initializerAssign errors (GenericAssignmentStatements.Head.ReachableErrors.equal missing uninitialized)

/-- The reachable receipt cannot be strengthened to the old operand law for
an empty diagnostic interpretation. -/
theorem equal_strict_impossible (noOperand : ∀ token, ¬ faults (.invalidAssignmentOperands .equal) token) :
    ¬ head.Errors registry faults := by
  intro errors
  exact noOperand _ errors.operands


include missing uninitialized in
theorem equal_assignment_extraction
    {id : StatementId} {node : StatementNode} {mode : Bool}
    {statements : List StatementId} {expected : TypeSystem.Ty} {code : Expr}
    {solved : List SolvedRequirement}
    (found : source.lookupStatement? id = some node) (form : node.form = .assignValue assignment .equal rhs)
    (tail : GenericImperativeMatch.ExtractionFor .reachable layouts owner active frame globals onError values source
      expressionSyntax certificates definitions administrative solved context scope (.statements mode statements) expected type code)
    (interpreted : tail.diagnostics registry faults) :
    (GenericImperativeMatch.ExtractionFor.assign found form head tail).diagnostics registry faults :=
  ⟨interpreted, GenericAssignmentStatements.Head.ReachableErrors.equal missing uninitialized⟩

end Receipt

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Choice { Left(Word), Right(Word) }",
    "function equalMatch(seed: Word) returns (integer) { let result = 0; for (let i = 0; i < 2; i = i + 1) { match (Choice.Left(i)) { case .Left(0) { result = seed; continue; } case .Left(x) { result = result + x; } case .Right(y) {} default {} } } return wordToInteger(result); }",
    "function sharedArms(seed: Word) returns (integer) { match (Choice.Left(seed)) { case .Left(x) {} case .Right(y) {} default {} } return wordToInteger(seed); }",
    "function earlyReturn(seed: Word) returns (integer) { let result = 0; let gap: Word; for (let i = 0; true; result = gap) { match (seed) { case x { result = x; return wordToInteger(result); } default {} } } return 99; }",
    "function rhsFault(seed: Word) returns (integer) { let root = 1; let seen: mapping(Bool => Word); let gap: Word; match (seed) { case x { root = seen[false] + gap; root = 99; } default {} } return wordToInteger(root); }",
    "function compoundFault(seed: Word) returns (integer) { let root: Word; let seen: mapping(Bool => Word); match (seed) { case x { root += seen[false] + x; root = 99; } default {} } return wordToInteger(root); }"
  ]}]
}

open Tests.SourceCompilerFeatureSupport in
private def sourceFor (entry : Entry) : IO TypedSource := do
  let exact ← get "actual source specialization" (SourceCompilationPlan.exactSpecialization entry.cached.validationPlan entry.key)
  pure exact.function.typedBody

open Tests.SourceCompilerFeatureSupport in
private def stable (entry : Entry) (args : List SourceCoreExecution.Value) : IO Unit := do
  let complete ← entry.audit args
  let invocation ← entry.invoke args
  for fuel in [0, 7, 43] do
    let started ← entry.audit args fuel
    let resumed ← get "native match resume" (started.resume 300000)
    require ((← nativeObservation complete) == (← nativeObservation resumed))
      "match resume changed its exact native result/store"
    let pending ← entry.invoke args {executionOptions with executionFuel := fuel}
    let finished ← match pending.outcome with
      | .outOfFuel checkpoint => checkpoint.resume 300000 2048
      | done => pure done
    match invocation.outcome, finished with
    | .succeeded expected, .succeeded actual => require (actual.value == expected.value) "match resume changed value"
    | .failed expected _, .failed actual session =>
      require (actual == expected) "match resume changed token"
      let diagnostic ← get "resumed match diagnostic" (session.diagnostic entry.key actual)
      require (decide (diagnostic = (← invocation.diagnostic expected))) "match resume changed diagnostic"
    | _, _ => throw (IO.userError "match resume changed terminal status")

open Tests.SourceCompilerFeatureSupport in
private def failure (entry : Entry) (expected : SourceCoreFaultSites.Diagnostic)
    (expectedCells : List (TypeSystem.Ty × Option SourceCoreExecution.Value)) : IO Unit := do
  let actual ← entry.invoke [scalar 7]
  match actual.outcome with
  | .failed token _ =>
    require (decide ((← actual.diagnostic token) = some expected)) "actual match failure lost exact source diagnostic"
  | _ => throw (IO.userError "match failure continued")
  entry.checkCells [scalar 7] expectedCells
  stable entry [scalar 7]

open Tests.SourceCompilerFeatureSupport in
def run : IO Unit := do
  let program ← get "match reachable fixtures" (checkProgram workspace)
  for (name, expected) in [("equalMatch", 8), ("sharedArms", 7), ("earlyReturn", 7)] do
    let entry ← compileNamed program name
    let source ← sourceFor entry
    let table ← get "actual equal match table" (SourceCoreAssignmentFaultSites.prepare source Core.wordModulus)
    require (table.sites.isEmpty && table.diagnostic? Word.zero == none)
      "equal match/header/post introduced an unreachable operand token"
    require ((← entry.run [scalar 7]) == .integer expected) "match control/binding/assignment order changed"
    stable entry [scalar 7]
  let rhs ← compileNamed program "rhsFault"
  let source ← sourceFor rhs
  let table ← get "actual RHS-failed equal table" (SourceCoreAssignmentFaultSites.prepare source Core.wordModulus)
  require table.sites.isEmpty "RHS failure added an equal operand token"
  let (node, binder) ← match source.nodes.findSome? fun
      | .expression node => match node.form with | .reference "gap" (.local binder) => some (node,binder) | _ => none
      | _ => none with
    | some pair => pure pair | none => throw (IO.userError "RHS missing read absent")
  failure rhs {error := .uninitializedLocal binder, site := .occurrence node.id.occurrence, span := some node.span}
    [(.word, some (scalar 7)), (.word, some (scalar 1)), (.mapping .bool .word, some (.mapping .bool .word [])),
      (.word, none), (.word, some (scalar 7)), (.word, some (scalar 7))]
  let compound ← compileNamed program "compoundFault"
  let source ← sourceFor compound
  let table ← get "actual compound match table" (SourceCoreAssignmentFaultSites.prepare source 100)
  let node ← match source.nodes.findSome? fun
      | .statement node => match node.form with | .assignValue _ .add _ => some node | _ => none
      | _ => none with
    | some node => pure node | none => throw (IO.userError "compound site absent")
  require (table.length == 1 && table.sites.all fun site => decide
    (site.site = .occurrence node.id.occurrence ∧ site.span = node.span ∧ site.rhsType = .word ∧ site.kind = .value .add))
    "compound match diagnostic lost its first complete raw metadata"
  failure compound {
    error := .invalidAssignmentOperands .add none (some .word),
    site := .occurrence node.id.occurrence, span := some node.span}
    [(.word, some (scalar 7)), (.word, none), (.mapping .bool .word, some (.mapping .bool .word [])),
      (.word, some (scalar 7)), (.word, some (scalar 7))]
  IO.println "reachable match: same-policy extraction/Ready/body finish, empty equal tables, scoped branches, for/continue, faults/effects and resume GREEN"

end Tests.SourceCoreMatchReachableDiagnostics
