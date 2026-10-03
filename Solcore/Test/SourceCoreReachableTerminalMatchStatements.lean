import Solcore.SourceSemantics.CoreLowering.GenericImperativeMatchCertificates
import Solcore.SourceSemantics.CoreLowering.BuiltinImperativeMatchBodyMeaning
import Solcore.SourceSemantics.CoreLowering.CallableIndexedNamedGeneration
import Solcore.Test.SourceCoreUnifiedCorpusSupport

import Solcore.SourceSemantics.CoreLowering.ReachableMatchContinuationMeaning

/-! A default-present stopping match extends the same existing static grammar.
The actual compiler emits every suffix, while only reached branches require
Trees, diagnostics and ledgers. Universal default stopping stays separate
from typed no-default stopping. Concrete Builtin body consumers close all
runtime child meaning; protected bounded catalog match closure is separate. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreReachableTerminalMatchStatements
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof CallableAncestryPairedLookup
open CallableIndexedHistory SourceCoreCallableIndexedFrames BuiltinImperativeMatchBody
#check_failure SourceTypedRuntime.run
section Syntax
variable {source : TypedSource} {context : SourceSemantics.Context} {expressionSyntax : ExpressionId → Prop}
  {mode : Bool} {id : StatementId} {node : StatementNode} {resolution : MatchResolution}
  {scrutineeNode : ExpressionNode} {rest : List StatementId} {expected : TypeSystem.Ty}
theorem actual_terminal_match_syntax {control : ControlContext} {caseFacts}
      (unique : NodeOccurrencesUnique source)
      (found : source.lookupStatement? id = some node) (form : node.form = .matchWith resolution)
      (sourceType : node.type = .unit ∨ node.type = expected)
      (scrutineeFound : source.lookupExpression? resolution.scrutinee = some scrutineeNode)
      (scrutineeTyped : ExpressionHasType source context resolution.scrutinee scrutineeNode.type)
      (scrutineeSyntax : expressionSyntax resolution.scrutinee)
      (casesTyped : MatchCasesHaveType source control context scrutineeNode.type resolution.cases caseFacts)
      (defaultTyped : ∀ statements, resolution.defaultBody = some statements →
        ∃ finalContext facts, StatementsHaveType source control context statements finalContext facts)
      (hiddenOrdinary : source.inputs.any (fun input => decide (input.id = resolution.hiddenScrutinee)) = false)
      (armsOrdinary : ∀ arm ∈ resolution.cases, ∀ binder ∈ arm.pattern.binderIds,
        source.inputs.any (fun input => decide (input.id = binder)) = false)
      (children : ∀ request childContext,
        GenericMatchChildren.ContextFor source context scrutineeNode.type resolution.cases resolution.defaultBody request childContext →
        GenericImperativeMatch.Syntax source expressionSyntax childContext (.statements false request.statements) expected)
      (stops : ReachableMatchContinuations.DefaultStopped source id resolution) :
      GenericImperativeMatch.Syntax source expressionSyntax context (.statements mode (id :: rest)) expected :=
  .terminalMatch unique found form sourceType scrutineeFound scrutineeTyped scrutineeSyntax casesTyped defaultTyped hiddenOrdinary armsOrdinary children stops

theorem stopped_of_actual_branches {fallback : List StatementId}
    (found : source.lookupStatement? id = some node) (form : node.form = .matchWith resolution)
    (present : resolution.defaultBody = some fallback)
    (branches : ReachableMatchContinuations.BranchStops source resolution) :
    ReachableMatchContinuations.DefaultStopped source id resolution :=
  .of_source found form present branches

theorem original_stops_transport {origin : TypedSource}
    (identity : GenericLexicalStatements.StatementSourceIdentity origin source)
    (stops : ReachableMatchContinuations.DefaultStopped origin id resolution) :
    ReachableMatchContinuations.DefaultStopped source id resolution := stops.transport identity

theorem no_default_stopped (absent : resolution.defaultBody = none) :
    ¬ ReachableMatchContinuations.DefaultStopped source id resolution := by
  intro stopped
  obtain ⟨fallback, present⟩ := stopped.default_present
  rw [absent] at present
  cases present

theorem empty_default_not_stopped (empty : resolution.defaultBody = some []) :
    ¬ ReachableMatchContinuations.DefaultStopped source id resolution := by
  intro stopped
  obtain ⟨origin, summary, _, original⟩ := stopped.current_branches.fallback [] empty
  exact original.nonempty rfl
/-- Reachable nil remains restricted; terminality cannot authenticate an empty list. -/
theorem reachable_nil_nonunit (nonunit : expected ≠ .unit) :
    ¬ GenericImperativeMatch.Syntax source expressionSyntax context (.statements true []) expected := by
  intro tree
  cases tree with
  | body lexical => cases lexical with
    | nil allowed => rcases allowed with impossible | unit; cases impossible; exact nonunit unit

theorem no_empty_stopped : ¬ GenericLexicalStatements.Stopped source [] := by
  rintro ⟨origin, summary, identity, stops⟩
  exact stops.nonempty rfl

/-- Source transport preserves the actual issuing source and callback equation.
It does not assume an arbitrary source-dependent policy accepts the view. -/
theorem original_suffix_transport {origin : TypedSource} {scope : SourceCoreLocalCell.Scope} {type : Ty} {code : Expr}
    (identity : GenericLexicalStatements.StatementSourceIdentity origin source)
    (issued : GenericLexicalStatements.IssuedSuffix origin scope mode rest type code) :
    GenericLexicalStatements.IssuedSuffix source scope mode rest type code :=
  issued.transport identity
end Syntax

section Extraction
open GenericImperativeMatch
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : SourceCoreCompatibleValues.Context} {source : TypedSource} {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {reasonAt : ExpressionId → Word} {policy : SourceCoreLoops.Policy}
  {matchCompilation : SourceCoreCompatibleDataMatches.Context}
  {administrative : Core.Context} {definitions : DataEnvironment}
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Solcore.Syntax.ValueAssignOp → Word}
  {invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}
theorem accepted_terminal_match (residualMode : Bool) (diagnosticPolicy : AssignmentDiagnosticPolicy) {tracked : Bool}
    (factory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy source invalidOperand)
    (matchPolicy : policy.lowerMatch = some (SourceCoreCompatibleDataMatches.lowerWithReasons matchCompilation))
    (matchValues : matchCompilation.values = values) (matchDefinitions : matchCompilation.definitions = definitions)
    (matchAllocator : matchCompilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (matchChildStatic : MatchChildStatic matchCompilation source certificates definitions administrative)
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      policy.lowerBinder source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked source scope binder)
    (allocationPolicy : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (expressions : ∀ sourceContext, sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = residualMode →
      sourceContext.signatures = values.checked.signatures →
      ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations source scope sourceContext → expressionSyntax id →
      source.lookupExpression? id = some node → ExpressionHasType source sourceContext id node.type →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
      certificates sourceContext scope id lowered)
    (assignments : CompatibleAssignmentStatements.AssignmentPolicy policy values invalidProjection invalidOperand missingDefault)
    (unaryPolicy : CompatibleBitNotStatements.Policy policy values invalidProjection invalidUnary missingDefault)
    (assignmentExpressions : ∀ sourceContext scope fuel id lowered,
      sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = residualMode →
      sourceContext.signatures = values.checked.signatures →
      CompatibleExpressionReads.ScopeDeclarations source scope sourceContext →
      expressionSyntax id → ∀ node, source.lookupExpression? id = some node →
      ExpressionHasType source sourceContext id node.type →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
        certificates sourceContext scope id lowered ∧
        HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
          (LanguageResult.resultType lowered.type) definitions)
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {mode : Bool} {id : StatementId}
    {node : StatementNode} {resolution : MatchResolution} {scrutineeNode : ExpressionNode}
    {rest : List StatementId} {expected : TypeSystem.Ty} {control : ControlContext} {caseFacts}
      (exactUnique : NodeOccurrencesUnique source)
      (found : source.lookupStatement? id = some node) (form : node.form = .matchWith resolution)
      (sourceType : node.type = .unit ∨ node.type = expected)
      (scrutineeFound : source.lookupExpression? resolution.scrutinee = some scrutineeNode)
      (scrutineeTyped : ExpressionHasType source context resolution.scrutinee scrutineeNode.type)
      (scrutineeSyntax : expressionSyntax resolution.scrutinee)
      (casesTyped : MatchCasesHaveType source control context scrutineeNode.type resolution.cases caseFacts)
      (defaultTyped : ∀ statements, resolution.defaultBody = some statements →
        ∃ finalContext facts, StatementsHaveType source control context statements finalContext facts)
      (hiddenOrdinary : source.inputs.any (fun input => decide (input.id = resolution.hiddenScrutinee)) = false)
      (armsOrdinary : ∀ arm ∈ resolution.cases, ∀ binder ∈ arm.pattern.binderIds,
        source.inputs.any (fun input => decide (input.id = binder)) = false)
      (children : ∀ request childContext,
        GenericMatchChildren.ContextFor source context scrutineeNode.type resolution.cases resolution.defaultBody request childContext →
        GenericImperativeMatch.Syntax source expressionSyntax childContext (.statements false request.statements) expected)
      (stops : ReachableMatchContinuations.DefaultStopped source id resolution)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = residualMode)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {fuel : Nat} {type : Ty} {code : Expr} {selfReason : Word} {nativeType : Ty}
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope (id :: rest) type reasonAt mode selfReason = .ok code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType definitions) :
    Nonempty (ExtractionFor diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative matchCompilation.solvedRequirements
      context scope (.statements mode (id :: rest)) expected type code) := by
  exact extraction_of_typed_flow_with_residual residualMode diagnosticPolicy factory matchPolicy matchValues matchDefinitions
    matchAllocator matchChildStatic readPolicy binderPolicy allocationPolicy expressions assignments unaryPolicy exactUnique
    assignmentExpressions (.terminalMatch exactUnique found form sourceType scrutineeFound scrutineeTyped scrutineeSyntax casesTyped
      defaultTyped hiddenOrdinary armsOrdinary children stops) closed residual sourceSignatures declarations projection accepted nativeTyped

end Extraction

section LedgerConsumers
open GenericImperativeMatch
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource} {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {definitions : DataEnvironment} {administrative : Core.Context}
  {diagnosticPolicy : AssignmentDiagnosticPolicy} {registry : SourceCoreRawMetadata.Registry}
  {faults : FunctionCalls.FaultRep} {solved : List SolvedRequirement} {evidence : Dynamic.EvidenceEnvironment}
  {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {id : StatementId} {node : StatementNode}
  {rest statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {innerCode suffix : Expr}

theorem branch_only_ready {resolution : MatchResolution} {scrutineeNode : ExpressionNode}
    {matched : Expr} {selfReason : Word} {control : ControlContext} {caseFacts}
      (unique : NodeOccurrencesUnique source)
      (found : source.lookupStatement? id = some node) (form : node.form = .matchWith resolution)
      (scrutineeFound : source.lookupExpression? resolution.scrutinee = some scrutineeNode)
      (scrutineeTyped : ExpressionHasType source context resolution.scrutinee scrutineeNode.type)
      (casesTyped : MatchCasesHaveType source control context scrutineeNode.type resolution.cases caseFacts)
      (defaultTyped : ∀ statements, resolution.defaultBody = some statements →
        ∃ finalContext facts, StatementsHaveType source control context statements finalContext facts)
      (compilation : SourceCoreCompatibleDataMatches.Context)
      (sameValues : compilation.values = values) (sameDefinitions : compilation.definitions = definitions)
      (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
        (layouts.allocatorAt owner active onError)))
      (requests : List GenericMatchChildren.Request)
      (receipt : CompatibleMatchCertificates.Certificate compilation source scope id resolution type selfReason
        (certificates context) (GenericMatchChildren.Occurs requests) matched)
      (ordinary : CompatibleMatchSelectionPrefix.Ordinary receipt)
      (children : ∀ request, request ∈ requests → ∀ childContext,
        GenericMatchChildren.ScopedContextFor source context (resolution.hiddenScrutinee :: scope.map Prod.fst) scrutineeNode.type resolution.cases resolution.defaultBody request childContext →
        Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
          childContext request.scope (.statements false request.statements) expected type request.code)
      (stops : ReachableMatchContinuations.DefaultStopped source id resolution)
      (issued : GenericLexicalStatements.IssuedSuffix source scope mode rest type suffix)
    (childErrors : ∀ request member childContext related, Tree.ErrorsFor diagnosticPolicy registry faults (children request member childContext related))
    (sameLedger : compilation.solvedRequirements = solved)
    (childLedgers : ∀ request member childContext related, Tree.SiteLedgersFor diagnosticPolicy solved registry faults (childErrors request member childContext related))
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (signatures : context.signatures = values.checked.signatures) :
    Tree.ReadyFor diagnosticPolicy registry faults (.terminalMatch unique found form scrutineeFound scrutineeTyped casesTyped defaultTyped
      compilation sameValues sameDefinitions allocator requests receipt ordinary children stops issued) := by
  exact Tree.SiteLedgersFor.ready
    (Tree.SiteLedgersFor.terminalMatch (unique := unique) (found := found) (scrutineeFound := scrutineeFound)
      (scrutineeTyped := scrutineeTyped) (casesTyped := casesTyped) (defaultTyped := defaultTyped)
      (sameValues := sameValues) (allocator := allocator) (receipt := receipt) (ordinary := ordinary)
      (stops := stops) (issued := issued) form sameDefinitions sameLedger childLedgers) valid signatures
end LedgerConsumers

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
    (tree : BuiltinImperativeMatch.Tree layouts owner active frameLayout globals onError readFuel
      values function.source solved reasonAt ambient.definitions administrative
      context scope (.statements true function.body) function.resultType type flow)
    (errors : GenericImperativeMatch.Tree.Ready registry faults tree)
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
  let certificate := of_extracted accepted projection generated tree
  exact certificate.preserves functions extension definitions registered catalogValid program
    contextValid unique escapedFault uninitialized missing faithful functionLeaves functionTypes
    errors environments heaps locals agrees actualTyped reference read unmapped trace

include definitions registered catalogValid escapedFault extension faithful functionLeaves functionTypes contextValid unique uninitialized missing in
theorem actual_compiler_body_reflects
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel function.source scope
      function.body type reasonAt fellThrough escaped = .ok code)
    (projection : values.checked.catalog.project function.resultType = .ok type)
    {flow : Expr}
    (generated : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel function.source scope
      function.body type reasonAt true escaped = .ok flow)
    (tree : BuiltinImperativeMatch.Tree layouts owner active frameLayout globals onError readFuel
      values function.source solved reasonAt ambient.definitions administrative
      context scope (.statements true function.body) function.resultType type flow)
    (errors : GenericImperativeMatch.Tree.Ready registry faults tree)
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
  let certificate := of_extracted accepted projection generated tree
  exact certificate.reflects functions extension definitions registered catalogValid program
    contextValid unique escapedFault uninitialized missing faithful functionLeaves functionTypes
    errors environments heaps locals agrees actualTyped reference read unmapped evaluated
end CompilerConsumers

private def content : String := String.intercalate "\n" [
  "enum Choice { Left(Word), Right(Word) }",
  "function direct(seed: Word) returns (Word) { match (seed) { case 0 { return 43; } default { return 47; } } }",
  "function dead(seed: Word) returns (Word) { match (seed) { case 0 { if (true) { return 13; } else { return 17; } } default { { return 19; } } } let gap: Word; gap; }",
  "function pattern(seed: Word) returns (Word) { match ((seed, 11)) { case (0, x) { { return x; } let skipped = 99; } default { if (true) { return seed; } else { return 61; } let skipped = 99; } } return 99; }",
  "function same(seed: Word) returns (Word) { match (seed) { case 0 { return 23; } case 1 { return 23; } default { return 23; } } return 99; }",
  "function reachable(seed: Word) returns (Word) { match (seed) { case 0 {} default { return 31; } } return 29; }",
  "function failed(seed: Word) returns (Word) { match (seed) { case 0 { let prior = 37; let gap: Word; return gap; } default { return 41; } } let skipped = 99; return skipped; }",
  "function scrutineeFault() returns (Word) { let gap: Word; match (gap) { case 0 { return 1; } default { return 2; } } let skipped = 99; return skipped; }",
  "function inFor() returns (Word) { for (; true; ) { match (4) { case 4 { return 23; } default { return 29; } } let gap: Word; gap; } return 99; }",
  "function inWhile() returns (Word) { while (true) { match (5) { case 5 { return 31; } default { return 37; } } let gap: Word; gap; } return 99; }",
  "function inBlock() returns (Word) { { match (6) { case 6 { return 41; } default { return 43; } } let gap: Word; gap; } let skipped = 99; return skipped; }",
  "function inIf(flag: Bool) returns (Word) { if (flag) { match (7) { case 7 { return 47; } default { return 53; } } let gap: Word; gap; } else { match (8) { case 8 { return 59; } default { return 61; } } let gap: Word; gap; } }",
  "function nominalLeft(value: Choice) returns (Word) { match (value) { case .Left(x) { return x; } case .Right(y) { return y; } } }",
  "function nominalRight(value: Choice) returns (Word) { match (value) { case .Left(x) { return x; } case .Right(y) { return y; } } }"
]
private def w (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue

private def inspect (compiled : SourceCoreUnifiedCompilation.Compiled) : IO Unit := do
  let prepared := compiled.indexed
  let diagnostics ← match prepared.base.diagnostics with
    | none => throw (IO.userError "terminal default match continuations missing diagnostics")
    | some diagnostic => pure diagnostic.program
  let diagnostics := match prepared.base.callableContext with
    | none => diagnostics
    | some native => {diagnostics with rootTable := native.diagnostics.rootTable}
  let parents ← get "terminal default match parent contexts"
    (SourceCoreStageCodebook.prepareContexts prepared.base.sourceProgram prepared.base.plan
      (prepared.base.locals.bindings.flatMap (·.instances)))
  let mut defaultNodes := 0
  let mut noDefaultNodes := 0
  let mut nilSuffixes := 0
  let mut nonemptySuffixes := 0
  for named in prepared.base.functions do
    let actual := (CallableIndexedNamedGeneration.representation prepared).atContext named.signature.key []
    let own ← match diagnostics.base.find? named.signature.key with
      | none => throw (IO.userError "terminal default match own diagnostics missing")
      | some own => pure own
    let source := CallableIndexedNamedGeneration.source named
    let scope := named.inputs.reverse.map (fun binding => (binding.1.id, binding.2))
    let reasonAt := diagnostics.reasonAt named.signature.key
    let lower := SourceCoreGeneralFunctions.lowerContextualExpression prepared.base.sourceProgram actual
      prepared.base.sourceProgram.signatures prepared.base.locals parents own.assignments diagnostics
      (CallableIndexedNamedGeneration.context prepared named) prepared.base.callableContext none none
    let policy : SourceCoreLoops.Policy := {
      actual.loopsWithSourceCells actual.expressions.sourceCells named.specialized.function.solvedRequirements
        own.assignments diagnostics named.signature.key lower with
      sourceCells := actual.expressions.sourceCells
      lowerBinder := SourceCoreGeneralFunctions.contextualBinder actual prepared.base.locals named.signature.key [] }
    let statements ← get "terminal default match actual roots"
      (source.roots.mapM (m := Except SourceCoreGeneralFunctions.Error) (fun
        | .statement id => pure id | .expression id => throw (.expectedStatementRoot id)))
    let body ← get "terminal default match actual body"
      (SourceCoreLoops.lowerStatementsWithPolicy policy prepared.fuel source scope statements
        named.signature.resultType reasonAt own.fellThroughReason own.table.escapedReason)
    let same ← get "terminal default match actual compiler body"
      (CallableIndexedNamedGeneration.bodyAction prepared named diagnostics parents own statements)
    require (body == same) "terminal default match changed actual body code"
    for item in source.nodes do
      match item with
      | .statement node =>
        match node.form with
        | .matchWith resolution =>
          if resolution.defaultBody.isSome then defaultNodes := defaultNodes + 1
          else noDefaultNodes := noDefaultNodes + 1
          require (!(SourceCoreDataPlaces.declaredBinders source).any (fun binder => binder.id == resolution.hiddenScrutinee))
            "terminal default match hidden scrutinee overlaps a source binder"
        | _ => pure ()
      | _ => pure ()
    match statements with
    | id :: rest =>
      let node ← match source.lookupStatement? id with
        | none => throw (IO.userError "terminal default match root lookup missing")
        | some node => pure node
      match node.form with
      | .matchWith resolution =>
        let callback ← match policy.lowerMatch with
          | none => throw (IO.userError "terminal default match callback missing")
          | some callback => pure callback
        let matched ← get "terminal default match actual callback"
          (callback policy.lowerExpression
            (fun _ childSource childScope childStatements resultType childReasonAt escaped =>
              SourceCoreLoops.lowerFlowStatementsWithPolicy policy (prepared.fuel - 1) childSource childScope childStatements
                resultType childReasonAt false escaped)
            (prepared.fuel - 1) source scope id resolution named.signature.resultType reasonAt own.table.escapedReason)
        let suffix ← get "terminal default match complete emitted suffix"
          (SourceCoreLoops.lowerFlowStatementsWithPolicy policy (prepared.fuel - 1) source scope rest
            named.signature.resultType reasonAt true own.table.escapedReason)
        let whole ← get "terminal default match whole flow"
          (SourceCoreLoops.lowerFlowStatementsWithPolicy policy prepared.fuel source scope statements
            named.signature.resultType reasonAt true own.table.escapedReason)
        require (whole == LocalLoop.sequence named.signature.resultType matched suffix)
          "terminal default match did not retain actual callback and full suffix"
        if rest.isEmpty then nilSuffixes := nilSuffixes + 1 else nonemptySuffixes := nonemptySuffixes + 1
      | _ => pure ()
    | [] => pure ()
  require (defaultNodes == 12 && noDefaultNodes == 2 && nilSuffixes == 3 && nonemptySuffixes == 5)
    s!"terminal default match fixture coverage changed: {defaultNodes}/{noDefaultNodes}/{nilSuffixes}/{nonemptySuffixes}"

private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (arguments : List SourceTypedRuntime.Value) (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) : IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel initial
  pure (← get "terminal default match public resume" (first.resume 300000)).observation

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "terminal default match continuations" content
    ["direct", "dead", "pattern", "same", "reachable", "failed", "scrutineeFault", "nominalLeft", "nominalRight", "inFor", "inWhile", "inBlock", "inIf"]
  inspect compiled
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.word, some (w 821)⟩]}
  let successes : List (String × List SourceTypedRuntime.Value × SourceTypedRuntime.Value × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("inFor", [], w 23, [(.word, some (w 4))]),
    ("inWhile", [], w 31, [(.word, some (w 5))]),
    ("inBlock", [], w 41, [(.word, some (w 6))]),
    ("inIf", [.bool true], w 47, [(.bool, some (.bool true)), (.word, some (w 7))]),
    ("inIf", [.bool false], w 59, [(.bool, some (.bool false)), (.word, some (w 8))]),
    ("direct", [w 0], w 43, [(.word, some (w 0)), (.word, some (w 0))]),
    ("direct", [w 1], w 47, [(.word, some (w 1)), (.word, some (w 1))]),
    ("dead", [w 0], w 13, [(.word, some (w 0)), (.word, some (w 0))]),
    ("dead", [w 1], w 19, [(.word, some (w 1)), (.word, some (w 1))]),
    ("pattern", [w 0], w 11, [(.word, some (w 0)), (.product .word .word, some (.product (w 0) (w 11))), (.word, some (w 11))]),
    ("pattern", [w 2], w 2, [(.word, some (w 2)), (.product .word .word, some (.product (w 2) (w 11)))]),
    ("same", [w 0], w 23, [(.word, some (w 0)), (.word, some (w 0))]),
    ("same", [w 1], w 23, [(.word, some (w 1)), (.word, some (w 1))]),
    ("same", [w 2], w 23, [(.word, some (w 2)), (.word, some (w 2))]),
    ("reachable", [w 0], w 29, [(.word, some (w 0)), (.word, some (w 0))]),
    ("reachable", [w 1], w 31, [(.word, some (w 1)), (.word, some (w 1))]),
    ("failed", [w 1], w 41, [(.word, some (w 1)), (.word, some (w 1))])]
  let baselines ← successes.mapM (fun test => finish compiled test.1 test.2.1 300000 initial)
  for fuel in [0, 31, 300000] do
    for ((name, arguments, expected, expectedCells), baseline) in successes.zip baselines do
      let observed ← finish compiled name arguments fuel initial
      require (reprStr observed == reprStr baseline) s!"terminal default match full resume changed {name}"
      match observed with
      | .done result final =>
        require (reprStr result == reprStr expected) s!"terminal default match result changed {name}"
        require (reprStr final.heap == reprStr (initial.heap ++ expectedCells.map (fun (type, value) => ⟨type, value⟩)))
          s!"terminal default match full heap/dead suffix changed {name}"
      | other => throw (IO.userError s!"terminal default match expected done {name}: {reprStr other}")
  let failures : List (String × List SourceTypedRuntime.Value × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("failed", [w 0], [(.word, some (w 0)), (.word, some (w 0)), (.word, some (w 37)), (.word, none)]),
    ("scrutineeFault", [], [(.word, none)])]
  for (name, arguments, expectedCells) in failures do
    let baseline ← finish compiled name arguments 300000 initial
    for fuel in [0, 31, 300000] do
      let observed ← finish compiled name arguments fuel initial
      require (reprStr observed == reprStr baseline) s!"terminal default match fault resume changed {name}"
      match observed with
      | .fault (.uninitializedLocal _) final =>
        require (reprStr final.heap == reprStr (initial.heap ++ expectedCells.map (fun (type, value) => ⟨type, value⟩)))
          s!"terminal default match first fault/dead suffix changed {name}"
      | other => throw (IO.userError s!"terminal default match expected fault {name}: {reprStr other}")
  let choice ← match compiled.indexed.base.sourceProgram.signatures.dataTypes.find? (·.name == "Choice") with
    | none => throw (IO.userError "terminal default match Choice missing")
    | some choice => pure choice
  let sourceType := TypeSystem.Ty.nominal choice.id []
  for (name, constructor, value) in [("nominalLeft", 0, 5), ("nominalRight", 1, 7)] do
    let metadata : DataConstructorInstantiation := ⟨⟨choice.id, constructor⟩, [], [.word], sourceType⟩
    let expected : SourceTypedRuntime.Value := .constructed metadata [w value]
    let baseline ← finish compiled name [expected] 300000 initial
    for fuel in [0, 31, 300000] do
      let observed ← finish compiled name [expected] fuel initial
      require (reprStr observed == reprStr baseline) s!"reachable typed nominal resume changed {name}"
      match observed with
      | .done result final =>
        require (reprStr result == reprStr (w value)) s!"reachable typed nominal result changed {name}"
        require (reprStr final.heap == reprStr (initial.heap ++ [⟨sourceType, some expected⟩, ⟨sourceType, some expected⟩, ⟨.word, some (w value)⟩]))
          s!"reachable typed nominal full heap changed {name}"
      | other => throw (IO.userError s!"reachable typed nominal expected done {name}: {reprStr other}")
  IO.println "terminal default match continuations: same grammar terminal default, separate typed no-default, actual issued suffix, full source cells/fault/public resume GREEN"

end Tests.SourceCoreReachableTerminalMatchStatements
