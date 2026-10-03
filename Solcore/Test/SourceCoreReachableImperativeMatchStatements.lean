import Solcore.SourceSemantics.CoreLowering.GenericImperativeMatchCertificates
import Solcore.SourceSemantics.CoreLowering.BuiltinImperativeMatchBodyMeaning
import Solcore.SourceSemantics.CoreLowering.CallableIndexedNamedGeneration
import Solcore.Test.SourceCoreUnifiedCorpusSupport

/-! Terminal block/if constructors extend the existing same recursive match
Tree. Reached children retain static stopping receipts and the suffix retains
its complete original compiler equation. Match ledgers are required only on
reached children. Actual body consumers close all Builtin expression/child
meaning. Direct terminal match heads, residual=true extraction and protected
bounded catalog match closure remain separate boundaries. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreReachableImperativeMatchStatements
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof CallableAncestryPairedLookup
open CallableIndexedHistory SourceCoreCallableIndexedFrames BuiltinImperativeMatchBody
#check_failure SourceTypedRuntime.run
section Syntax
variable {source : TypedSource} {context : SourceSemantics.Context} {expressionSyntax : ExpressionId → Prop}
  {mode : Bool} {id : StatementId} {node : StatementNode} {rest left right : List StatementId}
  {expected : TypeSystem.Ty} {condition : ExpressionId} {conditionNode : ExpressionNode}

theorem actual_nonunit_block_syntax
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (form : node.form = .block left) (annotation : node.type = expected)
    (inner : GenericImperativeMatch.Syntax source expressionSyntax context (.statements false left) expected)
    (stops : GenericLexicalStatements.Stopped source left) :
    GenericImperativeMatch.Syntax source expressionSyntax context (.statements mode (id :: rest)) expected :=
  .terminalBlock unique found form annotation inner stops

theorem actual_nonunit_if_syntax
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (form : node.form = .ifThen condition left (some right)) (annotation : node.type = expected)
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionType : conditionNode.type = .bool)
    (typed : ExpressionHasType source context condition conditionNode.type)
    (conditionSyntax : expressionSyntax condition)
    (thenSyntax : GenericImperativeMatch.Syntax source expressionSyntax context (.statements false left) expected)
    (elseSyntax : GenericImperativeMatch.Syntax source expressionSyntax context (.statements false right) expected)
    (thenStops : GenericLexicalStatements.Stopped source left)
    (elseStops : GenericLexicalStatements.Stopped source right) :
    GenericImperativeMatch.Syntax source expressionSyntax context (.statements mode (id :: rest)) expected :=
  .terminalIf unique found form annotation conditionFound conditionType typed conditionSyntax thenSyntax elseSyntax thenStops elseStops

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
/-- No-default exhaustiveness remains typed and pointwise; it does not
supply the universal stopping certificate used by enclosing block/if heads. -/
theorem no_default_match_has_no_stopping_head {resolution : MatchResolution} {summary : ControlSummary}
    (found : source.lookupStatement? id = some node) (form : node.form = .matchWith resolution)
    (absent : resolution.defaultBody = none) :
    ¬ ReachableStatementContinuations.StoppingStatement source id summary := by
  have shape : ∀ actual, source.lookupStatement? id = some actual →
      actual.form = .matchWith resolution := by
    intro actual actualFound
    have same := Option.some.inj (actualFound.symm.trans found)
    exact same ▸ form
  intro receipt
  cases receipt <;> have actualForm := shape _ (by assumption) <;> simp_all

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
theorem accepted_terminal_block
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
    (expressions : ∀ sourceContext, sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = false →
      sourceContext.signatures = values.checked.signatures →
      ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations source scope sourceContext → expressionSyntax id →
      source.lookupExpression? id = some node → ExpressionHasType source sourceContext id node.type →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
      certificates sourceContext scope id lowered)
    (assignments : CompatibleAssignmentStatements.AssignmentPolicy policy values invalidProjection invalidOperand missingDefault)
    (unaryPolicy : CompatibleBitNotStatements.Policy policy values invalidProjection invalidUnary missingDefault)
    (unique : NodeOccurrencesUnique source)
    (assignmentExpressions : ∀ sourceContext scope fuel id lowered,
      sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = false →
      sourceContext.signatures = values.checked.signatures →
      CompatibleExpressionReads.ScopeDeclarations source scope sourceContext →
      expressionSyntax id → ∀ node, source.lookupExpression? id = some node →
      ExpressionHasType source sourceContext id node.type →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
        certificates sourceContext scope id lowered ∧
        HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
          (LanguageResult.resultType lowered.type) definitions)
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {mode : Bool} {id : StatementId}
    {node : StatementNode} {statements rest : List StatementId} {expected : TypeSystem.Ty}
    (exactUnique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .block statements)
    (annotation : node.type = expected)
    (inner : Syntax source expressionSyntax context (.statements false statements) expected)
    (stops : GenericLexicalStatements.Stopped source statements)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {fuel : Nat} {type : Ty} {code : Expr} {selfReason : Word} {nativeType : Ty}
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope (id :: rest) type reasonAt mode selfReason = .ok code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType definitions) :
    Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
      context scope (.statements mode (id :: rest)) expected type code := by
  exact tree_of_typed_flow matchPolicy matchValues matchDefinitions matchAllocator matchChildStatic readPolicy binderPolicy allocationPolicy expressions assignments unaryPolicy unique
    assignmentExpressions (.terminalBlock exactUnique found form annotation inner stops) closed residual sourceSignatures declarations projection accepted nativeTyped

theorem accepted_terminal_if
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
    (expressions : ∀ sourceContext, sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = false →
      sourceContext.signatures = values.checked.signatures →
      ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations source scope sourceContext → expressionSyntax id →
      source.lookupExpression? id = some node → ExpressionHasType source sourceContext id node.type →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
      certificates sourceContext scope id lowered)
    (assignments : CompatibleAssignmentStatements.AssignmentPolicy policy values invalidProjection invalidOperand missingDefault)
    (unaryPolicy : CompatibleBitNotStatements.Policy policy values invalidProjection invalidUnary missingDefault)
    (unique : NodeOccurrencesUnique source)
    (assignmentExpressions : ∀ sourceContext scope fuel id lowered,
      sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = false →
      sourceContext.signatures = values.checked.signatures →
      CompatibleExpressionReads.ScopeDeclarations source scope sourceContext →
      expressionSyntax id → ∀ node, source.lookupExpression? id = some node →
      ExpressionHasType source sourceContext id node.type →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
        certificates sourceContext scope id lowered ∧
        HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
          (LanguageResult.resultType lowered.type) definitions)
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {mode : Bool} {id : StatementId}
    {node : StatementNode} {condition : ExpressionId} {conditionNode : ExpressionNode}
    {thenBody elseBody rest : List StatementId} {expected : TypeSystem.Ty}
    (exactUnique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .ifThen condition thenBody (some elseBody))
    (annotation : node.type = expected)
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionType : conditionNode.type = .bool)
    (typed : ExpressionHasType source context condition conditionNode.type)
    (conditionSyntax : expressionSyntax condition)
    (thenSyntax : Syntax source expressionSyntax context (.statements false thenBody) expected)
    (elseSyntax : Syntax source expressionSyntax context (.statements false elseBody) expected)
    (thenStops : GenericLexicalStatements.Stopped source thenBody)
    (elseStops : GenericLexicalStatements.Stopped source elseBody)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {fuel : Nat} {type : Ty} {code : Expr} {selfReason : Word} {nativeType : Ty}
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope (id :: rest) type reasonAt mode selfReason = .ok code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType definitions) :
    Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
      context scope (.statements mode (id :: rest)) expected type code := by
  exact tree_of_typed_flow matchPolicy matchValues matchDefinitions matchAllocator matchChildStatic readPolicy binderPolicy allocationPolicy expressions assignments unaryPolicy unique
    assignmentExpressions (.terminalIf exactUnique found form annotation conditionFound conditionType typed conditionSyntax thenSyntax elseSyntax thenStops elseStops) closed residual sourceSignatures declarations projection accepted nativeTyped
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

/-- Ready is reconstructed from the reached inner ledger alone. -/
theorem terminal_block_ready
    (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .block statements)
    (inner : Tree layouts owner active frame globals onError values source expressionSyntax certificates
      definitions administrative context scope (.statements false statements) expected type innerCode)
    (stops : GenericLexicalStatements.Stopped source statements)
    (issued : GenericLexicalStatements.IssuedSuffix source scope mode rest type suffix)
    (innerErrors : Tree.ErrorsFor diagnosticPolicy registry faults inner)
    (innerLedger : Tree.SiteLedgersFor diagnosticPolicy solved registry faults innerErrors)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (signatures : context.signatures = values.checked.signatures) :
    Tree.ReadyFor diagnosticPolicy registry faults (.terminalBlock unique found form inner stops issued) := by
  exact Tree.SiteLedgersFor.ready
    (Tree.SiteLedgersFor.terminalBlock (unique := unique) (found := found) (form := form)
      (stops := stops) (issued := issued) innerLedger) valid signatures

/-- Both reached branches keep their own ledger; no suffix ledger is requested. -/
theorem terminal_if_ready {condition : ExpressionId} {conditionNode : ExpressionNode}
    {thenBody elseBody : List StatementId} {conditionCode thenCode elseCode : Expr}
    (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node)
    (form : node.form = .ifThen condition thenBody (some elseBody))
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionType : conditionNode.type = .bool)
    (conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩)
    (thenTree : Tree layouts owner active frame globals onError values source expressionSyntax certificates
      definitions administrative context scope (.statements false thenBody) expected type thenCode)
    (elseTree : Tree layouts owner active frame globals onError values source expressionSyntax certificates
      definitions administrative context scope (.statements false elseBody) expected type elseCode)
    (thenStops : GenericLexicalStatements.Stopped source thenBody)
    (elseStops : GenericLexicalStatements.Stopped source elseBody)
    (issued : GenericLexicalStatements.IssuedSuffix source scope mode rest type suffix)
    (thenErrors : Tree.ErrorsFor diagnosticPolicy registry faults thenTree)
    (elseErrors : Tree.ErrorsFor diagnosticPolicy registry faults elseTree)
    (thenLedger : Tree.SiteLedgersFor diagnosticPolicy solved registry faults thenErrors)
    (elseLedger : Tree.SiteLedgersFor diagnosticPolicy solved registry faults elseErrors)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (signatures : context.signatures = values.checked.signatures) :
    Tree.ReadyFor diagnosticPolicy registry faults
      (.terminalIf unique found form conditionFound conditionType conditionTree thenTree elseTree thenStops elseStops issued) := by
  exact Tree.SiteLedgersFor.ready
    (Tree.SiteLedgersFor.terminalIf (unique := unique) (found := found) (form := form)
      (conditionFound := conditionFound) (conditionType := conditionType) (conditionTree := conditionTree)
      (thenStops := thenStops) (elseStops := elseStops) (issued := issued) thenLedger elseLedger) valid signatures
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
  "function both(flag: Bool) returns (Word) { if (flag) { match (1) { case 1 {} default {} } return 7; } else { match (2) { case 2 {} default {} } return 9; } }",
  "function block() returns (Word) { { match (3) { case 3 {} default {} } return 11; } }",
  "function arms(seed: Word) returns (Word) { match (seed) { case 0 { if (true) { return 13; } else { return 17; } let gap: Word; gap; } default { { return 19; } let gap: Word; gap; } } return 99; }",
  "function inFor() returns (Word) { for (; true; ) { if (true) { match (4) { case 4 {} default {} } return 23; } else { return 29; } let gap: Word; gap; } return 99; }",
  "function inWhile() returns (Word) { while (true) { { match (5) { case 5 {} default {} } return 31; } let gap: Word; gap; } return 99; }",
  "function failed(flag: Bool) returns (Word) { let prior = 37; if (flag) { match (6) { case 6 {} default {} } let gap: Word; return gap; } else { match (7) { case 7 {} default {} } return 41; } let skipped = 99; return skipped; }",
  "function unit() returns (Unit) { { match (8) { case 8 {} default {} } return; } let gap: Word; gap; }",
  "function directMatch(seed: Word) returns (Word) { match (seed) { case 0 { return 43; } default { return 47; } } }",
  "function pattern(seed: Word) returns (Word) { match ((seed, 11)) { case (0, x) { { return x; } let gap: Word; gap; } default { if (true) { return seed; } else { return 61; } let gap: Word; gap; } } return 99; }",
  "function reachable(flag: Bool) returns (Word) { if (flag) { return 53; } match (9) { case 9 {} default {} } return 59; }"
]
private def w (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue

private def inspect (compiled : SourceCoreUnifiedCompilation.Compiled) : IO Unit := do
  let prepared := compiled.indexed
  let diagnostics ← match prepared.base.diagnostics with
    | none => throw (IO.userError "reachable match integration missing diagnostics")
    | some diagnostic => pure diagnostic.program
  let diagnostics := match prepared.base.callableContext with
    | none => diagnostics
    | some native => {diagnostics with rootTable := native.diagnostics.rootTable}
  let parents ← get "reachable match integration parent contexts"
    (SourceCoreStageCodebook.prepareContexts prepared.base.sourceProgram prepared.base.plan
      (prepared.base.locals.bindings.flatMap (·.instances)))
  let mut terminalAnnotations := 0
  let mut reachableAnnotations := 0
  let mut deadSuffixes := 0
  let mut forNodes := 0
  let mut whileNodes := 0
  let mut matchNodes := 0
  let mut defaultNodes := 0
  for named in prepared.base.functions do
    let actual := (CallableIndexedNamedGeneration.representation prepared).atContext named.signature.key []
    let own ← match diagnostics.base.find? named.signature.key with
      | none => throw (IO.userError "reachable match integration missing own diagnostics")
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
    let statements ← get "reachable match integration actual roots"
      (source.roots.mapM (m := Except SourceCoreGeneralFunctions.Error) (fun
        | .statement id => pure id | .expression id => throw (.expectedStatementRoot id)))
    let body ← get "reachable match integration actual complete body"
      (SourceCoreLoops.lowerStatementsWithPolicy policy prepared.fuel source scope statements
        named.signature.resultType reasonAt own.fellThroughReason own.table.escapedReason)
    let same ← get "reachable match integration actual compiler body"
      (CallableIndexedNamedGeneration.bodyAction prepared named diagnostics parents own statements)
    require (body == same) "reachable match integration changed actual compiler body"
    for item in source.nodes do
      match item with
      | .statement node =>
          match node.form with
          | .block _ | .ifThen _ _ (some _) =>
              if node.type == .word then terminalAnnotations := terminalAnnotations + 1
          | .ifThen _ _ none =>
              require (node.type == .unit) "reachable one-branch annotation changed"
              reachableAnnotations := reachableAnnotations + 1
          | .forLoop _ _ _ _ => forNodes := forNodes + 1
          | .whileLoop _ _ => whileNodes := whileNodes + 1
          | .matchWith resolution =>
              matchNodes := matchNodes + 1
              if resolution.defaultBody.isSome then defaultNodes := defaultNodes + 1
              require (!(SourceCoreDataPlaces.declaredBinders source).any (fun binder => binder.id == resolution.hiddenScrutinee))
                "match hidden ID overlaps an ordinary source binder"
          | _ => pure ()
      | _ => pure ()
    match statements with
    | id :: rest =>
        let node ← match source.lookupStatement? id with
          | none => throw (IO.userError "reachable match integration root lookup missing")
          | some node => pure node
        match node.form with
        | .ifThen condition left (some right) =>
            let (_, _) ← get "reachable match integration actual statement read" (policy.readStatement source id)
            let condition ← get "reachable match integration actual condition" (lower (prepared.fuel - 1) source scope condition reasonAt)
            let leftCode ← get "reachable match integration actual left"
              (SourceCoreLoops.lowerFlowStatementsWithPolicy policy (prepared.fuel - 1) source scope left
                named.signature.resultType reasonAt false own.table.escapedReason)
            let rightCode ← get "reachable match integration actual right"
              (SourceCoreLoops.lowerFlowStatementsWithPolicy policy (prepared.fuel - 1) source scope right
                named.signature.resultType reasonAt false own.table.escapedReason)
            let suffix ← get "reachable match integration emitted suffix"
              (SourceCoreLoops.lowerFlowStatementsWithPolicy policy (prepared.fuel - 1) source scope rest
                named.signature.resultType reasonAt true own.table.escapedReason)
            let whole ← get "reachable match integration whole flow"
              (SourceCoreLoops.lowerFlowStatementsWithPolicy policy prepared.fuel source scope statements
                named.signature.resultType reasonAt true own.table.escapedReason)
            require (whole == LocalLoop.sequence named.signature.resultType
              (LocalLoop.conditional named.signature.resultType condition.expression leftCode rightCode) suffix)
              "reachable match integration did not retain original emitted suffix"
            if !rest.isEmpty then deadSuffixes := deadSuffixes + 1
        | .block inner =>
            let innerCode ← get "reachable match integration actual block child"
              (SourceCoreLoops.lowerFlowStatementsWithPolicy policy (prepared.fuel - 1) source scope inner
                named.signature.resultType reasonAt false own.table.escapedReason)
            let suffix ← get "reachable match integration emitted block suffix"
              (SourceCoreLoops.lowerFlowStatementsWithPolicy policy (prepared.fuel - 1) source scope rest
                named.signature.resultType reasonAt true own.table.escapedReason)
            let whole ← get "reachable match integration whole block flow"
              (SourceCoreLoops.lowerFlowStatementsWithPolicy policy prepared.fuel source scope statements
                named.signature.resultType reasonAt true own.table.escapedReason)
            require (whole == LocalLoop.sequence named.signature.resultType innerCode suffix)
              "reachable match integration did not retain original block suffix"
        | _ => pure ()
    | [] => pure ()
  require (terminalAnnotations >= 5 && reachableAnnotations == 1 && forNodes == 1 && whileNodes == 1 && matchNodes == 12 && defaultNodes == 12)
    s!"reachable match fixture coverage changed: {terminalAnnotations}/{reachableAnnotations}/{deadSuffixes}/{forNodes}/{whileNodes}/{matchNodes}/{defaultNodes}"

private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (arguments : List SourceTypedRuntime.Value) (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) : IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel initial
  pure (← get "reachable match integration public resume" (first.resume 300000)).observation

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "reachable match integration" content
    ["both", "block", "arms", "inFor", "inWhile", "failed", "unit", "directMatch", "pattern", "reachable"]
  inspect compiled
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.word, some (w 821)⟩]}
  let successes : List (String × List SourceTypedRuntime.Value × SourceTypedRuntime.Value × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("both", [.bool true], w 7, [(.bool, some (.bool true)), (.word, some (w 1))]),
    ("both", [.bool false], w 9, [(.bool, some (.bool false)), (.word, some (w 2))]),
    ("block", [], w 11, [(.word, some (w 3))]),
    ("arms", [w 0], w 13, [(.word, some (w 0)), (.word, some (w 0))]),
    ("arms", [w 1], w 19, [(.word, some (w 1)), (.word, some (w 1))]),
    ("inFor", [], w 23, [(.word, some (w 4))]),
    ("inWhile", [], w 31, [(.word, some (w 5))]),
    ("failed", [.bool false], w 41, [(.bool, some (.bool false)), (.word, some (w 37)), (.word, some (w 7))]),
    ("unit", [], .unit, [(.word, some (w 8))]),
    ("directMatch", [w 0], w 43, [(.word, some (w 0)), (.word, some (w 0))]),
    ("directMatch", [w 1], w 47, [(.word, some (w 1)), (.word, some (w 1))]),
    ("pattern", [w 0], w 11, [(.word, some (w 0)), (.product .word .word, some (.product (w 0) (w 11))), (.word, some (w 11))]),
    ("pattern", [w 2], w 2, [(.word, some (w 2)), (.product .word .word, some (.product (w 2) (w 11)))]),
    ("reachable", [.bool true], w 53, [(.bool, some (.bool true))]),
    ("reachable", [.bool false], w 59, [(.bool, some (.bool false)), (.word, some (w 9))])]
  let baselines ← successes.mapM (fun test => finish compiled test.1 test.2.1 300000 initial)
  let failure ← finish compiled "failed" [.bool true] 300000 initial
  for fuel in [0, 31, 300000] do
    for ((name, arguments, expected, expectedCells), baseline) in successes.zip baselines do
      let observed ← finish compiled name arguments fuel initial
      require (reprStr observed == reprStr baseline) s!"reachable match integration full resume changed {name}"
      match observed with
      | .done result final =>
          require (reprStr result == reprStr expected) s!"reachable match integration result changed {name}"
          require (reprStr final.heap == reprStr (initial.heap ++ expectedCells.map (fun (type, value) => ⟨type, value⟩)))
            s!"reachable match integration ordered heap/dead suffix changed {name}"
      | other => throw (IO.userError s!"reachable match integration expected done {name}: {reprStr other}")
    let observed ← finish compiled "failed" [.bool true] fuel initial
    require (reprStr observed == reprStr failure) "reachable match integration full fault resume changed"
    match observed with
    | .fault (.uninitializedLocal _) final =>
        require (reprStr final.heap == reprStr (initial.heap ++ [⟨.bool, some (.bool true)⟩, ⟨.word, some (w 37)⟩, ⟨.word, some (w 6)⟩, ⟨.word, none⟩]))
          "reachable match integration fault executed a dead suffix or changed its prefix"
    | other => throw (IO.userError s!"reachable match integration expected head fault: {reprStr other}")
  IO.println "reachable match integration: same recursive match/for/while grammar, non-Unit terminal annotations, source stops, original native child, emitted dead suffix, ordered full heaps and public resume GREEN"


end Tests.SourceCoreReachableImperativeMatchStatements
