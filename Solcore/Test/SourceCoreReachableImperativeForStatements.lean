import Solcore.SourceSemantics.CoreLowering.GenericImperativeForCertificates
import Solcore.SourceSemantics.CoreLowering.NamedForFunctionFallthrough
import Solcore.SourceSemantics.CoreLowering.CallableIndexedNamedGeneration
import Solcore.Test.SourceCoreRecursiveNamedImperativeForBounds

/-! The existing imperative Tree keeps terminal block/if children in the same
recursive positions as ordinary statements, for initializers and loop bodies.
Their suffix remains the exact originally issued code. Static stopping evidence
and the original source/native trace show that this suffix is not executed;
reachable nil is still Unit-only. The concrete final consumers close expression
and callee laws without adding runtime laws to static receipts. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreReachableImperativeForStatements
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof CallableAncestryPairedLookup
open CallableIndexedHistory SourceCoreCallableIndexedFrames RecursiveNamedCatalog
#check_failure SourceTypedRuntime.run
section Syntax
variable {source : TypedSource} {context : SourceSemantics.Context} {expressionSyntax : ExpressionId → Prop}
  {mode : Bool} {id : StatementId} {node : StatementNode} {rest left right : List StatementId}
  {expected : TypeSystem.Ty} {condition : ExpressionId} {conditionNode : ExpressionNode}

theorem actual_nonunit_block_syntax
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (form : node.form = .block left) (annotation : node.type = expected)
    (inner : GenericImperativeFor.Syntax source expressionSyntax context (.statements false left) expected)
    (stops : GenericLexicalStatements.Stopped source left) :
    GenericImperativeFor.Syntax source expressionSyntax context (.statements mode (id :: rest)) expected :=
  .terminalBlock unique found form annotation inner stops

theorem actual_nonunit_if_syntax
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (form : node.form = .ifThen condition left (some right)) (annotation : node.type = expected)
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionType : conditionNode.type = .bool)
    (typed : ExpressionHasType source context condition conditionNode.type)
    (conditionSyntax : expressionSyntax condition)
    (thenSyntax : GenericImperativeFor.Syntax source expressionSyntax context (.statements false left) expected)
    (elseSyntax : GenericImperativeFor.Syntax source expressionSyntax context (.statements false right) expected)
    (thenStops : GenericLexicalStatements.Stopped source left)
    (elseStops : GenericLexicalStatements.Stopped source right) :
    GenericImperativeFor.Syntax source expressionSyntax context (.statements mode (id :: rest)) expected :=
  .terminalIf unique found form annotation conditionFound conditionType typed conditionSyntax thenSyntax elseSyntax thenStops elseStops

/-- Reachable nil remains restricted; terminality cannot authenticate an empty list. -/
theorem reachable_nil_nonunit (nonunit : expected ≠ .unit) :
    ¬ GenericImperativeFor.Syntax source expressionSyntax context (.statements true []) expected := by
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
open GenericImperativeFor
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : SourceCoreCompatibleValues.Context} {source : TypedSource} {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {reasonAt : ExpressionId → Word} {policy : SourceCoreLoops.Policy}
  {administrative : Core.Context} {definitions : DataEnvironment}
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Solcore.Syntax.ValueAssignOp → Word}
  {invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}
theorem accepted_terminal_block (residualMode : Bool)
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
    (unique : NodeOccurrencesUnique source)
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
    {node : StatementNode} {statements rest : List StatementId} {expected : TypeSystem.Ty}
    (exactUnique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .block statements)
    (annotation : node.type = expected)
    (inner : Syntax source expressionSyntax context (.statements false statements) expected)
    (stops : GenericLexicalStatements.Stopped source statements)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = residualMode)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {fuel : Nat} {type : Ty} {code : Expr} {selfReason : Word} {nativeType : Ty}
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope (id :: rest) type reasonAt mode selfReason = .ok code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType definitions) :
    Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
      context scope (.statements mode (id :: rest)) expected type code := by
  exact tree_of_typed_flow_with_residual residualMode readPolicy binderPolicy allocationPolicy expressions assignments unaryPolicy unique
    assignmentExpressions (.terminalBlock exactUnique found form annotation inner stops) closed residual sourceSignatures declarations projection accepted nativeTyped

theorem accepted_terminal_if (residualMode : Bool)
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
    (unique : NodeOccurrencesUnique source)
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
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = residualMode)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {fuel : Nat} {type : Ty} {code : Expr} {selfReason : Word} {nativeType : Ty}
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope (id :: rest) type reasonAt mode selfReason = .ok code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType definitions) :
    Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
      context scope (.statements mode (id :: rest)) expected type code := by
  exact tree_of_typed_flow_with_residual residualMode readPolicy binderPolicy allocationPolicy expressions assignments unaryPolicy unique
    assignmentExpressions (.terminalIf exactUnique found form annotation conditionFound conditionType typed conditionSyntax thenSyntax elseSyntax thenStops elseStops) closed residual sourceSignatures declarations projection accepted nativeTyped
end Extraction

section Concrete
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {body : BuiltinNamedCalls.Body prepared values ambient.definitions program} {locations : Locations} {capturePrefix : Nat}
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {compilation : SourceCoreFunctions.Context} {fuel : Nat} {source : TypedSource}
  {expressionSyntax : ExpressionId → Prop} {administrative : Core.Context}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions) (evidence : Dynamic.EvidenceEnvironment)
  (unique : NodeOccurrencesUnique source)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  (bodyUninitialized : ∀ id location, faults (.uninitializedLocation location) (body.reasonAt id))
  (bodyMissing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((body.reasonAt id).add tag))


include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
theorem concrete_preserves (budget : Nat)
    {context : SourceSemantics.Context} {scope : Scope} {mode : Bool}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : GenericImperativeFor.Tree layouts owner active frame globals onError values source expressionSyntax
      (fun context => CompatibleExpressionCalls.Tree (RecursiveNamedCatalog.Head [Header.of_body body] compilation source context)
        fuel values source context solved reasonAt) ambient.definitions administrative
      context scope (.statements mode statements) expected type code)
    (errors : GenericImperativeFor.Tree.ReachableErrors registry faults tree) :
    RecursiveNamedHeaderContracts.AtMost budget (fun size => RecursiveNamedLoopContracts.PreservesAt functions program evidence
      (entry := protectedEntry [Header.of_body body] locations capturePrefix compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals) (administrative := administrative)
      size (scope := scope) mode statements expected type code) := by
  apply RecursiveNamedImperativeFor.preservesAt_for functions definitions registered extension program evidence
    entry_transport entry_binds budget faithful observations ?_ .reachable unique tree errors
  intro context valid child within
  exact SourceCoreRecursiveNamedExpressionTreeBounds.concrete_preserves_at
    functions extension body bodyUninitialized bodyMissing faithful observations runtimeViews
    valid unique owners uninitialized missing budget child within

include definitions registered extension faithful observations runtimeViews unique uninitialized missing bodyUninitialized bodyMissing in
theorem concrete_reflects (budget : Nat)
    {context : SourceSemantics.Context} {scope : Scope} {mode : Bool}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : GenericImperativeFor.Tree layouts owner active frame globals onError values source expressionSyntax
      (fun context => CompatibleExpressionCalls.Tree (RecursiveNamedCatalog.Head [Header.of_body body] compilation source context)
        fuel values source context solved reasonAt) ambient.definitions administrative
      context scope (.statements mode statements) expected type code)
    (errors : GenericImperativeFor.Tree.ReachableErrors registry faults tree) :
    RecursiveNamedBoundedContracts.Below budget (fun size => RecursiveNamedLoopContracts.ReflectsAt functions program evidence
      (entry := protectedEntry [Header.of_body body] locations capturePrefix compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals) (administrative := administrative)
      size (scope := scope) mode statements expected type code) := by
  apply RecursiveNamedImperativeFor.reflectsAt_for functions definitions registered extension program evidence
    entry_transport entry_binds budget ?_ faithful observations .reachable runtimeViews unique tree errors
  intro context valid child smaller
  exact SourceCoreRecursiveNamedExpressionTreeBounds.concrete_reflects_at
    functions extension body bodyUninitialized bodyMissing faithful observations runtimeViews
    valid uninitialized missing budget child (Nat.le_of_lt smaller)

include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
/-- The inclusive endpoint used by a source-body strong induction. No N+1
budget and no callee law at N is supplied by this consumer. -/
theorem concrete_preserves_at_top (size : Nat)
    {context : SourceSemantics.Context} {scope : Scope} {mode : Bool}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : GenericImperativeFor.Tree layouts owner active frame globals onError values source expressionSyntax
      (fun context => CompatibleExpressionCalls.Tree (RecursiveNamedCatalog.Head [Header.of_body body] compilation source context)
        fuel values source context solved reasonAt) ambient.definitions administrative
      context scope (.statements mode statements) expected type code)
    (errors : GenericImperativeFor.Tree.ReachableErrors registry faults tree) :
    RecursiveNamedLoopContracts.PreservesAt functions program evidence
      (entry := protectedEntry [Header.of_body body] locations capturePrefix compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals) (administrative := administrative)
      size (scope := scope) mode statements expected type code :=
  concrete_preserves functions definitions registered extension faithful observations runtimeViews evidence unique owners
    uninitialized missing bodyUninitialized bodyMissing size tree errors size (Nat.le_refl size)

include definitions registered extension faithful observations runtimeViews unique uninitialized missing bodyUninitialized bodyMissing in
/-- A completed native body gives its own source size, without relating source
cost to the original native budget. -/
theorem concrete_native_only (budget size : Nat) (smaller : size < budget)
    {context : SourceSemantics.Context} {scope : Scope} {mode : Bool}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : GenericImperativeFor.Tree layouts owner active frame globals onError values source expressionSyntax
      (fun context => CompatibleExpressionCalls.Tree (RecursiveNamedCatalog.Head [Header.of_body body] compilation source context)
        fuel values source context solved reasonAt) ambient.definitions administrative
      context scope (.statements mode statements) expected type code)
    (errors : GenericImperativeFor.Tree.ReachableErrors registry faults tree) :
    RecursiveNamedLoopContracts.ReflectsAt functions program evidence
      (entry := protectedEntry [Header.of_body body] locations capturePrefix compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals) (administrative := administrative)
      size (scope := scope) mode statements expected type code :=
  concrete_reflects functions definitions registered extension faithful observations runtimeViews evidence unique
    uninitialized missing bodyUninitialized bodyMissing budget tree errors size smaller
include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
theorem terminal_block_preserves_at (size : Nat)
    {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {id : StatementId} {node : StatementNode}
    {rest : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {suffix : Expr}
    (exactUnique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) {statements : List StatementId} {innerCode : Expr}
    (form : node.form = .block statements)
    (inner : GenericImperativeFor.Tree layouts owner active frame globals onError values source expressionSyntax
      (fun context => CompatibleExpressionCalls.Tree (RecursiveNamedCatalog.Head [Header.of_body body] compilation source context)
        fuel values source context solved reasonAt) ambient.definitions administrative context scope
      (.statements false statements) expected type innerCode)
    (stops : GenericLexicalStatements.Stopped source statements)
    (issued : GenericLexicalStatements.IssuedSuffix source scope mode rest type suffix)
    (innerErrors : GenericImperativeFor.Tree.ReachableErrors registry faults inner) :
    RecursiveNamedLoopContracts.PreservesAt functions program evidence
      (entry := protectedEntry [Header.of_body body] locations capturePrefix compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals) (administrative := administrative)
      size (scope := scope) mode (id :: rest) expected type (LocalLoop.sequence type innerCode suffix) := by
  exact concrete_preserves_at_top functions definitions registered extension faithful observations runtimeViews evidence unique owners uninitialized missing bodyUninitialized bodyMissing size
    (.terminalBlock exactUnique found form inner stops issued) (.terminalBlock (unique := exactUnique) (found := found) (form := form) (stops := stops) (issued := issued) innerErrors)

include definitions registered extension faithful observations runtimeViews unique uninitialized missing bodyUninitialized bodyMissing in
theorem terminal_block_reflects_at (budget size : Nat) (smaller : size < budget)
    {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {id : StatementId} {node : StatementNode}
    {rest : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {suffix : Expr}
    (exactUnique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) {statements : List StatementId} {innerCode : Expr}
    (form : node.form = .block statements)
    (inner : GenericImperativeFor.Tree layouts owner active frame globals onError values source expressionSyntax
      (fun context => CompatibleExpressionCalls.Tree (RecursiveNamedCatalog.Head [Header.of_body body] compilation source context)
        fuel values source context solved reasonAt) ambient.definitions administrative context scope
      (.statements false statements) expected type innerCode)
    (stops : GenericLexicalStatements.Stopped source statements)
    (issued : GenericLexicalStatements.IssuedSuffix source scope mode rest type suffix)
    (innerErrors : GenericImperativeFor.Tree.ReachableErrors registry faults inner) :
    RecursiveNamedLoopContracts.ReflectsAt functions program evidence
      (entry := protectedEntry [Header.of_body body] locations capturePrefix compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals) (administrative := administrative)
      size (scope := scope) mode (id :: rest) expected type (LocalLoop.sequence type innerCode suffix) := by
  exact concrete_native_only functions definitions registered extension faithful observations runtimeViews evidence unique uninitialized missing bodyUninitialized bodyMissing budget size smaller
    (.terminalBlock exactUnique found form inner stops issued) (.terminalBlock (unique := exactUnique) (found := found) (form := form) (stops := stops) (issued := issued) innerErrors)

include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
theorem terminal_if_preserves_at (size : Nat)
    {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {id : StatementId} {node : StatementNode}
    {rest : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {suffix : Expr}
    (exactUnique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) {condition : ExpressionId} {conditionNode : ExpressionNode}
    {thenBody elseBody : List StatementId} {conditionCode thenCode elseCode : Expr}
    (form : node.form = .ifThen condition thenBody (some elseBody))
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionType : conditionNode.type = .bool)
    (conditionTree : CompatibleExpressionCalls.Tree (RecursiveNamedCatalog.Head [Header.of_body body] compilation source context)
      fuel values source context solved reasonAt scope condition ⟨.bool, conditionCode⟩)
    (thenTree : GenericImperativeFor.Tree layouts owner active frame globals onError values source expressionSyntax
      (fun context => CompatibleExpressionCalls.Tree (RecursiveNamedCatalog.Head [Header.of_body body] compilation source context)
        fuel values source context solved reasonAt) ambient.definitions administrative context scope
      (.statements false thenBody) expected type thenCode)
    (elseTree : GenericImperativeFor.Tree layouts owner active frame globals onError values source expressionSyntax
      (fun context => CompatibleExpressionCalls.Tree (RecursiveNamedCatalog.Head [Header.of_body body] compilation source context)
        fuel values source context solved reasonAt) ambient.definitions administrative context scope
      (.statements false elseBody) expected type elseCode)
    (thenStops : GenericLexicalStatements.Stopped source thenBody)
    (elseStops : GenericLexicalStatements.Stopped source elseBody)
    (issued : GenericLexicalStatements.IssuedSuffix source scope mode rest type suffix)
    (thenErrors : GenericImperativeFor.Tree.ReachableErrors registry faults thenTree)
    (elseErrors : GenericImperativeFor.Tree.ReachableErrors registry faults elseTree) :
    RecursiveNamedLoopContracts.PreservesAt functions program evidence
      (entry := protectedEntry [Header.of_body body] locations capturePrefix compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals) (administrative := administrative)
      size (scope := scope) mode (id :: rest) expected type (LocalLoop.sequence type (LocalLoop.conditional type conditionCode thenCode elseCode) suffix) := by
  exact concrete_preserves_at_top functions definitions registered extension faithful observations runtimeViews evidence unique owners uninitialized missing bodyUninitialized bodyMissing size
    (.terminalIf exactUnique found form conditionFound conditionType conditionTree thenTree elseTree thenStops elseStops issued) (.terminalIf (unique := exactUnique) (found := found) (form := form) (conditionFound := conditionFound) (conditionType := conditionType) (conditionTree := conditionTree) (thenStops := thenStops) (elseStops := elseStops) (issued := issued) thenErrors elseErrors)

include definitions registered extension faithful observations runtimeViews unique uninitialized missing bodyUninitialized bodyMissing in
theorem terminal_if_reflects_at (budget size : Nat) (smaller : size < budget)
    {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {id : StatementId} {node : StatementNode}
    {rest : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {suffix : Expr}
    (exactUnique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) {condition : ExpressionId} {conditionNode : ExpressionNode}
    {thenBody elseBody : List StatementId} {conditionCode thenCode elseCode : Expr}
    (form : node.form = .ifThen condition thenBody (some elseBody))
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionType : conditionNode.type = .bool)
    (conditionTree : CompatibleExpressionCalls.Tree (RecursiveNamedCatalog.Head [Header.of_body body] compilation source context)
      fuel values source context solved reasonAt scope condition ⟨.bool, conditionCode⟩)
    (thenTree : GenericImperativeFor.Tree layouts owner active frame globals onError values source expressionSyntax
      (fun context => CompatibleExpressionCalls.Tree (RecursiveNamedCatalog.Head [Header.of_body body] compilation source context)
        fuel values source context solved reasonAt) ambient.definitions administrative context scope
      (.statements false thenBody) expected type thenCode)
    (elseTree : GenericImperativeFor.Tree layouts owner active frame globals onError values source expressionSyntax
      (fun context => CompatibleExpressionCalls.Tree (RecursiveNamedCatalog.Head [Header.of_body body] compilation source context)
        fuel values source context solved reasonAt) ambient.definitions administrative context scope
      (.statements false elseBody) expected type elseCode)
    (thenStops : GenericLexicalStatements.Stopped source thenBody)
    (elseStops : GenericLexicalStatements.Stopped source elseBody)
    (issued : GenericLexicalStatements.IssuedSuffix source scope mode rest type suffix)
    (thenErrors : GenericImperativeFor.Tree.ReachableErrors registry faults thenTree)
    (elseErrors : GenericImperativeFor.Tree.ReachableErrors registry faults elseTree) :
    RecursiveNamedLoopContracts.ReflectsAt functions program evidence
      (entry := protectedEntry [Header.of_body body] locations capturePrefix compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals) (administrative := administrative)
      size (scope := scope) mode (id :: rest) expected type (LocalLoop.sequence type (LocalLoop.conditional type conditionCode thenCode elseCode) suffix) := by
  exact concrete_native_only functions definitions registered extension faithful observations runtimeViews evidence unique uninitialized missing bodyUninitialized bodyMissing budget size smaller
    (.terminalIf exactUnique found form conditionFound conditionType conditionTree thenTree elseTree thenStops elseStops issued) (.terminalIf (unique := exactUnique) (found := found) (form := form) (conditionFound := conditionFound) (conditionType := conditionType) (conditionTree := conditionTree) (thenStops := thenStops) (elseStops := elseStops) (issued := issued) thenErrors elseErrors)

end Concrete

private def content : String := String.intercalate "\n" [
  "function both(flag: Bool) returns (Word) { if (flag) { for (let i = 0; i < 1; i += 1) {} return 7; } else { while (false) {} return 9; } }",
  "function block() returns (Word) { { for (let i = 0; i < 1; i += 1) {} return 11; } }",
  "function nested(flag: Bool) returns (Word) { let saved = 13; { if (flag) { for (; true; ) { break; } return saved; } else { while (true) { break; } return 17; } } }",
  "function inFor(flag: Bool) returns (Word) { for (; true; ) { if (flag) { return 43; } else { return 47; } let gap: Word; gap; } return 99; }",
  "function inWhile(flag: Bool) returns (Word) { while (true) { { if (flag) { return 53; } else { return 59; } } let gap: Word; gap; } return 99; }",
  "function reachable(flag: Bool) returns (Word) { if (flag) { return 19; } return 23; }",
  "function dead(flag: Bool) returns (Word) { if (flag) { for (; true; ) { break; } return 29; } else { while (false) {} return 31; } let gap: Word; gap; }",
  "function failed(flag: Bool) returns (Word) { let prior = 37; if (flag) { for (; false; ) {} let gap: Word; return gap; } else { while (false) {} return 41; } let skipped = 99; return skipped; }",
  "function unit() returns (Unit) { { for (; true; ) { break; } return; } let gap: Word; gap; }"
]
private def w (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue

private def inspect (compiled : SourceCoreUnifiedCompilation.Compiled) : IO Unit := do
  let prepared := compiled.indexed
  let diagnostics ← match prepared.base.diagnostics with
    | none => throw (IO.userError "reachable imperative integration missing diagnostics")
    | some diagnostic => pure diagnostic.program
  let diagnostics := match prepared.base.callableContext with
    | none => diagnostics
    | some native => {diagnostics with rootTable := native.diagnostics.rootTable}
  let parents ← get "reachable imperative integration parent contexts"
    (SourceCoreStageCodebook.prepareContexts prepared.base.sourceProgram prepared.base.plan
      (prepared.base.locals.bindings.flatMap (·.instances)))
  let mut terminalAnnotations := 0
  let mut reachableAnnotations := 0
  let mut deadSuffixes := 0
  let mut forNodes := 0
  let mut whileNodes := 0
  for named in prepared.base.functions do
    let actual := (CallableIndexedNamedGeneration.representation prepared).atContext named.signature.key []
    let own ← match diagnostics.base.find? named.signature.key with
      | none => throw (IO.userError "reachable imperative integration missing own diagnostics")
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
    let statements ← get "reachable imperative integration actual roots"
      (source.roots.mapM (m := Except SourceCoreGeneralFunctions.Error) (fun
        | .statement id => pure id | .expression id => throw (.expectedStatementRoot id)))
    let body ← get "reachable imperative integration actual complete body"
      (SourceCoreLoops.lowerStatementsWithPolicy policy prepared.fuel source scope statements
        named.signature.resultType reasonAt own.fellThroughReason own.table.escapedReason)
    let same ← get "reachable imperative integration actual compiler body"
      (CallableIndexedNamedGeneration.bodyAction prepared named diagnostics parents own statements)
    require (body == same) "reachable imperative integration changed actual compiler body"
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
          | _ => pure ()
      | _ => pure ()
    match statements with
    | id :: rest =>
        let node ← match source.lookupStatement? id with
          | none => throw (IO.userError "reachable imperative integration root lookup missing")
          | some node => pure node
        match node.form with
        | .ifThen condition left (some right) =>
            let (_, _) ← get "reachable imperative integration actual statement read" (policy.readStatement source id)
            let condition ← get "reachable imperative integration actual condition" (lower (prepared.fuel - 1) source scope condition reasonAt)
            let leftCode ← get "reachable imperative integration actual left"
              (SourceCoreLoops.lowerFlowStatementsWithPolicy policy (prepared.fuel - 1) source scope left
                named.signature.resultType reasonAt false own.table.escapedReason)
            let rightCode ← get "reachable imperative integration actual right"
              (SourceCoreLoops.lowerFlowStatementsWithPolicy policy (prepared.fuel - 1) source scope right
                named.signature.resultType reasonAt false own.table.escapedReason)
            let suffix ← get "reachable imperative integration emitted suffix"
              (SourceCoreLoops.lowerFlowStatementsWithPolicy policy (prepared.fuel - 1) source scope rest
                named.signature.resultType reasonAt true own.table.escapedReason)
            let whole ← get "reachable imperative integration whole flow"
              (SourceCoreLoops.lowerFlowStatementsWithPolicy policy prepared.fuel source scope statements
                named.signature.resultType reasonAt true own.table.escapedReason)
            require (whole == LocalLoop.sequence named.signature.resultType
              (LocalLoop.conditional named.signature.resultType condition.expression leftCode rightCode) suffix)
              "reachable imperative integration did not retain original emitted suffix"
            if !rest.isEmpty then deadSuffixes := deadSuffixes + 1
        | .block inner =>
            let innerCode ← get "reachable imperative integration actual block child"
              (SourceCoreLoops.lowerFlowStatementsWithPolicy policy (prepared.fuel - 1) source scope inner
                named.signature.resultType reasonAt false own.table.escapedReason)
            let suffix ← get "reachable imperative integration emitted block suffix"
              (SourceCoreLoops.lowerFlowStatementsWithPolicy policy (prepared.fuel - 1) source scope rest
                named.signature.resultType reasonAt true own.table.escapedReason)
            let whole ← get "reachable imperative integration whole block flow"
              (SourceCoreLoops.lowerFlowStatementsWithPolicy policy prepared.fuel source scope statements
                named.signature.resultType reasonAt true own.table.escapedReason)
            require (whole == LocalLoop.sequence named.signature.resultType innerCode suffix)
              "reachable imperative integration did not retain original block suffix"
        | _ => pure ()
    | [] => pure ()
  require (terminalAnnotations == 9 && reachableAnnotations == 1 && deadSuffixes == 1 && forNodes == 7 && whileNodes == 5)
    s!"reachable continuation fixture coverage changed: {terminalAnnotations}/{reachableAnnotations}/{deadSuffixes}/{forNodes}/{whileNodes}"

private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (arguments : List SourceTypedRuntime.Value) (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) : IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel initial
  pure (← get "reachable imperative integration public resume" (first.resume 300000)).observation

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "reachable imperative integration" content
    ["both", "block", "nested", "inFor", "inWhile", "reachable", "dead", "failed", "unit"]
  inspect compiled
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.word, some (w 821)⟩]}
  let successes : List (String × List SourceTypedRuntime.Value × SourceTypedRuntime.Value × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("both", [.bool true], w 7, [(.bool, some (.bool true)), (.word, some (w 1))]),
    ("both", [.bool false], w 9, [(.bool, some (.bool false))]),
    ("block", [], w 11, [(.word, some (w 1))]),
    ("nested", [.bool true], w 13, [(.bool, some (.bool true)), (.word, some (w 13))]),
    ("nested", [.bool false], w 17, [(.bool, some (.bool false)), (.word, some (w 13))]),
    ("inFor", [.bool true], w 43, [(.bool, some (.bool true))]),
    ("inFor", [.bool false], w 47, [(.bool, some (.bool false))]),
    ("inWhile", [.bool true], w 53, [(.bool, some (.bool true))]),
    ("inWhile", [.bool false], w 59, [(.bool, some (.bool false))]),
    ("reachable", [.bool true], w 19, [(.bool, some (.bool true))]),
    ("reachable", [.bool false], w 23, [(.bool, some (.bool false))]),
    ("dead", [.bool true], w 29, [(.bool, some (.bool true))]),
    ("dead", [.bool false], w 31, [(.bool, some (.bool false))]),
    ("failed", [.bool false], w 41, [(.bool, some (.bool false)), (.word, some (w 37))]),
    ("unit", [], .unit, [])]
  let baselines ← successes.mapM (fun test => finish compiled test.1 test.2.1 300000 initial)
  let failure ← finish compiled "failed" [.bool true] 300000 initial
  for fuel in [0, 31, 300000] do
    for ((name, arguments, expected, expectedCells), baseline) in successes.zip baselines do
      let observed ← finish compiled name arguments fuel initial
      require (reprStr observed == reprStr baseline) s!"reachable imperative integration full resume changed {name}"
      match observed with
      | .done result final =>
          require (reprStr result == reprStr expected) s!"reachable imperative integration result changed {name}"
          require (reprStr final.heap == reprStr (initial.heap ++ expectedCells.map (fun (type, value) => ⟨type, value⟩)))
            s!"reachable imperative integration ordered heap/dead suffix changed {name}"
      | other => throw (IO.userError s!"reachable imperative integration expected done {name}: {reprStr other}")
    let observed ← finish compiled "failed" [.bool true] fuel initial
    require (reprStr observed == reprStr failure) "reachable imperative integration full fault resume changed"
    match observed with
    | .fault (.uninitializedLocal _) final =>
        require (reprStr final.heap == reprStr (initial.heap ++ [⟨.bool, some (.bool true)⟩, ⟨.word, some (w 37)⟩, ⟨.word, none⟩]))
          "reachable imperative integration fault executed a dead suffix or changed its prefix"
    | other => throw (IO.userError s!"reachable imperative integration expected head fault: {reprStr other}")
  IO.println "reachable imperative integration: same recursive for/while grammar, non-Unit terminal annotations, source stops, original native child, emitted dead suffix, ordered full heaps and public resume GREEN"

end Tests.SourceCoreReachableImperativeForStatements
