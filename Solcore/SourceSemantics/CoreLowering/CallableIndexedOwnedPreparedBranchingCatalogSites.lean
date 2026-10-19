import Solcore.SourceSemantics.CoreLowering.PreparedBranchingCatalogSites
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBranchingTree
import Solcore.SourceSemantics.CoreLowering.GenericImperativeForMatchEmbedding

/-! Bare assignment diagnostics retain their actual fixed fault interpretation.
The original compiler tree and header diagnostic receipts remain paired. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedBranchingCatalogSites
open Core Frontend SourceInference SourceCoreCompatibleDataPlaces CompatiblePayload
open CallableIndexedOwnedPreparedStagedBranchingTree
open GenericImperativeMatch

private theorem empty_steps
    {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {context : SourceSemantics.Context} {certificate : GenericExpressionMeaning.Certificate}
    {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context} {definitions : DataEnvironment}
    {place : PlaceResolution} {prepared : SourceCoreCompatibleDataPlaces.Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {leaf : TypeSystem.Ty}
    (shape : GenericAssignmentStatements.Shape values source context certificate scope administrative
      definitions place prepared codes leaf) (bare : place.projections = []) : prepared.steps = [] := by
  cases shape with
  | bare _ layout => exact layout.steps
  | projected layout _ =>
    have length := CompatiblePlaceCompilerCertificates.PreparedPath.steps_length layout.path
    rw [bare, List.length_nil] at length
    exact False.elim (layout.nonempty (List.eq_nil_of_length_eq_zero length))

variable {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {definitions : DataEnvironment} {administrative : Core.Context}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {position : GenericImperativeMatch.Position} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}

/-- A bare target has no projection/default errors; operand errors retain their
actual diagnostic law. -/
private theorem reachable_bare
    {certificate : GenericExpressionMeaning.Certificate} {assignment : AssignmentResolution}
    {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    {head : GenericAssignmentStatements.Head values source context certificate scope administrative definitions assignment operator rhs}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (empty : head.prepared.steps = [])
    (operands : AssignmentOperandDiagnostics.OperandsLaw faults operator head.invalid) :
    head.ReachableErrors registry faults := by
  refine ⟨?_, fun nonempty => False.elim (nonempty empty), operands⟩
  intro root resolved reason token count fault
  rw [empty] at fault
  cases fault

theorem assignment_site
    {certificate : GenericExpressionMeaning.Certificate} {assignment : AssignmentResolution}
    {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    {head : GenericAssignmentStatements.Head values source context certificate scope administrative definitions assignment operator rhs}
    {site : SourceCoreElaboration.ErrorSite} {fuel : Nat}
    (origin : AssignmentDiagnosticOrigins.Occurs source site assignment operator rhs)
    (signatures : context.signatures = values.checked.signatures)
    (retained : head.PreparedAt site fuel (invalidProjection site assignment.target.root)
      (missingDefault site assignment.target.root))
    (operands : AssignmentOperandDiagnostics.OperandsLaw faults operator head.invalid)
    (registry : SourceCoreRawMetadata.Registry) :
    PreparedBranchingCatalogSites.AssignmentSite invalidProjection missingDefault registry faults head := by
  by_cases bare : assignment.target.projections = []
  · exact .existing (reachable_bare (empty_steps head.shape bare) operands)
  · exact .projected origin signatures bare retained operands

/-- The compiler retains the exact tree and its real catalog interpretation.
Bare routes do not constrain the registry. -/
structure Collected
    (invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word)
    (missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word)
    (faults : FunctionCalls.FaultRep)
    (layouts : SourceCoreAllocationLayouts.Prepared) (owner : SourceSpecialization.SpecializationKey)
    (active : TypeSystem.Substitution) (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (values : SourceCoreCompatibleValues.Context) (source : TypedSource)
    (expressionSyntax : ExpressionId → Prop)
    (certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate)
    (definitions : DataEnvironment) (administrative : Core.Context)
    (context : SourceSemantics.Context) (scope : SourceCoreLocalCell.Scope)
    (position : GenericImperativeMatch.Position) (expected : TypeSystem.Ty) (type : Ty) (code : Expr) : Prop where
  tree : GenericImperativeMatch.Tree layouts owner active frame globals onError values source
    expressionSyntax certificates definitions administrative context scope position expected type code
  sites : ∀ registry, PreparedBranchingCatalogSites.CatalogSites invalidProjection missingDefault registry faults tree

namespace Collected

 theorem breaking {context scope mode id node rest expected type}
      (found : source.lookupStatement? id = some node) (form : node.form = .breakStmt) :
      Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode (id :: rest)) expected type (LocalLoop.breaking type) := by
  refine ⟨.breaking found form, ?_⟩
  intro registry
  exact .breaking (found := found) (form := form)

 theorem continuing {context scope mode id node rest expected type}
      (found : source.lookupStatement? id = some node) (form : node.form = .continueStmt) :
      Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode (id :: rest)) expected type (LocalLoop.continuing type) := by
  refine ⟨.continuing found form, ?_⟩
  intro registry
  exact .continuing (found := found) (form := form)

 theorem body {context scope mode statements expected type code}
      (syntaxTree : GenericLexicalStatements.Syntax source expressionSyntax context mode statements expected)
      (body : GenericLexicalStatements.Tree layouts owner active frame globals onError values source certificates context scope mode statements expected type code) :
      Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode statements) expected type code := by
  refine ⟨.body syntaxTree body, ?_⟩
  intro registry
  exact .body (syntaxTree := syntaxTree) (body := body)

 theorem uninitialized {context nextContext scope mode id node binder rest expected type body payload}
      (found : source.lookupStatement? id = some node) (form : node.form = .letDecl binder none)
      (monomorphic : binder.scheme.quantified = [])
      (extended : BinderExtends source.owner context binder nextContext)
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (projected : values.checked.catalog.project binder.scheme.body = .ok payload)
      (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (absentRequest source scope binder payload))
      (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
        (layouts.allocatorAt owner active onError) (absentRequest source scope binder payload))
      (same : annotation.original = allocation.expression)
      (remaining : Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        nextContext ((binder.id, payload) :: scope) (.statements mode rest) expected type body) :
      Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode (id :: rest)) expected type (.letE annotation.expression body) := by
  refine ⟨.uninitialized found form monomorphic extended ordinary projected allocation annotation same remaining.tree, ?_⟩
  intro registry
  exact .uninitialized (found := found) (form := form) (monomorphic := monomorphic) (extended := extended) (ordinary := ordinary) (projected := projected) (allocation := allocation) (annotation := annotation) (same := same) (remaining := remaining.tree) (remaining.sites registry)

 theorem initialized {context nextContext scope mode id node binder initializer initializerNode lowered body rest expected type}
      (found : source.lookupStatement? id = some node) (form : node.form = .letDecl binder (some initializer))
      (monomorphic : binder.scheme.quantified = [])
      (extended : BinderExtends source.owner context binder nextContext)
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (initializerFound : source.lookupExpression? initializer = some initializerNode)
      (sourceType : initializerNode.type = binder.scheme.body)
      (initial : certificates context scope initializer lowered)
      (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (initializedRequest source scope binder lowered.type))
      (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
        (layouts.allocatorAt owner active onError) (initializedRequest source scope binder lowered.type))
      (same : annotation.original = allocation.expression)
      (remaining : Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative nextContext ((binder.id, lowered.type) :: scope) (.statements mode rest) expected type body) :
      Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode (id :: rest)) expected type (sequence type lowered.expression annotation.expression body) := by
  refine ⟨.initialized found form monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining.tree, ?_⟩
  intro registry
  exact .initialized (found := found) (form := form) (monomorphic := monomorphic) (extended := extended) (ordinary := ordinary) (initializerFound := initializerFound) (sourceType := sourceType) (initial := initial) (allocation := allocation) (annotation := annotation) (same := same) (remaining := remaining.tree) (remaining.sites registry)

 theorem discard {context scope mode id node expression expressionNode semicolon rest expected lowered type body}
      (found : source.lookupStatement? id = some node) (form : node.form = .expression expression semicolon)
      (notTail : (!semicolon && mode && rest.isEmpty) = false)
      (expressionFound : source.lookupExpression? expression = some expressionNode)
      (value : certificates context scope expression lowered)
      (remaining : Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode rest) expected type body) :
      Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode (id :: rest)) expected type
        (LocalSequence.discard (LocalLoop.controlType type) lowered.expression body) := by
  refine ⟨.discard found form notTail expressionFound value remaining.tree, ?_⟩
  intro registry
  exact .discard (found := found) (form := form) (notTail := notTail) (expressionFound := expressionFound) (value := value) (remaining := remaining.tree) (remaining.sites registry)

 theorem block {context scope mode id node statements rest expected type innerCode body}
      (found : source.lookupStatement? id = some node) (form : node.form = .block statements)
      (inner : Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements false statements) expected type innerCode)
      (remaining : Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode rest) expected type body) :
      Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode (id :: rest)) expected type
        (LocalLoop.sequence type innerCode body) := by
  refine ⟨.block found form inner.tree remaining.tree, ?_⟩
  intro registry
  exact .block (found := found) (form := form) (inner := inner.tree) (remaining := remaining.tree) (inner.sites registry) (remaining.sites registry)

 theorem ifThen {context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body}
      (found : source.lookupStatement? id = some node) (form : node.form = .ifThen condition thenBody elseBody)
      (conditionFound : source.lookupExpression? condition = some conditionNode)
      (conditionType : conditionNode.type = .bool)
      (conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩)
      (thenTree : Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements false thenBody) expected type thenCode)
      (elseTree : Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements false (elseBody.getD [])) expected type elseCode)
      (remaining : Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode rest) expected type body) :
      Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode (id :: rest)) expected type
        (LocalLoop.sequence type (LocalLoop.conditional type conditionCode thenCode elseCode) body) := by
  refine ⟨.ifThen found form conditionFound conditionType conditionTree thenTree.tree elseTree.tree remaining.tree, ?_⟩
  intro registry
  exact .ifThen (found := found) (form := form) (conditionFound := conditionFound) (conditionType := conditionType) (conditionTree := conditionTree) (thenTree := thenTree.tree) (elseTree := elseTree.tree) (remaining := remaining.tree) (thenTree.sites registry) (elseTree.sites registry) (remaining.sites registry)

 theorem whileLoop {context scope mode id node condition conditionNode statements rest expected type conditionCode loopCode body selfReason}
      (found : source.lookupStatement? id = some node) (form : node.form = .whileLoop condition statements)
      (conditionFound : source.lookupExpression? condition = some conditionNode)
      (conditionType : conditionNode.type = .bool)
      (conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩)
      (loopBody : Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements false statements) expected type loopCode)
      (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        (LocalLoop.whileLoop type conditionCode loopCode selfReason) (LocalLoop.resultType type) definitions)
      (remaining : Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode rest) expected type body) :
      Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode (id :: rest)) expected type
        (LocalLoop.sequence type (LocalLoop.whileLoop type conditionCode loopCode selfReason) body) := by
  refine ⟨.whileLoop found form conditionFound conditionType conditionTree loopBody.tree nativeTyped remaining.tree, ?_⟩
  intro registry
  exact .whileLoop (found := found) (form := form) (conditionFound := conditionFound) (conditionType := conditionType) (conditionTree := conditionTree) (loopBody := loopBody.tree) (nativeTyped := nativeTyped) (remaining := remaining.tree) (loopBody.sites registry) (remaining.sites registry)

 theorem assign {context scope mode id node assignment operator rhs rest expected type body}
      (found : source.lookupStatement? id = some node) (form : node.form = .assignValue assignment operator rhs)
      (head : GenericAssignmentStatements.Head values source context (certificates context) scope administrative definitions assignment operator rhs)
      (remaining : Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode rest) expected type body)
    (operands : AssignmentOperandDiagnostics.OperandsLaw faults operator head.invalid)
      (bare : assignment.target.projections = []) :
      Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode (id :: rest)) expected type (head.emit body (LocalLoop.controlType type)) := by
  refine ⟨.assign found form head remaining.tree, ?_⟩
  intro registry
  exact .assign (found := found) (form := form) (head := head) (remaining := remaining.tree) (remaining.sites registry) (.existing (reachable_bare (empty_steps head.shape bare) operands))

 theorem assignPrepared {context scope mode id node assignment operator rhs rest expected type body}
      (found : source.lookupStatement? id = some node) (form : node.form = .assignValue assignment operator rhs)
      (head : GenericAssignmentStatements.Head values source context (certificates context) scope administrative definitions assignment operator rhs)
      (remaining : Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode rest) expected type body)
    (site : ∀ registry, PreparedBranchingCatalogSites.AssignmentSite invalidProjection missingDefault registry faults head) :
      Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode (id :: rest)) expected type (head.emit body (LocalLoop.controlType type)) := by
  refine ⟨.assign found form head remaining.tree, ?_⟩
  intro registry
  exact .assign (found := found) (form := form) (head := head) (remaining := remaining.tree) (remaining.sites registry) (site registry)

 theorem bitNot {context scope mode id node assignment rest expected type body}
      (found : source.lookupStatement? id = some node) (form : node.form = .assignBitNot assignment)
      (head : CompatibleBitNotStatements.Head context scope assignment)
      (remaining : Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode rest) expected type body)
    (unary : head.Errors faults) :
      Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode (id :: rest)) expected type (head.emit body (LocalLoop.controlType type)) := by
  refine ⟨.bitNot found form head remaining.tree, ?_⟩
  intro registry
  exact .bitNot (found := found) (form := form) (head := head) (remaining := remaining.tree) (remaining.sites registry) unary

 theorem bitNotProjected {context scope mode id node assignment rest expected type body}
      (found : source.lookupStatement? id = some node) (form : node.form = .assignBitNot assignment)
      (head : CompatibleProjectedBitNotStatements.Head values source context (certificates context) scope administrative definitions assignment)
      (remaining : Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode rest) expected type body)
    (unary : PreparedBranchingCatalogSites.UnarySite invalidProjection missingDefault head) :
      Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode (id :: rest)) expected type (head.emit body (LocalLoop.controlType type)) := by
  refine ⟨.bitNotProjected found form head remaining.tree, ?_⟩
  intro registry
  exact .bitNotProjected (found := found) (form := form) (head := head) (remaining := remaining.tree) (remaining.sites registry) unary

 theorem matchWith {context scope mode id node resolution scrutineeNode rest expected type matched body selfReason control caseFacts}
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
        Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
          childContext request.scope (.statements false request.statements) expected type request.code)
      (remaining : Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode rest) expected type body)
    (catalog : SignatureCatalogWellFormed values.checked.signatures)
    (patternContext : GenericImperativeMatch.Tree.MatchContextFields compilation context) :
      Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode (id :: rest)) expected type (LocalLoop.sequence type matched body) := by
  refine ⟨.matchWith found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary (fun request member childContext related => (children request member childContext related).tree) remaining.tree, ?_⟩
  intro registry
  exact .matchWith (found := found) (form := form) (scrutineeFound := scrutineeFound) (scrutineeTyped := scrutineeTyped) (casesTyped := casesTyped) (defaultTyped := defaultTyped) (compilation := compilation) (sameValues := sameValues) (sameDefinitions := sameDefinitions) (allocator := allocator) (requests := requests) (receipt := receipt) (ordinary := ordinary) (children := (fun request member childContext related => (children request member childContext related).tree)) (remaining := remaining.tree) catalog patternContext (fun request member childContext related => (children request member childContext related).sites registry) (remaining.sites registry)

 theorem terminalBlock {context scope mode id node statements rest expected type innerCode suffix}
      (unique : NodeOccurrencesUnique source)
      (found : source.lookupStatement? id = some node) (form : node.form = .block statements)
      (inner : Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements false statements) expected type innerCode)
      (stops : GenericLexicalStatements.Stopped source statements)
      (issued : GenericLexicalStatements.IssuedSuffix source scope mode rest type suffix) :
      Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode (id :: rest)) expected type
        (LocalLoop.sequence type innerCode suffix) := by
  refine ⟨.terminalBlock unique found form inner.tree stops issued, ?_⟩
  intro registry
  exact .terminalBlock (unique := unique) (found := found) (form := form) (inner := inner.tree) (stops := stops) (issued := issued) (inner.sites registry)

 theorem terminalIf {context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode suffix}
      (unique : NodeOccurrencesUnique source)
      (found : source.lookupStatement? id = some node) (form : node.form = .ifThen condition thenBody (some elseBody))
      (conditionFound : source.lookupExpression? condition = some conditionNode)
      (conditionType : conditionNode.type = .bool)
      (conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩)
      (thenTree : Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements false thenBody) expected type thenCode)
      (elseTree : Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements false elseBody) expected type elseCode)
      (thenStops : GenericLexicalStatements.Stopped source thenBody) (elseStops : GenericLexicalStatements.Stopped source elseBody)
      (issued : GenericLexicalStatements.IssuedSuffix source scope mode rest type suffix) :
      Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode (id :: rest)) expected type
        (LocalLoop.sequence type (LocalLoop.conditional type conditionCode thenCode elseCode) suffix) := by
  refine ⟨.terminalIf unique found form conditionFound conditionType conditionTree thenTree.tree elseTree.tree thenStops elseStops issued, ?_⟩
  intro registry
  exact .terminalIf (unique := unique) (found := found) (form := form) (conditionFound := conditionFound) (conditionType := conditionType) (conditionTree := conditionTree) (thenTree := thenTree.tree) (elseTree := elseTree.tree) (thenStops := thenStops) (elseStops := elseStops) (issued := issued) (thenTree.sites registry) (elseTree.sites registry)

 theorem terminalMatch {context scope mode id node resolution scrutineeNode rest expected type matched suffix selfReason control caseFacts}
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
        Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
          childContext request.scope (.statements false request.statements) expected type request.code)
      (stops : ReachableMatchContinuations.DefaultStopped source id resolution)
      (issued : GenericLexicalStatements.IssuedSuffix source scope mode rest type suffix)
    (catalog : SignatureCatalogWellFormed values.checked.signatures)
    (patternContext : GenericImperativeMatch.Tree.MatchContextFields compilation context) :
      Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode (id :: rest)) expected type (LocalLoop.sequence type matched suffix) := by
  refine ⟨.terminalMatch unique found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary (fun request member childContext related => (children request member childContext related).tree) stops issued, ?_⟩
  intro registry
  exact .terminalMatch (unique := unique) (found := found) (form := form) (scrutineeFound := scrutineeFound) (scrutineeTyped := scrutineeTyped) (casesTyped := casesTyped) (defaultTyped := defaultTyped) (compilation := compilation) (sameValues := sameValues) (sameDefinitions := sameDefinitions) (allocator := allocator) (requests := requests) (receipt := receipt) (ordinary := ordinary) (children := (fun request member childContext related => (children request member childContext related).tree)) (stops := stops) (issued := issued) catalog patternContext (fun request member childContext related => (children request member childContext related).sites registry)


 theorem forLoop {context scope mode id node initializer condition post statements rest expected type initialCode body}
      (found : source.lookupStatement? id = some node) (form : node.form = .forLoop initializer condition post statements)
      (initial : Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.initializers initializer condition post statements) expected type initialCode)
      (remaining : Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode rest) expected type body) :
      Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode (id :: rest)) expected type (LocalLoop.sequence type initialCode body) := by
  refine ⟨.forLoop found form initial.tree remaining.tree, ?_⟩
  intro registry
  exact .forLoop (found := found) (form := form) (initial := initial.tree)
    (remaining := remaining.tree) (initial.sites registry) (remaining.sites registry)


 theorem initializersDone {context scope condition conditionNode post statements expected type conditionCode bodyCode postCode selfReason}
      (conditionFound : source.lookupExpression? condition = some conditionNode)
      (conditionType : conditionNode.type = .bool)
      (conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩)
      (loopBody : Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements false statements) expected type bodyCode)
      (postTree : GenericForHeader.Tree layouts owner active frame globals onError values source certificates definitions administrative
        type (TypedForHeader.Fallthrough type) context scope post postCode)
      (postSites : ∀ registry, PreparedBranchingCatalogSites.HeaderSites invalidProjection missingDefault registry faults postTree)
      (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        (LocalLoop.iterate type conditionCode bodyCode postCode selfReason) (LocalLoop.resultType type) definitions) :
      Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.initializers [] condition post statements) expected type
        (LocalLoop.iterate type conditionCode bodyCode postCode selfReason) := by
  refine ⟨.initializersDone conditionFound conditionType conditionTree loopBody.tree postTree nativeTyped, ?_⟩
  intro registry
  exact .initializersDone (conditionFound := conditionFound) (conditionType := conditionType)
    (conditionTree := conditionTree) (loopBody := loopBody.tree) (postTree := postTree)
    (nativeTyped := nativeTyped) (loopBody.sites registry) (postSites registry)


 theorem initializerUninitialized {context nextContext scope binder rest body payload condition post statements expected type}
      (monomorphic : binder.scheme.quantified = [])
      (extended : BinderExtends source.owner context binder nextContext)
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (projected : values.checked.catalog.project binder.scheme.body = .ok payload)
      (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (absentRequest source scope binder payload))
      (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
        (layouts.allocatorAt owner active onError) (absentRequest source scope binder payload))
      (same : annotation.original = allocation.expression)
      (remaining : Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        nextContext ((binder.id, payload) :: scope) (.initializers rest condition post statements) expected type body) :
      Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.initializers (.letDecl binder none :: rest) condition post statements) expected type (.letE annotation.expression body) := by
  refine ⟨.initializerUninitialized monomorphic extended ordinary projected allocation annotation same remaining.tree, ?_⟩
  intro registry
  exact .initializerUninitialized (monomorphic := monomorphic) (extended := extended)
    (ordinary := ordinary) (projected := projected) (allocation := allocation) (annotation := annotation)
    (same := same) (remaining := remaining.tree) (remaining.sites registry)


 theorem initializerInitialized {context nextContext scope binder initializer initializerNode lowered body rest condition post statements expected type}
      (monomorphic : binder.scheme.quantified = [])
      (extended : BinderExtends source.owner context binder nextContext)
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (initializerFound : source.lookupExpression? initializer = some initializerNode)
      (sourceType : initializerNode.type = binder.scheme.body)
      (initial : certificates context scope initializer lowered)
      (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (initializedRequest source scope binder lowered.type))
      (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
        (layouts.allocatorAt owner active onError) (initializedRequest source scope binder lowered.type))
      (same : annotation.original = allocation.expression)
      (remaining : Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        nextContext ((binder.id, lowered.type) :: scope) (.initializers rest condition post statements) expected type body) :
      Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.initializers (.letDecl binder (some initializer) :: rest) condition post statements) expected type (sequence type lowered.expression annotation.expression body) := by
  refine ⟨.initializerInitialized monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining.tree, ?_⟩
  intro registry
  exact .initializerInitialized (monomorphic := monomorphic) (extended := extended)
    (ordinary := ordinary) (initializerFound := initializerFound) (sourceType := sourceType)
    (initial := initial) (allocation := allocation) (annotation := annotation)
    (same := same) (remaining := remaining.tree) (remaining.sites registry)


 theorem initializerDiscard {context scope expression expressionNode rest lowered body condition post statements expected type}
      (found : source.lookupExpression? expression = some expressionNode)
      (value : certificates context scope expression lowered)
      (remaining : Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.initializers rest condition post statements) expected type body) :
      Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.initializers (.expression expression :: rest) condition post statements) expected type (LocalSequence.discard (LocalLoop.controlType type) lowered.expression body) := by
  refine ⟨.initializerDiscard found value remaining.tree, ?_⟩
  intro registry
  exact .initializerDiscard (found := found) (value := value) (remaining := remaining.tree)
    (remaining.sites registry)


 theorem initializerAssign {context scope assignment operator rhs rest body condition post statements expected type}
      (head : GenericAssignmentStatements.Head values source context (certificates context) scope administrative definitions assignment operator rhs)
      (remaining : Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.initializers rest condition post statements) expected type body)
      (operands : AssignmentOperandDiagnostics.OperandsLaw faults operator head.invalid)
      (bare : assignment.target.projections = []) :
      Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.initializers (.assignValue assignment operator rhs :: rest) condition post statements) expected type (head.emit body (LocalLoop.controlType type)) := by
  refine ⟨.initializerAssign head remaining.tree, ?_⟩
  intro registry
  exact .initializerAssign (head := head) (remaining := remaining.tree)
    (remaining.sites registry)
    (.existing (reachable_bare (empty_steps head.shape bare) operands))
 theorem initializerAssignPrepared {context scope assignment operator rhs rest body condition post statements expected type}
      (head : GenericAssignmentStatements.Head values source context (certificates context) scope administrative definitions assignment operator rhs)
      (remaining : Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.initializers rest condition post statements) expected type body)
      (site : ∀ registry, PreparedBranchingCatalogSites.AssignmentSite invalidProjection missingDefault registry faults head) :
      Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.initializers (.assignValue assignment operator rhs :: rest) condition post statements) expected type (head.emit body (LocalLoop.controlType type)) := by
  refine ⟨.initializerAssign head remaining.tree, ?_⟩
  intro registry
  exact .initializerAssign (head := head) (remaining := remaining.tree)
    (remaining.sites registry)
    (site registry)
 theorem initializerBitNot {context scope assignment rest body condition post statements expected type}
      (head : CompatibleBitNotStatements.Head context scope assignment)
      (remaining : Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.initializers rest condition post statements) expected type body)
      (unary : head.Errors faults) :
      Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.initializers (.assignBitNot assignment :: rest) condition post statements) expected type (head.emit body (LocalLoop.controlType type)) := by
  refine ⟨.initializerBitNot head remaining.tree, ?_⟩
  intro registry
  exact .initializerBitNot (head := head) (remaining := remaining.tree)
    (remaining.sites registry)
    unary

 theorem initializerBitNotProjected {context scope assignment rest body condition post statements expected type}
      (head : CompatibleProjectedBitNotStatements.Head values source context (certificates context) scope administrative definitions assignment)
      (remaining : Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.initializers rest condition post statements) expected type body)
      (unary : PreparedBranchingCatalogSites.UnarySite invalidProjection missingDefault head) :
      Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.initializers (.assignBitNot assignment :: rest) condition post statements) expected type (head.emit body (LocalLoop.controlType type)) := by
  refine ⟨.initializerBitNotProjected head remaining.tree, ?_⟩
  intro registry
  exact .initializerBitNotProjected (head := head) (remaining := remaining.tree)
    (remaining.sites registry)
    unary

end Collected
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedBranchingCatalogSites
