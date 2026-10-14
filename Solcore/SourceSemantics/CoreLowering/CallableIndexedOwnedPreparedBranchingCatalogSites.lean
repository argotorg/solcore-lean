import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBranchingTree
import Solcore.SourceSemantics.CoreLowering.GenericImperativeForMatchEmbedding

/-! Bare plain assignments have no reachable place or operand diagnostic.
The original fragment shape supplies catalog sites for the same compiler tree. -/
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

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {definitions : DataEnvironment} {administrative : Core.Context}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {position : GenericImperativeMatch.Position} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}

/-- The compiler retains the exact Tree and its static catalog obligations
jointly. Registry and fault parameters remain free because this fragment has no
reachable assignment diagnostic sites. -/
structure Collected
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
  sites : ∀ registry faults, tree.CatalogSites .reachable registry faults

/-- Every header assignment in the accepted fragment is a bare plain write.
Its place/modifier errors are unreachable, so only the actual expression child
certificates contribute failures. The original header tree is retained. -/
theorem header_sites {items : List ForItemForm} {body : Expr}
    {continuation : SourceSemantics.Context → SourceCoreLocalCell.Scope → Expr → Prop}
    (tree : GenericForHeader.Tree layouts owner active frame globals onError values source certificates
      definitions administrative type continuation context scope items body)
    (shape : ItemShape items) (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) :
    tree.ReachableErrors registry faults := by
  induction tree with
  | nil next => exact .nil (next := next)
  | uninitialized monomorphic extended ordinary projected allocation annotation same remaining ih =>
      exact .uninitialized (monomorphic := monomorphic) (extended := extended) (ordinary := ordinary)
        (projected := projected) (allocation := allocation) (annotation := annotation)
        (same := same) (remaining := remaining) (ih shape.let_tail)
  | initialized monomorphic extended ordinary found sourceType initial allocation annotation same remaining ih =>
      exact .initialized (monomorphic := monomorphic) (extended := extended) (ordinary := ordinary)
        (initializerFound := found) (sourceType := sourceType) (initial := initial)
        (allocation := allocation) (annotation := annotation) (same := same) (remaining := remaining) (ih shape.let_tail)
  | discard found value remaining ih =>
      exact .discard (found := found) (value := value) (remaining := remaining) (ih shape.discard_tail)
  | assign head remaining ih =>
    obtain ⟨same, bare, rest⟩ := shape.assign_tail
    cases same
    exact .assign (head := head) (remaining := remaining) (ih rest) (GenericAssignmentStatements.Head.ReachableErrors.bare_equal (empty_steps head.shape bare))
  | bitNot _ _ _ => cases shape

namespace Collected

 theorem breaking {context scope mode id node rest expected type}
      (found : source.lookupStatement? id = some node) (form : node.form = .breakStmt) :
      Collected layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode (id :: rest)) expected type (LocalLoop.breaking type) := by
  refine ⟨.breaking found form, ?_⟩
  intro registry faults
  exact .breaking (found := found) (form := form)

 theorem continuing {context scope mode id node rest expected type}
      (found : source.lookupStatement? id = some node) (form : node.form = .continueStmt) :
      Collected layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode (id :: rest)) expected type (LocalLoop.continuing type) := by
  refine ⟨.continuing found form, ?_⟩
  intro registry faults
  exact .continuing (found := found) (form := form)

 theorem body {context scope mode statements expected type code}
      (syntaxTree : GenericLexicalStatements.Syntax source expressionSyntax context mode statements expected)
      (body : GenericLexicalStatements.Tree layouts owner active frame globals onError values source certificates context scope mode statements expected type code) :
      Collected layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode statements) expected type code := by
  refine ⟨.body syntaxTree body, ?_⟩
  intro registry faults
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
      (remaining : Collected layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        nextContext ((binder.id, payload) :: scope) (.statements mode rest) expected type body) :
      Collected layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode (id :: rest)) expected type (.letE annotation.expression body) := by
  refine ⟨.uninitialized found form monomorphic extended ordinary projected allocation annotation same remaining.tree, ?_⟩
  intro registry faults
  exact .uninitialized (found := found) (form := form) (monomorphic := monomorphic) (extended := extended) (ordinary := ordinary) (projected := projected) (allocation := allocation) (annotation := annotation) (same := same) (remaining := remaining.tree) (remaining.sites registry faults)

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
      (remaining : Collected layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative nextContext ((binder.id, lowered.type) :: scope) (.statements mode rest) expected type body) :
      Collected layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode (id :: rest)) expected type (sequence type lowered.expression annotation.expression body) := by
  refine ⟨.initialized found form monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining.tree, ?_⟩
  intro registry faults
  exact .initialized (found := found) (form := form) (monomorphic := monomorphic) (extended := extended) (ordinary := ordinary) (initializerFound := initializerFound) (sourceType := sourceType) (initial := initial) (allocation := allocation) (annotation := annotation) (same := same) (remaining := remaining.tree) (remaining.sites registry faults)

 theorem discard {context scope mode id node expression expressionNode semicolon rest expected lowered type body}
      (found : source.lookupStatement? id = some node) (form : node.form = .expression expression semicolon)
      (notTail : (!semicolon && mode && rest.isEmpty) = false)
      (expressionFound : source.lookupExpression? expression = some expressionNode)
      (value : certificates context scope expression lowered)
      (remaining : Collected layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode rest) expected type body) :
      Collected layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode (id :: rest)) expected type
        (LocalSequence.discard (LocalLoop.controlType type) lowered.expression body) := by
  refine ⟨.discard found form notTail expressionFound value remaining.tree, ?_⟩
  intro registry faults
  exact .discard (found := found) (form := form) (notTail := notTail) (expressionFound := expressionFound) (value := value) (remaining := remaining.tree) (remaining.sites registry faults)

 theorem block {context scope mode id node statements rest expected type innerCode body}
      (found : source.lookupStatement? id = some node) (form : node.form = .block statements)
      (inner : Collected layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements false statements) expected type innerCode)
      (remaining : Collected layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode rest) expected type body) :
      Collected layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode (id :: rest)) expected type
        (LocalLoop.sequence type innerCode body) := by
  refine ⟨.block found form inner.tree remaining.tree, ?_⟩
  intro registry faults
  exact .block (found := found) (form := form) (inner := inner.tree) (remaining := remaining.tree) (inner.sites registry faults) (remaining.sites registry faults)

 theorem ifThen {context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body}
      (found : source.lookupStatement? id = some node) (form : node.form = .ifThen condition thenBody elseBody)
      (conditionFound : source.lookupExpression? condition = some conditionNode)
      (conditionType : conditionNode.type = .bool)
      (conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩)
      (thenTree : Collected layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements false thenBody) expected type thenCode)
      (elseTree : Collected layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements false (elseBody.getD [])) expected type elseCode)
      (remaining : Collected layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode rest) expected type body) :
      Collected layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode (id :: rest)) expected type
        (LocalLoop.sequence type (LocalLoop.conditional type conditionCode thenCode elseCode) body) := by
  refine ⟨.ifThen found form conditionFound conditionType conditionTree thenTree.tree elseTree.tree remaining.tree, ?_⟩
  intro registry faults
  exact .ifThen (found := found) (form := form) (conditionFound := conditionFound) (conditionType := conditionType) (conditionTree := conditionTree) (thenTree := thenTree.tree) (elseTree := elseTree.tree) (remaining := remaining.tree) (thenTree.sites registry faults) (elseTree.sites registry faults) (remaining.sites registry faults)

 theorem whileLoop {context scope mode id node condition conditionNode statements rest expected type conditionCode loopCode body selfReason}
      (found : source.lookupStatement? id = some node) (form : node.form = .whileLoop condition statements)
      (conditionFound : source.lookupExpression? condition = some conditionNode)
      (conditionType : conditionNode.type = .bool)
      (conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩)
      (loopBody : Collected layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements false statements) expected type loopCode)
      (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        (LocalLoop.whileLoop type conditionCode loopCode selfReason) (LocalLoop.resultType type) definitions)
      (remaining : Collected layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode rest) expected type body) :
      Collected layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode (id :: rest)) expected type
        (LocalLoop.sequence type (LocalLoop.whileLoop type conditionCode loopCode selfReason) body) := by
  refine ⟨.whileLoop found form conditionFound conditionType conditionTree loopBody.tree nativeTyped remaining.tree, ?_⟩
  intro registry faults
  exact .whileLoop (found := found) (form := form) (conditionFound := conditionFound) (conditionType := conditionType) (conditionTree := conditionTree) (loopBody := loopBody.tree) (nativeTyped := nativeTyped) (remaining := remaining.tree) (loopBody.sites registry faults) (remaining.sites registry faults)

 theorem assign {context scope mode id node assignment operator rhs rest expected type body}
      (found : source.lookupStatement? id = some node) (form : node.form = .assignValue assignment operator rhs)
      (head : GenericAssignmentStatements.Head values source context (certificates context) scope administrative definitions assignment operator rhs)
      (remaining : Collected layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode rest) expected type body)
    (equal : operator = .equal) (bare : assignment.target.projections = []) :
      Collected layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode (id :: rest)) expected type (head.emit body (LocalLoop.controlType type)) := by
  cases equal
  refine ⟨.assign found form head remaining.tree, ?_⟩
  intro registry faults
  exact .assign (found := found) (form := form) (head := head) (remaining := remaining.tree) (remaining.sites registry faults) (GenericAssignmentStatements.Head.ReachableErrors.bare_equal (empty_steps head.shape bare))

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
        Collected layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
          childContext request.scope (.statements false request.statements) expected type request.code)
      (remaining : Collected layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode rest) expected type body)
    (catalog : SignatureCatalogWellFormed values.checked.signatures)
    (patternContext : GenericImperativeMatch.Tree.MatchContextFields compilation context) :
      Collected layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode (id :: rest)) expected type (LocalLoop.sequence type matched body) := by
  refine ⟨.matchWith found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary (fun request member childContext related => (children request member childContext related).tree) remaining.tree, ?_⟩
  intro registry faults
  exact .matchWith (found := found) (form := form) (scrutineeFound := scrutineeFound) (scrutineeTyped := scrutineeTyped) (casesTyped := casesTyped) (defaultTyped := defaultTyped) (compilation := compilation) (sameValues := sameValues) (sameDefinitions := sameDefinitions) (allocator := allocator) (requests := requests) (receipt := receipt) (ordinary := ordinary) (children := (fun request member childContext related => (children request member childContext related).tree)) (remaining := remaining.tree) catalog patternContext (fun request member childContext related => (children request member childContext related).sites registry faults) (remaining.sites registry faults)

 theorem terminalBlock {context scope mode id node statements rest expected type innerCode suffix}
      (unique : NodeOccurrencesUnique source)
      (found : source.lookupStatement? id = some node) (form : node.form = .block statements)
      (inner : Collected layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements false statements) expected type innerCode)
      (stops : GenericLexicalStatements.Stopped source statements)
      (issued : GenericLexicalStatements.IssuedSuffix source scope mode rest type suffix) :
      Collected layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode (id :: rest)) expected type
        (LocalLoop.sequence type innerCode suffix) := by
  refine ⟨.terminalBlock unique found form inner.tree stops issued, ?_⟩
  intro registry faults
  exact .terminalBlock (unique := unique) (found := found) (form := form) (inner := inner.tree) (stops := stops) (issued := issued) (inner.sites registry faults)

 theorem terminalIf {context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode suffix}
      (unique : NodeOccurrencesUnique source)
      (found : source.lookupStatement? id = some node) (form : node.form = .ifThen condition thenBody (some elseBody))
      (conditionFound : source.lookupExpression? condition = some conditionNode)
      (conditionType : conditionNode.type = .bool)
      (conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩)
      (thenTree : Collected layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements false thenBody) expected type thenCode)
      (elseTree : Collected layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements false elseBody) expected type elseCode)
      (thenStops : GenericLexicalStatements.Stopped source thenBody) (elseStops : GenericLexicalStatements.Stopped source elseBody)
      (issued : GenericLexicalStatements.IssuedSuffix source scope mode rest type suffix) :
      Collected layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode (id :: rest)) expected type
        (LocalLoop.sequence type (LocalLoop.conditional type conditionCode thenCode elseCode) suffix) := by
  refine ⟨.terminalIf unique found form conditionFound conditionType conditionTree thenTree.tree elseTree.tree thenStops elseStops issued, ?_⟩
  intro registry faults
  exact .terminalIf (unique := unique) (found := found) (form := form) (conditionFound := conditionFound) (conditionType := conditionType) (conditionTree := conditionTree) (thenTree := thenTree.tree) (elseTree := elseTree.tree) (thenStops := thenStops) (elseStops := elseStops) (issued := issued) (thenTree.sites registry faults) (elseTree.sites registry faults)

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
        Collected layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
          childContext request.scope (.statements false request.statements) expected type request.code)
      (stops : ReachableMatchContinuations.DefaultStopped source id resolution)
      (issued : GenericLexicalStatements.IssuedSuffix source scope mode rest type suffix)
    (catalog : SignatureCatalogWellFormed values.checked.signatures)
    (patternContext : GenericImperativeMatch.Tree.MatchContextFields compilation context) :
      Collected layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode (id :: rest)) expected type (LocalLoop.sequence type matched suffix) := by
  refine ⟨.terminalMatch unique found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary (fun request member childContext related => (children request member childContext related).tree) stops issued, ?_⟩
  intro registry faults
  exact .terminalMatch (unique := unique) (found := found) (form := form) (scrutineeFound := scrutineeFound) (scrutineeTyped := scrutineeTyped) (casesTyped := casesTyped) (defaultTyped := defaultTyped) (compilation := compilation) (sameValues := sameValues) (sameDefinitions := sameDefinitions) (allocator := allocator) (requests := requests) (receipt := receipt) (ordinary := ordinary) (children := (fun request member childContext related => (children request member childContext related).tree)) (stops := stops) (issued := issued) catalog patternContext (fun request member childContext related => (children request member childContext related).sites registry faults)


 theorem forLoop {context scope mode id node initializer condition post statements rest expected type initialCode body}
      (found : source.lookupStatement? id = some node) (form : node.form = .forLoop initializer condition post statements)
      (initial : Collected layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.initializers initializer condition post statements) expected type initialCode)
      (remaining : Collected layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode rest) expected type body) :
      Collected layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode (id :: rest)) expected type (LocalLoop.sequence type initialCode body) := by
  refine ⟨.forLoop found form initial.tree remaining.tree, ?_⟩
  intro registry faults
  exact .forLoop (found := found) (form := form) (initial := initial.tree)
    (remaining := remaining.tree) (initial.sites registry faults) (remaining.sites registry faults)


 theorem initializersDone {context scope condition conditionNode post statements expected type conditionCode bodyCode postCode selfReason}
      (conditionFound : source.lookupExpression? condition = some conditionNode)
      (conditionType : conditionNode.type = .bool)
      (conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩)
      (loopBody : Collected layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements false statements) expected type bodyCode)
      (postTree : GenericForHeader.Tree layouts owner active frame globals onError values source certificates definitions administrative
        type (TypedForHeader.Fallthrough type) context scope post postCode)
      (postShape : ItemShape post)
      (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        (LocalLoop.iterate type conditionCode bodyCode postCode selfReason) (LocalLoop.resultType type) definitions) :
      Collected layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.initializers [] condition post statements) expected type
        (LocalLoop.iterate type conditionCode bodyCode postCode selfReason) := by
  refine ⟨.initializersDone conditionFound conditionType conditionTree loopBody.tree postTree nativeTyped, ?_⟩
  intro registry faults
  exact .initializersDone (conditionFound := conditionFound) (conditionType := conditionType)
    (conditionTree := conditionTree) (loopBody := loopBody.tree) (postTree := postTree)
    (nativeTyped := nativeTyped) (loopBody.sites registry faults) (header_sites postTree postShape registry faults)


 theorem initializerUninitialized {context nextContext scope binder rest body payload condition post statements expected type}
      (monomorphic : binder.scheme.quantified = [])
      (extended : BinderExtends source.owner context binder nextContext)
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (projected : values.checked.catalog.project binder.scheme.body = .ok payload)
      (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (absentRequest source scope binder payload))
      (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
        (layouts.allocatorAt owner active onError) (absentRequest source scope binder payload))
      (same : annotation.original = allocation.expression)
      (remaining : Collected layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        nextContext ((binder.id, payload) :: scope) (.initializers rest condition post statements) expected type body) :
      Collected layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.initializers (.letDecl binder none :: rest) condition post statements) expected type (.letE annotation.expression body) := by
  refine ⟨.initializerUninitialized monomorphic extended ordinary projected allocation annotation same remaining.tree, ?_⟩
  intro registry faults
  exact .initializerUninitialized (monomorphic := monomorphic) (extended := extended)
    (ordinary := ordinary) (projected := projected) (allocation := allocation) (annotation := annotation)
    (same := same) (remaining := remaining.tree) (remaining.sites registry faults)


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
      (remaining : Collected layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        nextContext ((binder.id, lowered.type) :: scope) (.initializers rest condition post statements) expected type body) :
      Collected layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.initializers (.letDecl binder (some initializer) :: rest) condition post statements) expected type (sequence type lowered.expression annotation.expression body) := by
  refine ⟨.initializerInitialized monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining.tree, ?_⟩
  intro registry faults
  exact .initializerInitialized (monomorphic := monomorphic) (extended := extended)
    (ordinary := ordinary) (initializerFound := initializerFound) (sourceType := sourceType)
    (initial := initial) (allocation := allocation) (annotation := annotation)
    (same := same) (remaining := remaining.tree) (remaining.sites registry faults)


 theorem initializerDiscard {context scope expression expressionNode rest lowered body condition post statements expected type}
      (found : source.lookupExpression? expression = some expressionNode)
      (value : certificates context scope expression lowered)
      (remaining : Collected layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.initializers rest condition post statements) expected type body) :
      Collected layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.initializers (.expression expression :: rest) condition post statements) expected type (LocalSequence.discard (LocalLoop.controlType type) lowered.expression body) := by
  refine ⟨.initializerDiscard found value remaining.tree, ?_⟩
  intro registry faults
  exact .initializerDiscard (found := found) (value := value) (remaining := remaining.tree)
    (remaining.sites registry faults)


 theorem initializerAssign {context scope assignment operator rhs rest body condition post statements expected type}
      (head : GenericAssignmentStatements.Head values source context (certificates context) scope administrative definitions assignment operator rhs)
      (remaining : Collected layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.initializers rest condition post statements) expected type body)
      (equal : operator = .equal) (bare : assignment.target.projections = []) :
      Collected layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.initializers (.assignValue assignment operator rhs :: rest) condition post statements) expected type (head.emit body (LocalLoop.controlType type)) := by
  cases equal
  refine ⟨.initializerAssign head remaining.tree, ?_⟩
  intro registry faults
  exact .initializerAssign (head := head) (remaining := remaining.tree)
    (remaining.sites registry faults)
    (GenericAssignmentStatements.Head.ReachableErrors.bare_equal (empty_steps head.shape bare))

end Collected
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedBranchingCatalogSites
