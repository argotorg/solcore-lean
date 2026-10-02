import Solcore.SourceSemantics.CoreLowering.GenericImperativeMatchReadyFactory

/-! Static extraction results retain the actual recursive Tree and exactly the
per-site diagnostic obligations that it uses. Materializing those obligations
builds the existing Errors and SiteLedgers receipts. No source execution or
child semantic contract is stored in this factory. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericImperativeMatch
open Core Frontend SourceInference
open TypedLexicalWhile (absentRequest initializedRequest sequence)

structure Extraction (layouts : SourceCoreAllocationLayouts.Prepared)
    (owner : SourceSpecialization.SpecializationKey) (active : TypeSystem.Substitution)
    (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (values : ValuesContext) (source : TypedSource) (expressionSyntax : ExpressionId → Prop)
    (certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate)
    (definitions : DataEnvironment) (administrative : Core.Context) (solved : List SolvedRequirement)
    (context : SourceSemantics.Context) (scope : Scope) (position : Position)
    (expected : TypeSystem.Ty) (type : Ty) (code : Expr) where
  tree : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
    context scope position expected type code
  diagnostics : SourceCoreRawMetadata.Registry → FunctionCalls.FaultRep → Prop
  materialize : ∀ registry faults, diagnostics registry faults →
    ∃ errors : Tree.Errors registry faults tree, Tree.SiteLedgers solved registry faults errors

namespace Extraction
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource} {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {definitions : DataEnvironment} {administrative : Core.Context} {solved : List SolvedRequirement}

def body
    {context scope mode statements expected type code}
    (syntaxTree : GenericLexicalStatements.Syntax source expressionSyntax context mode statements expected)
    (body : GenericLexicalStatements.Tree layouts owner active frame globals onError values source certificates context scope mode statements expected type code) :
    Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
        context scope (.statements mode statements) expected type code := by
  refine ⟨(@Tree.body layouts owner active frame globals onError values source expressionSyntax certificates
    definitions administrative context scope mode statements expected type code syntaxTree body), (fun registry
    faults => True), ?_⟩
  intro registry faults provided
  exact ⟨@Tree.Errors.body layouts owner active frame globals onError values source expressionSyntax certificates
    definitions administrative registry faults context scope mode statements expected type code syntaxTree body,
    @Tree.SiteLedgers.body layouts owner active frame globals onError values source expressionSyntax certificates
    definitions administrative solved registry faults context scope mode statements expected type code syntaxTree
    body⟩

def uninitialized
    {context nextContext scope mode id node binder rest expected type body payload}
    (found : source.lookupStatement? id = some node)
    (form : node.form = .letDecl binder none)
    (monomorphic : binder.scheme.quantified = [])
    (extended : BinderExtends source.owner context binder nextContext)
    (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (projected : values.checked.catalog.project binder.scheme.body = .ok payload)
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (absentRequest source scope binder payload))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
        (layouts.allocatorAt owner active onError) (absentRequest source scope binder payload))
    (same : annotation.original = allocation.expression)
    (remaining : Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
        nextContext ((binder.id, payload) :: scope) (.statements mode rest) expected type body) :
    Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
        context scope (.statements mode (id :: rest)) expected type (.letE annotation.expression body) := by
  refine ⟨(@Tree.uninitialized layouts owner active frame globals onError values source expressionSyntax
    certificates definitions administrative context nextContext scope mode id node binder rest expected type body
    payload found form monomorphic extended ordinary projected allocation annotation same remaining.tree), (fun
    registry faults => remaining.diagnostics registry faults), ?_⟩
  intro registry faults provided
  have remainingErrorsGiven := provided
  obtain ⟨remainingErrors, remainingErrorsLedger⟩ := remaining.materialize registry faults remainingErrorsGiven
  exact ⟨@Tree.Errors.uninitialized layouts owner active frame globals onError values source expressionSyntax
    certificates definitions administrative registry faults context nextContext scope mode id node binder rest
    expected type body payload found form monomorphic extended ordinary projected allocation annotation same
    remaining.tree remainingErrors, @Tree.SiteLedgers.uninitialized layouts owner active frame globals onError
    values source expressionSyntax certificates definitions administrative solved registry faults context
    nextContext scope mode id node binder rest expected type body payload found form monomorphic extended ordinary
    projected allocation annotation same remaining.tree remainingErrors remainingErrorsLedger⟩

def initialized
    {context nextContext scope mode id node binder initializer initializerNode lowered body rest expected type}
    (found : source.lookupStatement? id = some node)
    (form : node.form = .letDecl binder (some initializer))
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
    (remaining : Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved nextContext ((binder.id, lowered.type) :: scope) (.statements mode rest) expected type body) :
    Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
        context scope (.statements mode (id :: rest)) expected type (sequence type lowered.expression annotation.expression body) := by
  refine ⟨(@Tree.initialized layouts owner active frame globals onError values source expressionSyntax certificates
    definitions administrative context nextContext scope mode id node binder initializer initializerNode lowered
    body rest expected type found form monomorphic extended ordinary initializerFound sourceType initial allocation
    annotation same remaining.tree), (fun registry faults => remaining.diagnostics registry faults), ?_⟩
  intro registry faults provided
  have remainingErrorsGiven := provided
  obtain ⟨remainingErrors, remainingErrorsLedger⟩ := remaining.materialize registry faults remainingErrorsGiven
  exact ⟨@Tree.Errors.initialized layouts owner active frame globals onError values source expressionSyntax
    certificates definitions administrative registry faults context nextContext scope mode id node binder
    initializer initializerNode lowered body rest expected type found form monomorphic extended ordinary
    initializerFound sourceType initial allocation annotation same remaining.tree remainingErrors,
    @Tree.SiteLedgers.initialized layouts owner active frame globals onError values source expressionSyntax
    certificates definitions administrative solved registry faults context nextContext scope mode id node binder
    initializer initializerNode lowered body rest expected type found form monomorphic extended ordinary
    initializerFound sourceType initial allocation annotation same remaining.tree remainingErrors
    remainingErrorsLedger⟩

def discard
    {context scope mode id node expression expressionNode semicolon rest expected lowered type body}
    (found : source.lookupStatement? id = some node)
    (form : node.form = .expression expression semicolon)
    (notTail : (!semicolon && mode && rest.isEmpty) = false)
    (expressionFound : source.lookupExpression? expression = some expressionNode)
    (value : certificates context scope expression lowered)
    (remaining : Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved context scope (.statements mode rest) expected type body) :
    Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved context scope (.statements mode (id :: rest)) expected type
        (LocalSequence.discard (LocalLoop.controlType type) lowered.expression body) := by
  refine ⟨(@Tree.discard layouts owner active frame globals onError values source expressionSyntax certificates
    definitions administrative context scope mode id node expression expressionNode semicolon rest expected lowered
    type body found form notTail expressionFound value remaining.tree), (fun registry faults =>
    remaining.diagnostics registry faults), ?_⟩
  intro registry faults provided
  have remainingErrorsGiven := provided
  obtain ⟨remainingErrors, remainingErrorsLedger⟩ := remaining.materialize registry faults remainingErrorsGiven
  exact ⟨@Tree.Errors.discard layouts owner active frame globals onError values source expressionSyntax certificates
    definitions administrative registry faults context scope mode id node expression expressionNode semicolon rest
    expected lowered type body found form notTail expressionFound value remaining.tree remainingErrors,
    @Tree.SiteLedgers.discard layouts owner active frame globals onError values source expressionSyntax certificates
    definitions administrative solved registry faults context scope mode id node expression expressionNode semicolon
    rest expected lowered type body found form notTail expressionFound value remaining.tree remainingErrors
    remainingErrorsLedger⟩

def block
    {context scope mode id node statements rest expected type innerCode body}
    (found : source.lookupStatement? id = some node)
    (form : node.form = .block statements)
    (inner : Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved context scope (.statements false statements) expected type innerCode)
    (remaining : Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved context scope (.statements mode rest) expected type body) :
    Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved context scope (.statements mode (id :: rest)) expected type
        (LocalLoop.sequence type innerCode body) := by
  refine ⟨(@Tree.block layouts owner active frame globals onError values source expressionSyntax certificates
    definitions administrative context scope mode id node statements rest expected type innerCode body found form
    inner.tree remaining.tree), (fun registry faults => inner.diagnostics registry faults ∧ remaining.diagnostics
    registry faults), ?_⟩
  intro registry faults provided
  rcases provided with ⟨innerErrorsGiven, remainingErrorsGiven⟩
  obtain ⟨innerErrors, innerErrorsLedger⟩ := inner.materialize registry faults innerErrorsGiven
  obtain ⟨remainingErrors, remainingErrorsLedger⟩ := remaining.materialize registry faults remainingErrorsGiven
  exact ⟨@Tree.Errors.block layouts owner active frame globals onError values source expressionSyntax certificates
    definitions administrative registry faults context scope mode id node statements rest expected type innerCode
    body found form inner.tree remaining.tree innerErrors remainingErrors, @Tree.SiteLedgers.block layouts owner
    active frame globals onError values source expressionSyntax certificates definitions administrative solved
    registry faults context scope mode id node statements rest expected type innerCode body found form inner.tree
    remaining.tree innerErrors remainingErrors innerErrorsLedger remainingErrorsLedger⟩

def ifThen
    {context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body}
    (found : source.lookupStatement? id = some node)
    (form : node.form = .ifThen condition thenBody elseBody)
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionType : conditionNode.type = .bool)
    (conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩)
    (thenTree : Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved context scope (.statements false thenBody) expected type thenCode)
    (elseTree : Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved context scope (.statements false (elseBody.getD [])) expected type elseCode)
    (remaining : Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved context scope (.statements mode rest) expected type body) :
    Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved context scope (.statements mode (id :: rest)) expected type
        (LocalLoop.sequence type (LocalLoop.conditional type conditionCode thenCode elseCode) body) := by
  refine ⟨(@Tree.ifThen layouts owner active frame globals onError values source expressionSyntax certificates
    definitions administrative context scope mode id node condition conditionNode thenBody elseBody rest expected
    type conditionCode thenCode elseCode body found form conditionFound conditionType conditionTree thenTree.tree
    elseTree.tree remaining.tree), (fun registry faults => thenTree.diagnostics registry faults ∧
    elseTree.diagnostics registry faults ∧ remaining.diagnostics registry faults), ?_⟩
  intro registry faults provided
  rcases provided with ⟨thenTreeErrorsGiven, elseTreeErrorsGiven, remainingErrorsGiven⟩
  obtain ⟨thenTreeErrors, thenTreeErrorsLedger⟩ := thenTree.materialize registry faults thenTreeErrorsGiven
  obtain ⟨elseTreeErrors, elseTreeErrorsLedger⟩ := elseTree.materialize registry faults elseTreeErrorsGiven
  obtain ⟨remainingErrors, remainingErrorsLedger⟩ := remaining.materialize registry faults remainingErrorsGiven
  exact ⟨@Tree.Errors.ifThen layouts owner active frame globals onError values source expressionSyntax certificates
    definitions administrative registry faults context scope mode id node condition conditionNode thenBody elseBody
    rest expected type conditionCode thenCode elseCode body found form conditionFound conditionType conditionTree
    thenTree.tree elseTree.tree remaining.tree thenTreeErrors elseTreeErrors remainingErrors,
    @Tree.SiteLedgers.ifThen layouts owner active frame globals onError values source expressionSyntax certificates
    definitions administrative solved registry faults context scope mode id node condition conditionNode thenBody
    elseBody rest expected type conditionCode thenCode elseCode body found form conditionFound conditionType
    conditionTree thenTree.tree elseTree.tree remaining.tree thenTreeErrors elseTreeErrors remainingErrors
    thenTreeErrorsLedger elseTreeErrorsLedger remainingErrorsLedger⟩

def breaking
    {context scope mode id node rest expected type}
    (found : source.lookupStatement? id = some node)
    (form : node.form = .breakStmt) :
    Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
        context scope (.statements mode (id :: rest)) expected type (LocalLoop.breaking type) := by
  refine ⟨(@Tree.breaking layouts owner active frame globals onError values source expressionSyntax certificates
    definitions administrative context scope mode id node rest expected type found form), (fun registry faults =>
    True), ?_⟩
  intro registry faults provided
  exact ⟨@Tree.Errors.breaking layouts owner active frame globals onError values source expressionSyntax
    certificates definitions administrative registry faults context scope mode id node rest expected type found
    form, @Tree.SiteLedgers.breaking layouts owner active frame globals onError values source expressionSyntax
    certificates definitions administrative solved registry faults context scope mode id node rest expected type
    found form⟩

def continuing
    {context scope mode id node rest expected type}
    (found : source.lookupStatement? id = some node)
    (form : node.form = .continueStmt) :
    Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
        context scope (.statements mode (id :: rest)) expected type (LocalLoop.continuing type) := by
  refine ⟨(@Tree.continuing layouts owner active frame globals onError values source expressionSyntax certificates
    definitions administrative context scope mode id node rest expected type found form), (fun registry faults =>
    True), ?_⟩
  intro registry faults provided
  exact ⟨@Tree.Errors.continuing layouts owner active frame globals onError values source expressionSyntax
    certificates definitions administrative registry faults context scope mode id node rest expected type found
    form, @Tree.SiteLedgers.continuing layouts owner active frame globals onError values source expressionSyntax
    certificates definitions administrative solved registry faults context scope mode id node rest expected type
    found form⟩

def whileLoop
    {context scope mode id node condition conditionNode statements rest expected type conditionCode loopCode body selfReason}
    (found : source.lookupStatement? id = some node)
    (form : node.form = .whileLoop condition statements)
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionType : conditionNode.type = .bool)
    (conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩)
    (loopBody : Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
        context scope (.statements false statements) expected type loopCode)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        (LocalLoop.whileLoop type conditionCode loopCode selfReason) (LocalLoop.resultType type) definitions)
    (remaining : Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
        context scope (.statements mode rest) expected type body) :
    Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
        context scope (.statements mode (id :: rest)) expected type
        (LocalLoop.sequence type (LocalLoop.whileLoop type conditionCode loopCode selfReason) body) := by
  refine ⟨(@Tree.whileLoop layouts owner active frame globals onError values source expressionSyntax certificates
    definitions administrative context scope mode id node condition conditionNode statements rest expected type
    conditionCode loopCode body selfReason found form conditionFound conditionType conditionTree loopBody.tree
    nativeTyped remaining.tree), (fun registry faults => loopBody.diagnostics registry faults ∧
    remaining.diagnostics registry faults), ?_⟩
  intro registry faults provided
  rcases provided with ⟨loopBodyErrorsGiven, remainingErrorsGiven⟩
  obtain ⟨loopBodyErrors, loopBodyErrorsLedger⟩ := loopBody.materialize registry faults loopBodyErrorsGiven
  obtain ⟨remainingErrors, remainingErrorsLedger⟩ := remaining.materialize registry faults remainingErrorsGiven
  exact ⟨@Tree.Errors.whileLoop layouts owner active frame globals onError values source expressionSyntax
    certificates definitions administrative registry faults context scope mode id node condition conditionNode
    statements rest expected type conditionCode loopCode body selfReason found form conditionFound conditionType
    conditionTree loopBody.tree nativeTyped remaining.tree loopBodyErrors remainingErrors,
    @Tree.SiteLedgers.whileLoop layouts owner active frame globals onError values source expressionSyntax
    certificates definitions administrative solved registry faults context scope mode id node condition
    conditionNode statements rest expected type conditionCode loopCode body selfReason found form conditionFound
    conditionType conditionTree loopBody.tree nativeTyped remaining.tree loopBodyErrors remainingErrors
    loopBodyErrorsLedger remainingErrorsLedger⟩

def assign
    {context scope mode id node assignment operator rhs rest expected type body}
    (found : source.lookupStatement? id = some node)
    (form : node.form = .assignValue assignment operator rhs)
    (head : GenericAssignmentStatements.Head values source context (certificates context) scope administrative definitions assignment operator rhs)
    (remaining : Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
        context scope (.statements mode rest) expected type body) :
    Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
        context scope (.statements mode (id :: rest)) expected type (head.emit body (LocalLoop.controlType type)) := by
  refine ⟨(@Tree.assign layouts owner active frame globals onError values source expressionSyntax certificates
    definitions administrative context scope mode id node assignment operator rhs rest expected type body found form
    head remaining.tree), (fun registry faults => remaining.diagnostics registry faults ∧ head.Errors registry
    faults), ?_⟩
  intro registry faults provided
  rcases provided with ⟨remainingErrorsGiven, headErrors⟩
  obtain ⟨remainingErrors, remainingErrorsLedger⟩ := remaining.materialize registry faults remainingErrorsGiven
  exact ⟨@Tree.Errors.assign layouts owner active frame globals onError values source expressionSyntax certificates
    definitions administrative registry faults context scope mode id node assignment operator rhs rest expected type
    body found form head remaining.tree remainingErrors headErrors, @Tree.SiteLedgers.assign layouts owner active
    frame globals onError values source expressionSyntax certificates definitions administrative solved registry
    faults context scope mode id node assignment operator rhs rest expected type body found form head remaining.tree
    remainingErrors headErrors remainingErrorsLedger⟩

def bitNot
    {context scope mode id node assignment rest expected type body}
    (found : source.lookupStatement? id = some node)
    (form : node.form = .assignBitNot assignment)
    (head : CompatibleBitNotStatements.Head context scope assignment)
    (remaining : Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
        context scope (.statements mode rest) expected type body) :
    Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
        context scope (.statements mode (id :: rest)) expected type (head.emit body (LocalLoop.controlType type)) := by
  refine ⟨(@Tree.bitNot layouts owner active frame globals onError values source expressionSyntax certificates
    definitions administrative context scope mode id node assignment rest expected type body found form head
    remaining.tree), (fun registry faults => remaining.diagnostics registry faults ∧ head.Errors faults), ?_⟩
  intro registry faults provided
  rcases provided with ⟨remainingErrorsGiven, headErrors⟩
  obtain ⟨remainingErrors, remainingErrorsLedger⟩ := remaining.materialize registry faults remainingErrorsGiven
  exact ⟨@Tree.Errors.bitNot layouts owner active frame globals onError values source expressionSyntax certificates
    definitions administrative registry faults context scope mode id node assignment rest expected type body found
    form head remaining.tree remainingErrors headErrors, @Tree.SiteLedgers.bitNot layouts owner active frame globals
    onError values source expressionSyntax certificates definitions administrative solved registry faults context
    scope mode id node assignment rest expected type body found form head remaining.tree remainingErrors headErrors
    remainingErrorsLedger⟩

def forLoop
    {context scope mode id node initializer condition post statements rest expected type initialCode body}
    (found : source.lookupStatement? id = some node)
    (form : node.form = .forLoop initializer condition post statements)
    (initial : Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved context scope (.initializers initializer condition post statements) expected type initialCode)
    (remaining : Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved context scope (.statements mode rest) expected type body) :
    Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved context scope (.statements mode (id :: rest)) expected type (LocalLoop.sequence type initialCode body) := by
  refine ⟨(@Tree.forLoop layouts owner active frame globals onError values source expressionSyntax certificates
    definitions administrative context scope mode id node initializer condition post statements rest expected type
    initialCode body found form initial.tree remaining.tree), (fun registry faults => initial.diagnostics registry
    faults ∧ remaining.diagnostics registry faults), ?_⟩
  intro registry faults provided
  rcases provided with ⟨initialErrorsGiven, remainingErrorsGiven⟩
  obtain ⟨initialErrors, initialErrorsLedger⟩ := initial.materialize registry faults initialErrorsGiven
  obtain ⟨remainingErrors, remainingErrorsLedger⟩ := remaining.materialize registry faults remainingErrorsGiven
  exact ⟨@Tree.Errors.forLoop layouts owner active frame globals onError values source expressionSyntax certificates
    definitions administrative registry faults context scope mode id node initializer condition post statements rest
    expected type initialCode body found form initial.tree remaining.tree initialErrors remainingErrors,
    @Tree.SiteLedgers.forLoop layouts owner active frame globals onError values source expressionSyntax certificates
    definitions administrative solved registry faults context scope mode id node initializer condition post
    statements rest expected type initialCode body found form initial.tree remaining.tree initialErrors
    remainingErrors initialErrorsLedger remainingErrorsLedger⟩

def initializersDone
    {context scope condition conditionNode post statements expected type conditionCode bodyCode postCode selfReason}
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionType : conditionNode.type = .bool)
    (conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩)
    (loopBody : Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved context scope (.statements false statements) expected type bodyCode)
    (postTree : GenericForHeader.Tree layouts owner active frame globals onError values source certificates definitions administrative
        type (TypedForHeader.Fallthrough type) context scope post postCode)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        (LocalLoop.iterate type conditionCode bodyCode postCode selfReason) (LocalLoop.resultType type) definitions) :
    Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved context scope (.initializers [] condition post statements) expected type
        (LocalLoop.iterate type conditionCode bodyCode postCode selfReason) := by
  refine ⟨(@Tree.initializersDone layouts owner active frame globals onError values source expressionSyntax
    certificates definitions administrative context scope condition conditionNode post statements expected type
    conditionCode bodyCode postCode selfReason conditionFound conditionType conditionTree loopBody.tree postTree
    nativeTyped), (fun registry faults => loopBody.diagnostics registry faults ∧ GenericForHeader.Tree.Errors
    registry faults postTree), ?_⟩
  intro registry faults provided
  rcases provided with ⟨loopErrorsGiven, postErrors⟩
  obtain ⟨loopErrors, loopErrorsLedger⟩ := loopBody.materialize registry faults loopErrorsGiven
  exact ⟨@Tree.Errors.initializersDone layouts owner active frame globals onError values source expressionSyntax
    certificates definitions administrative registry faults context scope condition conditionNode post statements
    expected type conditionCode bodyCode postCode selfReason conditionFound conditionType conditionTree
    loopBody.tree postTree nativeTyped loopErrors postErrors, @Tree.SiteLedgers.initializersDone layouts owner
    active frame globals onError values source expressionSyntax certificates definitions administrative solved
    registry faults context scope condition conditionNode post statements expected type conditionCode bodyCode
    postCode selfReason conditionFound conditionType conditionTree loopBody.tree postTree nativeTyped loopErrors
    postErrors loopErrorsLedger⟩

def initializerUninitialized
    {context nextContext scope binder rest body payload condition post statements expected type}
    (monomorphic : binder.scheme.quantified = [])
    (extended : BinderExtends source.owner context binder nextContext)
    (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (projected : values.checked.catalog.project binder.scheme.body = .ok payload)
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (absentRequest source scope binder payload))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
        (layouts.allocatorAt owner active onError) (absentRequest source scope binder payload))
    (same : annotation.original = allocation.expression)
    (remaining : Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
        nextContext ((binder.id, payload) :: scope) (.initializers rest condition post statements) expected type body) :
    Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
        context scope (.initializers (.letDecl binder none :: rest) condition post statements) expected type (.letE annotation.expression body) := by
  refine ⟨(@Tree.initializerUninitialized layouts owner active frame globals onError values source expressionSyntax
    certificates definitions administrative context nextContext scope binder rest body payload condition post
    statements expected type monomorphic extended ordinary projected allocation annotation same remaining.tree),
    (fun registry faults => remaining.diagnostics registry faults), ?_⟩
  intro registry faults provided
  have remainingErrorsGiven := provided
  obtain ⟨remainingErrors, remainingErrorsLedger⟩ := remaining.materialize registry faults remainingErrorsGiven
  exact ⟨@Tree.Errors.initializerUninitialized layouts owner active frame globals onError values source
    expressionSyntax certificates definitions administrative registry faults context nextContext scope binder rest
    body payload condition post statements expected type monomorphic extended ordinary projected allocation
    annotation same remaining.tree remainingErrors, @Tree.SiteLedgers.initializerUninitialized layouts owner active
    frame globals onError values source expressionSyntax certificates definitions administrative solved registry
    faults context nextContext scope binder rest body payload condition post statements expected type monomorphic
    extended ordinary projected allocation annotation same remaining.tree remainingErrors remainingErrorsLedger⟩

def initializerInitialized
    {context nextContext scope binder initializer initializerNode lowered body rest condition post statements expected type}
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
    (remaining : Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
        nextContext ((binder.id, lowered.type) :: scope) (.initializers rest condition post statements) expected type body) :
    Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
        context scope (.initializers (.letDecl binder (some initializer) :: rest) condition post statements) expected type (sequence type lowered.expression annotation.expression body) := by
  refine ⟨(@Tree.initializerInitialized layouts owner active frame globals onError values source expressionSyntax
    certificates definitions administrative context nextContext scope binder initializer initializerNode lowered
    body rest condition post statements expected type monomorphic extended ordinary initializerFound sourceType
    initial allocation annotation same remaining.tree), (fun registry faults => remaining.diagnostics registry
    faults), ?_⟩
  intro registry faults provided
  have remainingErrorsGiven := provided
  obtain ⟨remainingErrors, remainingErrorsLedger⟩ := remaining.materialize registry faults remainingErrorsGiven
  exact ⟨@Tree.Errors.initializerInitialized layouts owner active frame globals onError values source
    expressionSyntax certificates definitions administrative registry faults context nextContext scope binder
    initializer initializerNode lowered body rest condition post statements expected type monomorphic extended
    ordinary initializerFound sourceType initial allocation annotation same remaining.tree remainingErrors,
    @Tree.SiteLedgers.initializerInitialized layouts owner active frame globals onError values source
    expressionSyntax certificates definitions administrative solved registry faults context nextContext scope binder
    initializer initializerNode lowered body rest condition post statements expected type monomorphic extended
    ordinary initializerFound sourceType initial allocation annotation same remaining.tree remainingErrors
    remainingErrorsLedger⟩

def initializerDiscard
    {context scope expression expressionNode rest lowered body condition post statements expected type}
    (found : source.lookupExpression? expression = some expressionNode)
    (value : certificates context scope expression lowered)
    (remaining : Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
        context scope (.initializers rest condition post statements) expected type body) :
    Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
        context scope (.initializers (.expression expression :: rest) condition post statements) expected type (LocalSequence.discard (LocalLoop.controlType type) lowered.expression body) := by
  refine ⟨(@Tree.initializerDiscard layouts owner active frame globals onError values source expressionSyntax
    certificates definitions administrative context scope expression expressionNode rest lowered body condition post
    statements expected type found value remaining.tree), (fun registry faults => remaining.diagnostics registry
    faults), ?_⟩
  intro registry faults provided
  have remainingErrorsGiven := provided
  obtain ⟨remainingErrors, remainingErrorsLedger⟩ := remaining.materialize registry faults remainingErrorsGiven
  exact ⟨@Tree.Errors.initializerDiscard layouts owner active frame globals onError values source expressionSyntax
    certificates definitions administrative registry faults context scope expression expressionNode rest lowered
    body condition post statements expected type found value remaining.tree remainingErrors,
    @Tree.SiteLedgers.initializerDiscard layouts owner active frame globals onError values source expressionSyntax
    certificates definitions administrative solved registry faults context scope expression expressionNode rest
    lowered body condition post statements expected type found value remaining.tree remainingErrors
    remainingErrorsLedger⟩

def initializerAssign
    {context scope assignment operator rhs rest body condition post statements expected type}
    (head : GenericAssignmentStatements.Head values source context (certificates context) scope administrative definitions assignment operator rhs)
    (remaining : Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
        context scope (.initializers rest condition post statements) expected type body) :
    Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
        context scope (.initializers (.assignValue assignment operator rhs :: rest) condition post statements) expected type (head.emit body (LocalLoop.controlType type)) := by
  refine ⟨(@Tree.initializerAssign layouts owner active frame globals onError values source expressionSyntax
    certificates definitions administrative context scope assignment operator rhs rest body condition post
    statements expected type head remaining.tree), (fun registry faults => remaining.diagnostics registry faults ∧
    head.Errors registry faults), ?_⟩
  intro registry faults provided
  rcases provided with ⟨remainingErrorsGiven, headErrors⟩
  obtain ⟨remainingErrors, remainingErrorsLedger⟩ := remaining.materialize registry faults remainingErrorsGiven
  exact ⟨@Tree.Errors.initializerAssign layouts owner active frame globals onError values source expressionSyntax
    certificates definitions administrative registry faults context scope assignment operator rhs rest body
    condition post statements expected type head remaining.tree remainingErrors headErrors,
    @Tree.SiteLedgers.initializerAssign layouts owner active frame globals onError values source expressionSyntax
    certificates definitions administrative solved registry faults context scope assignment operator rhs rest body
    condition post statements expected type head remaining.tree remainingErrors headErrors remainingErrorsLedger⟩

def initializerBitNot
    {context scope assignment rest body condition post statements expected type}
    (head : CompatibleBitNotStatements.Head context scope assignment)
    (remaining : Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
        context scope (.initializers rest condition post statements) expected type body) :
    Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
        context scope (.initializers (.assignBitNot assignment :: rest) condition post statements) expected type (head.emit body (LocalLoop.controlType type)) := by
  refine ⟨(@Tree.initializerBitNot layouts owner active frame globals onError values source expressionSyntax
    certificates definitions administrative context scope assignment rest body condition post statements expected
    type head remaining.tree), (fun registry faults => remaining.diagnostics registry faults ∧ head.Errors faults),
    ?_⟩
  intro registry faults provided
  rcases provided with ⟨remainingErrorsGiven, headErrors⟩
  obtain ⟨remainingErrors, remainingErrorsLedger⟩ := remaining.materialize registry faults remainingErrorsGiven
  exact ⟨@Tree.Errors.initializerBitNot layouts owner active frame globals onError values source expressionSyntax
    certificates definitions administrative registry faults context scope assignment rest body condition post
    statements expected type head remaining.tree remainingErrors headErrors, @Tree.SiteLedgers.initializerBitNot
    layouts owner active frame globals onError values source expressionSyntax certificates definitions
    administrative solved registry faults context scope assignment rest body condition post statements expected type
    head remaining.tree remainingErrors headErrors remainingErrorsLedger⟩

def matchWith
    {context scope mode id node resolution scrutineeNode rest expected type matched body selfReason control caseFacts}
    (found : source.lookupStatement? id = some node)
    (form : node.form = .matchWith resolution)
    (scrutineeFound : source.lookupExpression? resolution.scrutinee = some scrutineeNode)
    (scrutineeTyped : ExpressionHasType source context resolution.scrutinee scrutineeNode.type)
    (casesTyped : MatchCasesHaveType source control context scrutineeNode.type resolution.cases caseFacts)
    (defaultTyped : ∀ statements, resolution.defaultBody = some statements →
        ∃ finalContext facts, StatementsHaveType source control context statements finalContext facts)
    (compilation : SourceCoreCompatibleDataMatches.Context)
    (sameValues : compilation.values = values)
    (sameDefinitions : compilation.definitions = definitions)
    (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
        (layouts.allocatorAt owner active onError)))
    (requests : List GenericMatchChildren.Request)
    (receipt : CompatibleMatchCertificates.Certificate compilation source scope id resolution type selfReason
        (certificates context) (GenericMatchChildren.Occurs requests) matched)
    (ordinary : CompatibleMatchSelectionPrefix.Ordinary receipt)
    (children : ∀ request, request ∈ requests → ∀ childContext,
        GenericMatchChildren.ScopedContextFor source context (resolution.hiddenScrutinee :: scope.map Prod.fst) scrutineeNode.type resolution.cases resolution.defaultBody request childContext →
        Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
          childContext request.scope (.statements false request.statements) expected type request.code)
    (remaining : Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
        context scope (.statements mode rest) expected type body)
    (sameLedger : compilation.solvedRequirements = solved) :
    Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
        context scope (.statements mode (id :: rest)) expected type (LocalLoop.sequence type matched body) := by
  refine ⟨(@Tree.matchWith layouts owner active frame globals onError values source expressionSyntax certificates
    definitions administrative context scope mode id node resolution scrutineeNode rest expected type matched body
    selfReason control caseFacts found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation
    sameValues sameDefinitions allocator requests receipt ordinary (fun request member childContext related =>
    (children request member childContext related).tree) remaining.tree), (fun registry faults => (∀ request member
    childContext related, (children request member childContext related).diagnostics registry faults) ∧
    remaining.diagnostics registry faults), ?_⟩
  intro registry faults provided
  rcases provided with ⟨childErrorsGiven, remainingErrorsGiven⟩
  classical
  have childrenMaterialized := fun request member childContext related =>
    (children request member childContext related).materialize registry faults (childErrorsGiven request member childContext related)
  let childErrors := fun request member childContext related => Classical.choose (childrenMaterialized request member childContext related)
  have childLedgers := fun request member childContext related => Classical.choose_spec (childrenMaterialized request member childContext related)
  obtain ⟨remainingErrors, remainingErrorsLedger⟩ := remaining.materialize registry faults remainingErrorsGiven
  exact ⟨@Tree.Errors.matchWith layouts owner active frame globals onError values source expressionSyntax
    certificates definitions administrative registry faults context scope mode id node resolution scrutineeNode rest
    expected type matched body selfReason control caseFacts found form scrutineeFound scrutineeTyped casesTyped
    defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary (fun request member
    childContext related => (children request member childContext related).tree) remaining.tree childErrors
    remainingErrors, @Tree.SiteLedgers.matchWith layouts owner active frame globals onError values source
    expressionSyntax certificates definitions administrative solved registry faults context scope mode id node
    resolution scrutineeNode rest expected type matched body selfReason control caseFacts found form scrutineeFound
    scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt
    ordinary (fun request member childContext related => (children request member childContext related).tree)
    remaining.tree childErrors remainingErrors sameLedger childLedgers remainingErrorsLedger⟩

/-- Once the unchanged diagnostic obligations are interpreted, the actual
site ledgers and the caller's source context supply the existing Ready API. -/
theorem ready
    {context : SourceSemantics.Context} {scope : Scope} {position : Position}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (extracted : Extraction layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
      context scope position expected type code)
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (diagnostics : extracted.diagnostics registry faults)
    {evidence : Dynamic.EvidenceEnvironment}
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (signatures : context.signatures = values.checked.signatures) :
    Tree.Ready registry faults extracted.tree := by
  obtain ⟨errors, ledgers⟩ := extracted.materialize registry faults diagnostics
  exact ledgers.ready valid signatures

end Extraction
end Solcore.SourceSemantics.CoreLowering.GenericImperativeMatch
