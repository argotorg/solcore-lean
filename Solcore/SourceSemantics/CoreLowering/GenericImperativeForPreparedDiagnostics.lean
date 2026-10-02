import Solcore.SourceSemantics.CoreLowering.NamedForFunctionBodyMeaning
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogProfiles
import Solcore.SourceSemantics.CoreLowering.GenericImperativeForTree
import Solcore.SourceSemantics.CoreLowering.GenericForHeaderDiagnosticExtraction

/-! Residual diagnostics for the existing for Tree. Materialization builds the
same policy-indexed Errors, without a new statement grammar or runtime premise.
Actual prepared operand laws are supplied by authenticated origin factories. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericImperativeFor
open Core Frontend SourceInference
open TypedLexicalWhile (absentRequest initializedRequest sequence)

structure DiagnosticExtraction (diagnosticPolicy : AssignmentDiagnosticPolicy) (layouts : SourceCoreAllocationLayouts.Prepared)
    (owner : SourceSpecialization.SpecializationKey) (active : TypeSystem.Substitution)
    (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (values : ValuesContext) (source : TypedSource) (expressionSyntax : ExpressionId → Prop)
    (certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate)
    (definitions : DataEnvironment) (administrative : Core.Context)
    (context : SourceSemantics.Context) (scope : Scope) (position : Position)
    (expected : TypeSystem.Ty) (type : Ty) (code : Expr) where
  tree : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
    context scope position expected type code
  diagnostics : SourceCoreRawMetadata.Registry → FunctionCalls.FaultRep → Prop
  materialize : ∀ registry faults, diagnostics registry faults →
    Tree.ErrorsFor diagnosticPolicy registry faults tree

namespace DiagnosticExtraction
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource} {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {definitions : DataEnvironment} {administrative : Core.Context} {diagnosticPolicy : AssignmentDiagnosticPolicy}


def body
    {context scope mode statements expected type code}
    (syntaxTree : GenericLexicalStatements.Syntax source expressionSyntax context mode statements expected)
    (body : GenericLexicalStatements.Tree layouts owner active frame globals onError values source certificates context scope mode statements expected type code) :
    DiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode statements) expected type code := by
  refine ⟨(@Tree.body layouts owner active frame globals onError values source expressionSyntax certificates
    definitions administrative context scope mode statements expected type code syntaxTree body), (fun registry
    faults => True), ?_⟩
  intro registry faults provided
  exact @Tree.ErrorsFor.body layouts owner active frame globals onError values source expressionSyntax certificates
    definitions administrative diagnosticPolicy registry faults context scope mode statements expected type code syntaxTree body

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
    (remaining : DiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        nextContext ((binder.id, payload) :: scope) (.statements mode rest) expected type body) :
    DiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode (id :: rest)) expected type (.letE annotation.expression body) := by
  refine ⟨(@Tree.uninitialized layouts owner active frame globals onError values source expressionSyntax
    certificates definitions administrative context nextContext scope mode id node binder rest expected type body
    payload found form monomorphic extended ordinary projected allocation annotation same remaining.tree), (fun
    registry faults => remaining.diagnostics registry faults), ?_⟩
  intro registry faults provided
  have remainingErrorsGiven := provided
  have remainingErrors := remaining.materialize registry faults remainingErrorsGiven
  exact @Tree.ErrorsFor.uninitialized layouts owner active frame globals onError values source expressionSyntax
    certificates definitions administrative diagnosticPolicy registry faults context nextContext scope mode id node binder rest
    expected type body payload found form monomorphic extended ordinary projected allocation annotation same
    remaining.tree remainingErrors

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
    (remaining : DiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative nextContext ((binder.id, lowered.type) :: scope) (.statements mode rest) expected type body) :
    DiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode (id :: rest)) expected type (sequence type lowered.expression annotation.expression body) := by
  refine ⟨(@Tree.initialized layouts owner active frame globals onError values source expressionSyntax certificates
    definitions administrative context nextContext scope mode id node binder initializer initializerNode lowered
    body rest expected type found form monomorphic extended ordinary initializerFound sourceType initial allocation
    annotation same remaining.tree), (fun registry faults => remaining.diagnostics registry faults), ?_⟩
  intro registry faults provided
  have remainingErrorsGiven := provided
  have remainingErrors := remaining.materialize registry faults remainingErrorsGiven
  exact @Tree.ErrorsFor.initialized layouts owner active frame globals onError values source expressionSyntax
    certificates definitions administrative diagnosticPolicy registry faults context nextContext scope mode id node binder
    initializer initializerNode lowered body rest expected type found form monomorphic extended ordinary
    initializerFound sourceType initial allocation annotation same remaining.tree remainingErrors

def discard
    {context scope mode id node expression expressionNode semicolon rest expected lowered type body}
    (found : source.lookupStatement? id = some node)
    (form : node.form = .expression expression semicolon)
    (notTail : (!semicolon && mode && rest.isEmpty) = false)
    (expressionFound : source.lookupExpression? expression = some expressionNode)
    (value : certificates context scope expression lowered)
    (remaining : DiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode rest) expected type body) :
    DiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode (id :: rest)) expected type
        (LocalSequence.discard (LocalLoop.controlType type) lowered.expression body) := by
  refine ⟨(@Tree.discard layouts owner active frame globals onError values source expressionSyntax certificates
    definitions administrative context scope mode id node expression expressionNode semicolon rest expected lowered
    type body found form notTail expressionFound value remaining.tree), (fun registry faults =>
    remaining.diagnostics registry faults), ?_⟩
  intro registry faults provided
  have remainingErrorsGiven := provided
  have remainingErrors := remaining.materialize registry faults remainingErrorsGiven
  exact @Tree.ErrorsFor.discard layouts owner active frame globals onError values source expressionSyntax certificates
    definitions administrative diagnosticPolicy registry faults context scope mode id node expression expressionNode semicolon rest
    expected lowered type body found form notTail expressionFound value remaining.tree remainingErrors

def block
    {context scope mode id node statements rest expected type innerCode body}
    (found : source.lookupStatement? id = some node)
    (form : node.form = .block statements)
    (inner : DiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements false statements) expected type innerCode)
    (remaining : DiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode rest) expected type body) :
    DiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode (id :: rest)) expected type
        (LocalLoop.sequence type innerCode body) := by
  refine ⟨(@Tree.block layouts owner active frame globals onError values source expressionSyntax certificates
    definitions administrative context scope mode id node statements rest expected type innerCode body found form
    inner.tree remaining.tree), (fun registry faults => inner.diagnostics registry faults ∧ remaining.diagnostics
    registry faults), ?_⟩
  intro registry faults provided
  rcases provided with ⟨innerErrorsGiven, remainingErrorsGiven⟩
  have innerErrors := inner.materialize registry faults innerErrorsGiven
  have remainingErrors := remaining.materialize registry faults remainingErrorsGiven
  exact @Tree.ErrorsFor.block layouts owner active frame globals onError values source expressionSyntax certificates
    definitions administrative diagnosticPolicy registry faults context scope mode id node statements rest expected type innerCode
    body found form inner.tree remaining.tree innerErrors remainingErrors

def ifThen
    {context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body}
    (found : source.lookupStatement? id = some node)
    (form : node.form = .ifThen condition thenBody elseBody)
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionType : conditionNode.type = .bool)
    (conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩)
    (thenTree : DiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements false thenBody) expected type thenCode)
    (elseTree : DiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements false (elseBody.getD [])) expected type elseCode)
    (remaining : DiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode rest) expected type body) :
    DiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode (id :: rest)) expected type
        (LocalLoop.sequence type (LocalLoop.conditional type conditionCode thenCode elseCode) body) := by
  refine ⟨(@Tree.ifThen layouts owner active frame globals onError values source expressionSyntax certificates
    definitions administrative context scope mode id node condition conditionNode thenBody elseBody rest expected
    type conditionCode thenCode elseCode body found form conditionFound conditionType conditionTree thenTree.tree
    elseTree.tree remaining.tree), (fun registry faults => thenTree.diagnostics registry faults ∧
    elseTree.diagnostics registry faults ∧ remaining.diagnostics registry faults), ?_⟩
  intro registry faults provided
  rcases provided with ⟨thenTreeErrorsGiven, elseTreeErrorsGiven, remainingErrorsGiven⟩
  have thenTreeErrors := thenTree.materialize registry faults thenTreeErrorsGiven
  have elseTreeErrors := elseTree.materialize registry faults elseTreeErrorsGiven
  have remainingErrors := remaining.materialize registry faults remainingErrorsGiven
  exact @Tree.ErrorsFor.ifThen layouts owner active frame globals onError values source expressionSyntax certificates
    definitions administrative diagnosticPolicy registry faults context scope mode id node condition conditionNode thenBody elseBody
    rest expected type conditionCode thenCode elseCode body found form conditionFound conditionType conditionTree
    thenTree.tree elseTree.tree remaining.tree thenTreeErrors elseTreeErrors remainingErrors

def breaking
    {context scope mode id node rest expected type}
    (found : source.lookupStatement? id = some node)
    (form : node.form = .breakStmt) :
    DiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode (id :: rest)) expected type (LocalLoop.breaking type) := by
  refine ⟨(@Tree.breaking layouts owner active frame globals onError values source expressionSyntax certificates
    definitions administrative context scope mode id node rest expected type found form), (fun registry faults =>
    True), ?_⟩
  intro registry faults provided
  exact @Tree.ErrorsFor.breaking layouts owner active frame globals onError values source expressionSyntax
    certificates definitions administrative diagnosticPolicy registry faults context scope mode id node rest expected type found
    form

def continuing
    {context scope mode id node rest expected type}
    (found : source.lookupStatement? id = some node)
    (form : node.form = .continueStmt) :
    DiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode (id :: rest)) expected type (LocalLoop.continuing type) := by
  refine ⟨(@Tree.continuing layouts owner active frame globals onError values source expressionSyntax certificates
    definitions administrative context scope mode id node rest expected type found form), (fun registry faults =>
    True), ?_⟩
  intro registry faults provided
  exact @Tree.ErrorsFor.continuing layouts owner active frame globals onError values source expressionSyntax
    certificates definitions administrative diagnosticPolicy registry faults context scope mode id node rest expected type found
    form

def whileLoop
    {context scope mode id node condition conditionNode statements rest expected type conditionCode loopCode body selfReason}
    (found : source.lookupStatement? id = some node)
    (form : node.form = .whileLoop condition statements)
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionType : conditionNode.type = .bool)
    (conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩)
    (loopBody : DiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements false statements) expected type loopCode)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        (LocalLoop.whileLoop type conditionCode loopCode selfReason) (LocalLoop.resultType type) definitions)
    (remaining : DiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode rest) expected type body) :
    DiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode (id :: rest)) expected type
        (LocalLoop.sequence type (LocalLoop.whileLoop type conditionCode loopCode selfReason) body) := by
  refine ⟨(@Tree.whileLoop layouts owner active frame globals onError values source expressionSyntax certificates
    definitions administrative context scope mode id node condition conditionNode statements rest expected type
    conditionCode loopCode body selfReason found form conditionFound conditionType conditionTree loopBody.tree
    nativeTyped remaining.tree), (fun registry faults => loopBody.diagnostics registry faults ∧
    remaining.diagnostics registry faults), ?_⟩
  intro registry faults provided
  rcases provided with ⟨loopBodyErrorsGiven, remainingErrorsGiven⟩
  have loopBodyErrors := loopBody.materialize registry faults loopBodyErrorsGiven
  have remainingErrors := remaining.materialize registry faults remainingErrorsGiven
  exact @Tree.ErrorsFor.whileLoop layouts owner active frame globals onError values source expressionSyntax
    certificates definitions administrative diagnosticPolicy registry faults context scope mode id node condition conditionNode
    statements rest expected type conditionCode loopCode body selfReason found form conditionFound conditionType
    conditionTree loopBody.tree nativeTyped remaining.tree loopBodyErrors remainingErrors

def assign
    {context scope mode id node assignment operator rhs rest expected type body}
    (found : source.lookupStatement? id = some node)
    (form : node.form = .assignValue assignment operator rhs)
    (head : GenericAssignmentStatements.Head values source context (certificates context) scope administrative definitions assignment operator rhs)
    (headDiagnostics : SourceCoreRawMetadata.Registry → FunctionCalls.FaultRep → Prop)
    (headErrors : ∀ registry faults, headDiagnostics registry faults → head.ErrorsFor diagnosticPolicy registry faults)
    (remaining : DiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode rest) expected type body) :
    DiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode (id :: rest)) expected type (head.emit body (LocalLoop.controlType type)) := by
  refine ⟨(@Tree.assign layouts owner active frame globals onError values source expressionSyntax certificates
    definitions administrative context scope mode id node assignment operator rhs rest expected type body found form
    head remaining.tree), (fun registry faults => remaining.diagnostics registry faults ∧ headDiagnostics registry faults), ?_⟩
  intro registry faults provided
  rcases provided with ⟨remainingErrorsGiven, headErrorsGiven⟩
  have remainingErrors := remaining.materialize registry faults remainingErrorsGiven
  exact @Tree.ErrorsFor.assign layouts owner active frame globals onError values source expressionSyntax certificates
    definitions administrative diagnosticPolicy registry faults context scope mode id node assignment operator rhs rest expected type
    body found form head remaining.tree remainingErrors (headErrors registry faults headErrorsGiven)

def bitNot
    {context scope mode id node assignment rest expected type body}
    (found : source.lookupStatement? id = some node)
    (form : node.form = .assignBitNot assignment)
    (head : CompatibleBitNotStatements.Head context scope assignment)
    (remaining : DiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode rest) expected type body) :
    DiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode (id :: rest)) expected type (head.emit body (LocalLoop.controlType type)) := by
  refine ⟨(@Tree.bitNot layouts owner active frame globals onError values source expressionSyntax certificates
    definitions administrative context scope mode id node assignment rest expected type body found form head
    remaining.tree), (fun registry faults => remaining.diagnostics registry faults ∧ head.Errors faults), ?_⟩
  intro registry faults provided
  rcases provided with ⟨remainingErrorsGiven, headErrors⟩
  have remainingErrors := remaining.materialize registry faults remainingErrorsGiven
  exact @Tree.ErrorsFor.bitNot layouts owner active frame globals onError values source expressionSyntax certificates
    definitions administrative diagnosticPolicy registry faults context scope mode id node assignment rest expected type body found
    form head remaining.tree remainingErrors headErrors

def forLoop
    {context scope mode id node initializer condition post statements rest expected type initialCode body}
    (found : source.lookupStatement? id = some node)
    (form : node.form = .forLoop initializer condition post statements)
    (initial : DiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.initializers initializer condition post statements) expected type initialCode)
    (remaining : DiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode rest) expected type body) :
    DiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode (id :: rest)) expected type (LocalLoop.sequence type initialCode body) := by
  refine ⟨(@Tree.forLoop layouts owner active frame globals onError values source expressionSyntax certificates
    definitions administrative context scope mode id node initializer condition post statements rest expected type
    initialCode body found form initial.tree remaining.tree), (fun registry faults => initial.diagnostics registry
    faults ∧ remaining.diagnostics registry faults), ?_⟩
  intro registry faults provided
  rcases provided with ⟨initialErrorsGiven, remainingErrorsGiven⟩
  have initialErrors := initial.materialize registry faults initialErrorsGiven
  have remainingErrors := remaining.materialize registry faults remainingErrorsGiven
  exact @Tree.ErrorsFor.forLoop layouts owner active frame globals onError values source expressionSyntax certificates
    definitions administrative diagnosticPolicy registry faults context scope mode id node initializer condition post statements rest
    expected type initialCode body found form initial.tree remaining.tree initialErrors remainingErrors

def initializersDone
    {context scope condition conditionNode post statements expected type conditionCode bodyCode postCode selfReason}
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionType : conditionNode.type = .bool)
    (conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩)
    (loopBody : DiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements false statements) expected type bodyCode)
    (postTree : GenericForHeader.DiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source certificates definitions administrative
        type (TypedForHeader.Fallthrough type) context scope post postCode)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        (LocalLoop.iterate type conditionCode bodyCode postCode selfReason) (LocalLoop.resultType type) definitions) :
    DiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.initializers [] condition post statements) expected type
        (LocalLoop.iterate type conditionCode bodyCode postCode selfReason) := by
  refine ⟨(@Tree.initializersDone layouts owner active frame globals onError values source expressionSyntax
    certificates definitions administrative context scope condition conditionNode post statements expected type
    conditionCode bodyCode postCode selfReason conditionFound conditionType conditionTree loopBody.tree postTree.tree
    nativeTyped), (fun registry faults => loopBody.diagnostics registry faults ∧ postTree.diagnostics registry faults), ?_⟩
  intro registry faults provided
  rcases provided with ⟨loopErrorsGiven, postErrors⟩
  have loopErrors := loopBody.materialize registry faults loopErrorsGiven
  exact @Tree.ErrorsFor.initializersDone layouts owner active frame globals onError values source expressionSyntax
    certificates definitions administrative diagnosticPolicy registry faults context scope condition conditionNode post statements
    expected type conditionCode bodyCode postCode selfReason conditionFound conditionType conditionTree
    loopBody.tree postTree.tree nativeTyped loopErrors (postTree.materialize registry faults postErrors)

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
    (remaining : DiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        nextContext ((binder.id, payload) :: scope) (.initializers rest condition post statements) expected type body) :
    DiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.initializers (.letDecl binder none :: rest) condition post statements) expected type (.letE annotation.expression body) := by
  refine ⟨(@Tree.initializerUninitialized layouts owner active frame globals onError values source expressionSyntax
    certificates definitions administrative context nextContext scope binder rest body payload condition post
    statements expected type monomorphic extended ordinary projected allocation annotation same remaining.tree),
    (fun registry faults => remaining.diagnostics registry faults), ?_⟩
  intro registry faults provided
  have remainingErrorsGiven := provided
  have remainingErrors := remaining.materialize registry faults remainingErrorsGiven
  exact @Tree.ErrorsFor.initializerUninitialized layouts owner active frame globals onError values source
    expressionSyntax certificates definitions administrative diagnosticPolicy registry faults context nextContext scope binder rest
    body payload condition post statements expected type monomorphic extended ordinary projected allocation
    annotation same remaining.tree remainingErrors

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
    (remaining : DiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        nextContext ((binder.id, lowered.type) :: scope) (.initializers rest condition post statements) expected type body) :
    DiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.initializers (.letDecl binder (some initializer) :: rest) condition post statements) expected type (sequence type lowered.expression annotation.expression body) := by
  refine ⟨(@Tree.initializerInitialized layouts owner active frame globals onError values source expressionSyntax
    certificates definitions administrative context nextContext scope binder initializer initializerNode lowered
    body rest condition post statements expected type monomorphic extended ordinary initializerFound sourceType
    initial allocation annotation same remaining.tree), (fun registry faults => remaining.diagnostics registry
    faults), ?_⟩
  intro registry faults provided
  have remainingErrorsGiven := provided
  have remainingErrors := remaining.materialize registry faults remainingErrorsGiven
  exact @Tree.ErrorsFor.initializerInitialized layouts owner active frame globals onError values source
    expressionSyntax certificates definitions administrative diagnosticPolicy registry faults context nextContext scope binder
    initializer initializerNode lowered body rest condition post statements expected type monomorphic extended
    ordinary initializerFound sourceType initial allocation annotation same remaining.tree remainingErrors

def initializerDiscard
    {context scope expression expressionNode rest lowered body condition post statements expected type}
    (found : source.lookupExpression? expression = some expressionNode)
    (value : certificates context scope expression lowered)
    (remaining : DiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.initializers rest condition post statements) expected type body) :
    DiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.initializers (.expression expression :: rest) condition post statements) expected type (LocalSequence.discard (LocalLoop.controlType type) lowered.expression body) := by
  refine ⟨(@Tree.initializerDiscard layouts owner active frame globals onError values source expressionSyntax
    certificates definitions administrative context scope expression expressionNode rest lowered body condition post
    statements expected type found value remaining.tree), (fun registry faults => remaining.diagnostics registry
    faults), ?_⟩
  intro registry faults provided
  have remainingErrorsGiven := provided
  have remainingErrors := remaining.materialize registry faults remainingErrorsGiven
  exact @Tree.ErrorsFor.initializerDiscard layouts owner active frame globals onError values source expressionSyntax
    certificates definitions administrative diagnosticPolicy registry faults context scope expression expressionNode rest lowered
    body condition post statements expected type found value remaining.tree remainingErrors

def initializerAssign
    {context scope assignment operator rhs rest body condition post statements expected type}
    (head : GenericAssignmentStatements.Head values source context (certificates context) scope administrative definitions assignment operator rhs)
    (headDiagnostics : SourceCoreRawMetadata.Registry → FunctionCalls.FaultRep → Prop)
    (headErrors : ∀ registry faults, headDiagnostics registry faults → head.ErrorsFor diagnosticPolicy registry faults)
    (remaining : DiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.initializers rest condition post statements) expected type body) :
    DiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.initializers (.assignValue assignment operator rhs :: rest) condition post statements) expected type (head.emit body (LocalLoop.controlType type)) := by
  refine ⟨(@Tree.initializerAssign layouts owner active frame globals onError values source expressionSyntax
    certificates definitions administrative context scope assignment operator rhs rest body condition post
    statements expected type head remaining.tree), (fun registry faults => remaining.diagnostics registry faults ∧
    headDiagnostics registry faults), ?_⟩
  intro registry faults provided
  rcases provided with ⟨remainingErrorsGiven, headErrorsGiven⟩
  have remainingErrors := remaining.materialize registry faults remainingErrorsGiven
  exact @Tree.ErrorsFor.initializerAssign layouts owner active frame globals onError values source expressionSyntax
    certificates definitions administrative diagnosticPolicy registry faults context scope assignment operator rhs rest body
    condition post statements expected type head remaining.tree remainingErrors (headErrors registry faults headErrorsGiven)

def initializerBitNot
    {context scope assignment rest body condition post statements expected type}
    (head : CompatibleBitNotStatements.Head context scope assignment)
    (remaining : DiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.initializers rest condition post statements) expected type body) :
    DiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.initializers (.assignBitNot assignment :: rest) condition post statements) expected type (head.emit body (LocalLoop.controlType type)) := by
  refine ⟨(@Tree.initializerBitNot layouts owner active frame globals onError values source expressionSyntax
    certificates definitions administrative context scope assignment rest body condition post statements expected
    type head remaining.tree), (fun registry faults => remaining.diagnostics registry faults ∧ head.Errors faults),
    ?_⟩
  intro registry faults provided
  rcases provided with ⟨remainingErrorsGiven, headErrors⟩
  have remainingErrors := remaining.materialize registry faults remainingErrorsGiven
  exact @Tree.ErrorsFor.initializerBitNot layouts owner active frame globals onError values source expressionSyntax
    certificates definitions administrative diagnosticPolicy registry faults context scope assignment rest body condition post
    statements expected type head remaining.tree remainingErrors headErrors

end DiagnosticExtraction

open CallableAncestryPairedLookup CompatiblePayload

/-- Feed the same emitted Tree and its materialized laws into the existing body receipt. -/
def DiagnosticExtraction.named_body {diagnosticPolicy : AssignmentDiagnosticPolicy}
    {checked : Checked} {base : Base checked}
    {prepared : SourceCoreCallableIndexedAncestry.Prepared base}
    {values : SourceCoreCompatibleValues.Context}
    {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}
    {bodies : NamedCallExpressions.Bodies prepared values ambient.definitions program}
    {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {compilation : SourceCoreFunctions.Context} {expressionFuel : Nat}
    {source : TypedSource} {expressionSyntax : ExpressionId → Prop} {context : SourceSemantics.Context}
    {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
    {administrative : Core.Context}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    {scope : SourceCoreLocalCell.Scope} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {policy : SourceCoreLoops.Policy}
    {fuel : Nat} {fellThrough escaped : Word} {code flow : Expr}
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope
      statements type reasonAt fellThrough escaped = .ok code)
    (projection : values.checked.catalog.project expected = .ok type)
    (generated : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope
      statements type reasonAt true escaped = .ok flow)
    (extracted : DiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax
      (fun nextContext => NamedCallExpressions.Tree bodies compilation expressionFuel source nextContext solved reasonAt)
      ambient.definitions administrative context scope (.statements true statements) expected type flow)
    (interpreted : extracted.diagnostics registry faults) :
    NamedForFunctionBody.CertificateFor diagnosticPolicy bodies layouts owner active frame globals onError compilation expressionFuel
      source expressionSyntax context solved reasonAt administrative registry faults scope statements
      expected type policy fuel fellThrough escaped code :=
  NamedForFunctionBody.of_extracted_for accepted projection generated extracted.tree (extracted.materialize registry faults interpreted)

/-- Feed the same emitted Tree and its materialized laws into the existing body receipt. -/
def DiagnosticExtraction.catalog_profile {diagnosticPolicy : AssignmentDiagnosticPolicy}
    {checked : Checked} {base : Base checked}
    {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
    {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}
    {headers : RecursiveNamedCatalog.Inventory prepared values ambient.definitions program}
    {header : RecursiveNamedCatalog.Header prepared values ambient.definitions program}
    {compilation : SourceCoreFunctions.Context} {expressionFuel : Nat}
    {expressionSyntax : ExpressionId → Prop} {administrative : Core.Context}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep} {flow : Expr}
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy header.policy header.fuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body
      header.output header.reasonAt header.fellThrough header.escaped = .ok header.body)
    (projection : values.checked.catalog.project header.function.resultType = .ok header.output)
    (generated : SourceCoreLoops.lowerFlowStatementsWithPolicy header.policy header.fuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body
      header.output header.reasonAt true header.escaped = .ok flow)
    (extracted : DiagnosticExtraction diagnosticPolicy header.layouts header.owner header.active prepared.layout.frame header.globals
      header.onError values header.function.source expressionSyntax
      (fun context => RecursiveNamedCatalog.Expressions headers compilation expressionFuel header.function.source context header.solved header.reasonAt)
      ambient.definitions administrative header.context
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      (.statements true header.function.body) header.function.resultType header.output flow)
    (interpreted : extracted.diagnostics registry faults) :
    RecursiveNamedCatalog.ProfileFor diagnosticPolicy headers header compilation expressionFuel expressionSyntax administrative registry faults :=
  RecursiveNamedCatalog.ProfileFor.of_extracted accepted projection generated extracted.tree (extracted.materialize registry faults interpreted)

end Solcore.SourceSemantics.CoreLowering.GenericImperativeFor
