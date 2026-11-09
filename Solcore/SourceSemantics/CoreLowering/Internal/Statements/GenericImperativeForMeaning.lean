import Solcore.SourceSemantics.CoreLowering.Internal.Statements.NamedFunctionLoops
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CatalogEntries
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.GenericImperativeForTrees
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.GenericForHeaderTrees
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.TypedImperativeForTrees
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.GenericImperativeFor

/-!
# Generic imperative for loops: meaning

Prepared diagnostics, certificates and meaning of `for` loops.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GenericImperativeForPreparedDiagnostics
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
    (initialValid : CompatibleExpressionLiterals.ContextValid header.solved header.context header.function.evidence)
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
  RecursiveNamedCatalog.ProfileFor.of_extracted initialValid accepted projection generated extracted.tree (extracted.materialize registry faults interpreted)

end Solcore.SourceSemantics.CoreLowering.GenericImperativeFor
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GenericImperativeForCertificates
/-! Real native typing is inverted along emitted lexical/assignment/loop
wrappers. Generic expression extraction consumes retained source syntax and
source typing; native equality is not used to infer either of those facts. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericImperativeFor
open Core Frontend SourceInference
open TypedImperativeFor (Accepted InitialAccepted)
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource}
  {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {reasonAt : ExpressionId → Word}
  {definitions : DataEnvironment} {administrative : Core.Context}

open CompatibleEncoding (bind_ok)

private theorem unary_read_found {checked : SourceCoreCompatibleCatalog.Checked} {source : TypedSource}
    {id : StatementId} {node : StatementNode} {type : Ty}
    (accepted : SourceCoreCompatibleDataExpressions.readStatement checked source id = .ok (node, type)) :
    source.lookupStatement? id = some node := by
  unfold SourceCoreCompatibleDataExpressions.readStatement at accepted
  by_cases owner : id.occurrence.owner ≠ source.owner
  · simp [owner, throw, bind, Except.bind] at accepted
  · simp only [owner, ↓reduceIte, bind, Except.bind, pure, Except.pure] at accepted
    cases found : source.lookupStatement? id with
    | none => simp [found] at accepted
    | some actual =>
      simp only [found] at accepted
      obtain ⟨projected, _, same⟩ := bind_ok accepted
      cases same
      rfl

open CompatibleStatementBindings (binder_projected scope_bind)

private theorem unary_ensure_same {site : SourceCoreElaboration.ErrorSite} {expected actual : Ty}
    (accepted : SourceCoreBasic.ensureType site expected actual = .ok ()) : expected = actual := by
  unfold SourceCoreBasic.ensureType at accepted
  split at accepted
  · assumption
  · cases accepted

variable {policy : SourceCoreLoops.Policy}
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Solcore.Syntax.ValueAssignOp → Word}
  {invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}

/-- This extraction consumes one native typing receipt for the actual output.
Source grammar, expression typing and authenticated allocator policies remain
static inputs, independently of native type equality. -/
theorem extraction_of_typed_position_with_residual (residualMode : Bool) (diagnosticPolicy : AssignmentDiagnosticPolicy) {tracked : Bool}
    (factory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy source invalidOperand)
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
    {context : SourceSemantics.Context} {scope : Scope} {position : Position} {expected : TypeSystem.Ty}
    (syntaxTree : Syntax source expressionSyntax context position expected)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = residualMode)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {fuel : Nat} {type : Ty} {code : Expr} {selfReason : Word} {nativeType : Ty}
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : AssignmentDiagnosticOrigins.AcceptedFor tracked policy fuel source scope position type reasonAt selfReason code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType definitions) :
    Nonempty (DiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
      context scope position expected type code) := by
  classical
  induction syntaxTree generalizing scope fuel code nativeType with
  | body syntaxTree => exact ⟨DiagnosticExtraction.body syntaxTree (GenericLexicalStatements.tree_of_flow_with_residual residualMode readPolicy binderPolicy allocationPolicy expressions syntaxTree closed residual sourceSignatures declarations projection accepted)⟩
  | @uninitialized context nextContext mode id node binder rest expected found form declaration monomorphic extended ordinary remaining ih =>
    simp only [AssignmentDiagnosticOrigins.AcceptedFor] at accepted
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((unary_read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      obtain ⟨payload, projected, accepted⟩ := bind_ok accepted
      obtain ⟨body, generated, accepted⟩ := bind_ok accepted
      simp only [SourceCoreSourceCells.letUninitialized, allocationPolicy] at accepted
      obtain ⟨allocationCode, generatedAllocation, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨allocation, annotation, same, rfl⟩ :=
        CallableIndexedAllocationCompletion.accepted_receipts onError generatedAllocation
      exact ⟨DiagnosticExtraction.uninitialized found form monomorphic extended ordinary (binder_projected (binderPolicy scope binder monomorphic ▸ projected))
        allocation annotation same (Classical.choice (ih (by cases extended; exact closed) (by cases extended; exact residual) (by cases extended; exact sourceSignatures)
          (scope_bind payload declarations declaration extended) projection generated (TypedLexicalWhile.Native.absent_child allocation annotation same nativeTyped)))⟩

  | @initialized context nextContext mode id node binder initializer initializerNode rest expected found form declaration mono extended ordinary initializerFound sourceType typed initializerSyntax remaining ih =>
    simp only [AssignmentDiagnosticOrigins.AcceptedFor] at accepted
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have identical := Option.some.inj ((unary_read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      obtain ⟨payload, projected, accepted⟩ := bind_ok accepted
      obtain ⟨lowered, generated, accepted⟩ := bind_ok accepted
      obtain ⟨checked, checkedType, accepted⟩ := bind_ok accepted
      cases checked
      have sameType := unary_ensure_same checkedType
      subst payload
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      simp only [mono, List.isEmpty_nil, ↓reduceIte] at accepted
      simp only [SourceCoreSourceCells.letInitialized, allocationPolicy] at accepted
      obtain ⟨allocationCode, generatedAllocation, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨allocation, annotation, same, rfl⟩ := CallableIndexedAllocationCompletion.accepted_receipts onError generatedAllocation
      exact ⟨DiagnosticExtraction.initialized found form mono extended ordinary initializerFound sourceType
        (expressions context closed residual sourceSignatures declarations initializerSyntax initializerFound typed generated)
        allocation annotation same
        (Classical.choice (ih (by cases extended; exact closed) (by cases extended; exact residual) (by cases extended; exact sourceSignatures)
          (scope_bind lowered.type declarations declaration extended) projection generatedBody (TypedLexicalWhile.Native.initialized_child allocation annotation same nativeTyped)))⟩

  | @discard context mode id node expression expressionNode semicolon rest expected found form notTail sourceType expressionFound typed syntaxValue remaining ih =>
    simp only [AssignmentDiagnosticOrigins.AcceptedFor] at accepted
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((unary_read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨lowered, generated, accepted⟩ := bind_ok accepted
      simp only [notTail, Bool.false_eq_true, ↓reduceIte] at accepted
      cases semicolon <;> simp only [Bool.false_eq_true, ↓reduceIte] at accepted
      all_goals
        obtain ⟨checked, _, accepted⟩ := bind_ok accepted
        cases checked
        obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
        cases accepted
        obtain ⟨_, tailTyped⟩ := TypedLexicalWhile.Native.discard_child nativeTyped
        exact ⟨DiagnosticExtraction.discard found form notTail expressionFound (expressions context closed residual sourceSignatures declarations syntaxValue expressionFound typed generated)
          (Classical.choice (ih closed residual sourceSignatures declarations projection generatedBody tailTyped))⟩

  | @block context mode id node statements rest expected found form sourceType inner remaining innerIH restIH =>
    simp only [AssignmentDiagnosticOrigins.AcceptedFor] at accepted
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((unary_read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨innerCode, generatedInner, accepted⟩ := bind_ok accepted
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨⟨_, headTyped⟩, ⟨_, tailTyped⟩⟩ := TypedLexicalWhile.Native.sequence_children nativeTyped
      exact ⟨DiagnosticExtraction.block found form (Classical.choice (innerIH closed residual sourceSignatures declarations projection generatedInner headTyped)) (Classical.choice (restIH closed residual sourceSignatures declarations projection generatedBody tailTyped))⟩
  | @ifThen context mode id node condition conditionNode thenBody elseBody rest expected found form sourceType conditionFound conditionType typed conditionSyntax thenSyntax elseSyntax remaining thenIH elseIH restIH =>
    simp only [AssignmentDiagnosticOrigins.AcceptedFor] at accepted
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((unary_read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨conditionCode, generatedCondition, accepted⟩ := bind_ok accepted
      obtain ⟨checked, checkedCondition, accepted⟩ := bind_ok accepted
      cases checked
      have conditionTypeEq := unary_ensure_same checkedCondition
      rcases conditionCode with ⟨native, code⟩
      dsimp only at conditionTypeEq
      subst native
      obtain ⟨thenCode, generatedThen, accepted⟩ := bind_ok accepted
      cases elseBody with
      | none =>
        simp only [bind, Except.bind, pure, Except.pure] at accepted
        obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
        cases accepted
        have generatedElse : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope [] type reasonAt false selfReason =
            .ok (LocalLoop.fallthrough type) := by cases fuel <;> rfl
        obtain ⟨⟨_, branchTyped⟩, ⟨_, tailTyped⟩⟩ := TypedLexicalWhile.Native.sequence_children nativeTyped
        obtain ⟨⟨_, thenTyped⟩, ⟨_, elseTyped⟩⟩ := TypedLexicalWhile.Native.conditional_children branchTyped
        exact ⟨DiagnosticExtraction.ifThen found form conditionFound conditionType
          (expressions context closed residual sourceSignatures declarations conditionSyntax conditionFound typed generatedCondition)
          (Classical.choice (thenIH closed residual sourceSignatures declarations projection generatedThen thenTyped)) (Classical.choice (elseIH closed residual sourceSignatures declarations projection generatedElse elseTyped)) (Classical.choice (restIH closed residual sourceSignatures declarations projection generatedBody tailTyped))⟩
      | some statements =>
        obtain ⟨elseCode, generatedElse, accepted⟩ := bind_ok accepted
        obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
        cases accepted
        obtain ⟨⟨_, branchTyped⟩, ⟨_, tailTyped⟩⟩ := TypedLexicalWhile.Native.sequence_children nativeTyped
        obtain ⟨⟨_, thenTyped⟩, ⟨_, elseTyped⟩⟩ := TypedLexicalWhile.Native.conditional_children branchTyped
        exact ⟨DiagnosticExtraction.ifThen found form conditionFound conditionType
          (expressions context closed residual sourceSignatures declarations conditionSyntax conditionFound typed generatedCondition)
          (Classical.choice (thenIH closed residual sourceSignatures declarations projection generatedThen thenTyped)) (Classical.choice (elseIH closed residual sourceSignatures declarations projection generatedElse elseTyped)) (Classical.choice (restIH closed residual sourceSignatures declarations projection generatedBody tailTyped))⟩


  | @terminalBlock context mode id node statements rest expected exactUnique found form sourceType inner stops innerIH =>
    simp only [AssignmentDiagnosticOrigins.AcceptedFor] at accepted
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((unary_read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨innerCode, generatedInner, accepted⟩ := bind_ok accepted
      obtain ⟨suffix, generatedSuffix, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨⟨_, headTyped⟩, _⟩ := TypedLexicalWhile.Native.sequence_children nativeTyped
      let child := Classical.choice (innerIH closed residual sourceSignatures declarations projection generatedInner headTyped)
      let issued := GenericLexicalStatements.IssuedSuffix.of_accepted generatedSuffix
      refine ⟨⟨.terminalBlock exactUnique found form child.tree stops issued, child.diagnostics, ?_⟩⟩
      intro registry faults provided
      exact .terminalBlock (unique := exactUnique) (found := found) (form := form)
        (stops := stops) (issued := issued) (child.materialize registry faults provided)
  | @terminalIf context mode id node condition conditionNode thenBody elseBody rest expected exactUnique found form sourceType conditionFound conditionType typed conditionSyntax thenSyntax elseSyntax thenStops elseStops thenIH elseIH =>
    simp only [AssignmentDiagnosticOrigins.AcceptedFor] at accepted
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((unary_read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨conditionCode, generatedCondition, accepted⟩ := bind_ok accepted
      obtain ⟨checked, checkedCondition, accepted⟩ := bind_ok accepted
      cases checked
      have sameType := unary_ensure_same checkedCondition
      rcases conditionCode with ⟨native, code⟩
      dsimp only at sameType
      subst native
      obtain ⟨thenCode, generatedThen, accepted⟩ := bind_ok accepted
      obtain ⟨elseCode, generatedElse, accepted⟩ := bind_ok accepted
      obtain ⟨suffix, generatedSuffix, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨⟨_, branchTyped⟩, _⟩ := TypedLexicalWhile.Native.sequence_children nativeTyped
      obtain ⟨⟨_, thenTyped⟩, ⟨_, elseTyped⟩⟩ := TypedLexicalWhile.Native.conditional_children branchTyped
      let left := Classical.choice (thenIH closed residual sourceSignatures declarations projection generatedThen thenTyped)
      let right := Classical.choice (elseIH closed residual sourceSignatures declarations projection generatedElse elseTyped)
      let conditionTree := expressions context closed residual sourceSignatures declarations conditionSyntax conditionFound typed generatedCondition
      let issued := GenericLexicalStatements.IssuedSuffix.of_accepted generatedSuffix
      refine ⟨⟨.terminalIf exactUnique found form conditionFound conditionType conditionTree left.tree right.tree thenStops elseStops issued,
        (fun registry faults => left.diagnostics registry faults ∧ right.diagnostics registry faults), ?_⟩⟩
      intro registry faults provided
      exact .terminalIf (unique := exactUnique) (found := found) (form := form)
        (conditionFound := conditionFound) (conditionType := conditionType) (conditionTree := conditionTree)
        (thenStops := thenStops) (elseStops := elseStops) (issued := issued)
        (left.materialize registry faults provided.1) (right.materialize registry faults provided.2)

  | @breaking context mode id node rest expected found form =>
    simp only [AssignmentDiagnosticOrigins.AcceptedFor] at accepted
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((unary_read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      cases accepted
      exact ⟨DiagnosticExtraction.breaking found form⟩
  | @continuing context mode id node rest expected found form =>
    simp only [AssignmentDiagnosticOrigins.AcceptedFor] at accepted
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((unary_read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      cases accepted
      exact ⟨DiagnosticExtraction.continuing found form⟩
  | @whileLoop context mode id node condition conditionNode statements rest expected found form conditionFound conditionType typed conditionSyntax loopSyntax remaining loopIH restIH =>
    simp only [AssignmentDiagnosticOrigins.AcceptedFor] at accepted
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((unary_read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      obtain ⟨conditionCode, generatedCondition, accepted⟩ := bind_ok accepted
      obtain ⟨checked, checkedCondition, accepted⟩ := bind_ok accepted
      cases checked
      have sameType := unary_ensure_same checkedCondition
      rcases conditionCode with ⟨native, code⟩
      dsimp only at sameType
      subst native
      obtain ⟨loopCode, generatedLoop, accepted⟩ := bind_ok accepted
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨⟨_, loopTyped⟩, ⟨_, tailTyped⟩⟩ := TypedLexicalWhile.Native.sequence_children nativeTyped
      obtain ⟨⟨_, loopBodyTyped⟩, loopTyped⟩ := TypedLexicalWhile.Native.while_body loopTyped
      exact ⟨DiagnosticExtraction.whileLoop found form conditionFound conditionType
        (expressions context closed residual sourceSignatures declarations conditionSyntax conditionFound typed generatedCondition)
        (Classical.choice (loopIH closed residual sourceSignatures declarations projection generatedLoop loopBodyTyped))
        loopTyped
        (Classical.choice (restIH closed residual sourceSignatures declarations projection generatedBody tailTyped))⟩

  | @assign context mode id node assignment operator rhs rest expected found form sourceTyped writable rightTyped profile children remaining ih =>
    simp only [AssignmentDiagnosticOrigins.AcceptedFor] at accepted
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((unary_read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      obtain ⟨body, compiledBody, accepted⟩ := bind_ok accepted
      have compiled : SourceCoreCompatibleDataPlaces.lower values values.checked.signatures policy.lowerExpression fuel source scope (.occurrence id.occurrence)
          assignment operator (some rhs) (LocalLoop.controlType type) body reasonAt
          (invalidProjection (.occurrence id.occurrence) assignment.target.root)
          (invalidOperand (.occurrence id.occurrence) assignment.target.root operator)
          (missingDefault (.occurrence id.occurrence) assignment.target.root) = .ok code := by
        cases operator <;> simpa only [SourceCoreLoops.assignValue, assignments.equal, assignments.value] using accepted
      obtain ⟨head, rfl, sameToken⟩ := GenericAssignmentStatements.Head.of_lower_with_token unique sourceSignatures sourceTyped writable rightTyped profile
        (fun id lowered member generated => by
          obtain ⟨syntaxTree, node, found, typed⟩ := children id member
          exact ⟨node, found, assignmentExpressions context scope fuel id lowered closed residual sourceSignatures declarations syntaxTree node found typed generated⟩) compiled nativeTyped
      exact ⟨DiagnosticExtraction.assign found form head (factory.residual head)
        (factory.materialize head (.occurrence id.occurrence) (AssignmentDiagnosticOrigins.OccursFor.statement found form) sameToken) (Classical.choice (ih closed residual sourceSignatures declarations projection compiledBody (TypedImperative.Native.execute_continuation nativeTyped)))⟩

  | @forLoop context mode id node initializer condition post statements rest expected found form sourceType initial remaining initialIH restIH =>
    simp only [AssignmentDiagnosticOrigins.AcceptedFor] at accepted
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((unary_read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      obtain ⟨initialCode, generatedInitial, accepted⟩ := bind_ok accepted
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨⟨_, initialTyped⟩, ⟨_, tailTyped⟩⟩ := TypedLexicalWhile.Native.sequence_children nativeTyped
      refine ⟨DiagnosticExtraction.forLoop found form ?_ ?_⟩
      · apply Classical.choice
        apply initialIH closed residual sourceSignatures declarations projection (nativeTyped := initialTyped)
        refine ⟨fuel, .occurrence id.occurrence, _, AssignmentDiagnosticOrigins.ForOriginFor.start found form, generatedInitial, ?_⟩
        intro loopScope nextCode generated
        obtain ⟨conditionCode, conditionGenerated, generated⟩ := bind_ok generated
        obtain ⟨checked, conditionChecked, generated⟩ := bind_ok generated
        cases checked
        obtain ⟨loopCode, loopGenerated, generated⟩ := bind_ok generated
        obtain ⟨postCode, postGenerated, generated⟩ := bind_ok generated
        cases generated
        exact ⟨conditionCode, loopCode, postCode, conditionGenerated, (unary_ensure_same conditionChecked).symm, loopGenerated, postGenerated, rfl⟩
      · exact Classical.choice (restIH closed residual sourceSignatures declarations projection generatedBody tailTyped)
  | @initializersDone context condition conditionNode post statements expected conditionFound conditionType typed conditionSyntax loopBody postSyntax loopIH =>
    obtain ⟨headerFuel, parentSite, next, origin, generated, nextReceipt⟩ := accepted
    have nextAccepted : next scope = .ok code := by cases headerFuel <;> exact generated
    obtain ⟨conditionCode, loopCode, postCode, conditionGenerated, conditionChecked, loopGenerated, postGenerated, rfl⟩ :=
      nextReceipt scope code nextAccepted
    rcases conditionCode with ⟨native, expression⟩
    dsimp only at conditionChecked
    subst native
    obtain ⟨⟨_, bodyTyped⟩, ⟨_, postTyped⟩, loopTyped⟩ := TypedImperativeFor.Native.iterate_children nativeTyped
    exact ⟨DiagnosticExtraction.initializersDone conditionFound conditionType
      (expressions context closed residual sourceSignatures declarations conditionSyntax conditionFound typed conditionGenerated)
      (Classical.choice (loopIH closed residual sourceSignatures declarations projection loopGenerated bodyTyped))
      (Classical.choice (GenericForHeader.extraction_of_lowerForItems_with_residual residualMode factory binderPolicy allocationPolicy assignments unaryPolicy unique assignmentExpressions
        (fun _ _ _ _ _ _ _ same => by cases same; rfl) postSyntax closed residual sourceSignatures declarations postGenerated postTyped origin.post_origin))
      loopTyped⟩
  | @initializerUninitialized context nextContext binder rest condition post statements expected declaration monomorphic extended ordinary remaining ih =>
    obtain ⟨headerFuel, parentSite, next, origin, accepted, nextReceipt⟩ := accepted
    cases headerFuel with
    | zero => cases accepted
    | succ headerFuel =>
      simp only [SourceCoreLoops.lowerForItems] at accepted
      obtain ⟨payload, projected, accepted⟩ := bind_ok accepted
      obtain ⟨body, generated, accepted⟩ := bind_ok accepted
      simp only [SourceCoreSourceCells.letUninitialized, allocationPolicy] at accepted
      obtain ⟨allocationCode, generatedAllocation, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨allocation, annotation, same, rfl⟩ :=
        CallableIndexedAllocationCompletion.accepted_receipts onError generatedAllocation
      exact ⟨DiagnosticExtraction.initializerUninitialized monomorphic extended ordinary (binder_projected (binderPolicy scope binder monomorphic ▸ projected))
        allocation annotation same (Classical.choice (ih (by cases extended; exact closed) (by cases extended; exact residual) (by cases extended; exact sourceSignatures)
          (scope_bind payload declarations declaration extended) projection ⟨headerFuel, parentSite, next, origin.tail, generated, nextReceipt⟩ (TypedLexicalWhile.Native.absent_child allocation annotation same nativeTyped)))⟩
  | @initializerInitialized context nextContext binder initializer initializerNode rest condition post statements expected declaration mono extended ordinary initializerFound sourceType typed initializerSyntax remaining ih =>
    obtain ⟨headerFuel, parentSite, next, origin, accepted, nextReceipt⟩ := accepted
    cases headerFuel with
    | zero => cases accepted
    | succ headerFuel =>
      simp only [SourceCoreLoops.lowerForItems] at accepted
      obtain ⟨payload, projected, accepted⟩ := bind_ok accepted
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      obtain ⟨lowered, generated, accepted⟩ := bind_ok accepted
      obtain ⟨checked, checkedType, accepted⟩ := bind_ok accepted
      cases checked
      have sameType := unary_ensure_same checkedType
      subst payload
      simp only [mono, List.isEmpty_nil, ↓reduceIte] at accepted
      simp only [SourceCoreSourceCells.letInitialized, allocationPolicy] at accepted
      obtain ⟨allocationCode, generatedAllocation, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨allocation, annotation, same, rfl⟩ := CallableIndexedAllocationCompletion.accepted_receipts onError generatedAllocation
      have initial := expressions context closed residual sourceSignatures declarations initializerSyntax initializerFound typed generated
      exact ⟨DiagnosticExtraction.initializerInitialized mono extended ordinary initializerFound sourceType initial allocation annotation same
        (Classical.choice (ih (by cases extended; exact closed) (by cases extended; exact residual) (by cases extended; exact sourceSignatures)
          (scope_bind lowered.type declarations declaration extended) projection ⟨headerFuel, parentSite, next, origin.tail, generatedBody, nextReceipt⟩ (TypedLexicalWhile.Native.initialized_child allocation annotation same nativeTyped)))⟩
  | @initializerDiscard context expression expressionNode rest condition post statements expected found typed syntaxTree remaining ih =>
    obtain ⟨headerFuel, parentSite, next, origin, accepted, nextReceipt⟩ := accepted
    cases headerFuel with
    | zero => cases accepted
    | succ headerFuel =>
      simp only [SourceCoreLoops.lowerForItems] at accepted
      obtain ⟨lowered, generated, accepted⟩ := bind_ok accepted
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      cases accepted
      have child := expressions context closed residual sourceSignatures declarations syntaxTree found typed generated
      obtain ⟨_, bodyTyped⟩ := TypedLexicalWhile.Native.discard_child nativeTyped
      exact ⟨DiagnosticExtraction.initializerDiscard found child (Classical.choice (ih closed residual sourceSignatures declarations projection ⟨headerFuel, parentSite, next, origin.tail, generatedBody, nextReceipt⟩ bodyTyped))⟩
  | @initializerAssign context assignment operator rhs rest condition post statements expected sourceTyped writable rightTyped profile children remaining ih =>
    obtain ⟨headerFuel, parentSite, next, origin, accepted, nextReceipt⟩ := accepted
    cases headerFuel with
    | zero => cases accepted
    | succ headerFuel =>
      simp only [SourceCoreLoops.lowerForItems] at accepted
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      have compiled : SourceCoreCompatibleDataPlaces.lower values values.checked.signatures policy.lowerExpression headerFuel source scope parentSite
          assignment operator (some rhs) (LocalLoop.controlType type) body reasonAt
          (invalidProjection parentSite assignment.target.root) (invalidOperand parentSite assignment.target.root operator)
          (missingDefault parentSite assignment.target.root) = .ok code := by
        cases operator <;> simpa only [SourceCoreLoops.assignValue, assignments.equal, assignments.value] using accepted
      obtain ⟨head, rfl, sameToken⟩ := GenericAssignmentStatements.Head.of_lower_with_token unique sourceSignatures sourceTyped writable rightTyped profile
        (fun id lowered member generated => by
          obtain ⟨syntaxTree, node, found, typed⟩ := children id member
          exact ⟨node, found, assignmentExpressions context scope headerFuel id lowered closed residual sourceSignatures declarations syntaxTree node found typed generated⟩) compiled nativeTyped
      exact ⟨DiagnosticExtraction.initializerAssign head (factory.residual head)
        (factory.materialize head parentSite origin.header.operand sameToken) (Classical.choice (ih closed residual sourceSignatures declarations projection ⟨headerFuel, parentSite, next, origin.tail, generatedBody, nextReceipt⟩ (TypedImperative.Native.execute_continuation nativeTyped)))⟩

  | @bitNot context mode id node assignment rest expected found form writable bare profile remaining ih =>
    simp only [AssignmentDiagnosticOrigins.AcceptedFor] at accepted
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((unary_read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      simp only [unaryPolicy] at accepted
      obtain ⟨body, compiledBody, accepted⟩ := bind_ok accepted
      obtain ⟨head, rfl⟩ := CompatibleBitNotStatements.Head.of_lower writable bare profile accepted
      exact ⟨DiagnosticExtraction.bitNot found form head (Classical.choice (ih closed residual sourceSignatures declarations projection compiledBody
        (TypedImperative.Native.execute_continuation nativeTyped)))⟩
  | @initializerBitNot context assignment rest condition post statements expected writable bare profile remaining ih =>
    obtain ⟨headerFuel, parentSite, next, origin, generated, nextReceipt⟩ := accepted
    cases headerFuel with
    | zero => cases generated
    | succ headerFuel =>
      simp only [SourceCoreLoops.lowerForItems, unaryPolicy] at generated
      obtain ⟨body, generatedBody, generated⟩ := bind_ok generated
      obtain ⟨head, rfl⟩ := CompatibleBitNotStatements.Head.of_lower writable bare profile generated
      exact ⟨DiagnosticExtraction.initializerBitNot head (Classical.choice (ih closed residual sourceSignatures declarations projection
        ⟨headerFuel, parentSite, next, origin.tail, generatedBody, nextReceipt⟩ (TypedImperative.Native.execute_continuation nativeTyped)))⟩

/-- Compatibility entry for the former closed residual scope. -/
theorem extraction_of_typed_position (diagnosticPolicy : AssignmentDiagnosticPolicy) {tracked : Bool}
    (factory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy source invalidOperand)
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
    {context : SourceSemantics.Context} {scope : Scope} {position : Position} {expected : TypeSystem.Ty}
    (syntaxTree : Syntax source expressionSyntax context position expected)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {fuel : Nat} {type : Ty} {code : Expr} {selfReason : Word} {nativeType : Ty}
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : AssignmentDiagnosticOrigins.AcceptedFor tracked policy fuel source scope position type reasonAt selfReason code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType definitions) :
    Nonempty (DiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
      context scope position expected type code) := by
  exact extraction_of_typed_position_with_residual false (diagnosticPolicy := diagnosticPolicy) (tracked := tracked)
    (factory := factory) (readPolicy := readPolicy) (binderPolicy := binderPolicy)
    (allocationPolicy := allocationPolicy) (expressions := expressions) (assignments := assignments)
    (unaryPolicy := unaryPolicy) (unique := unique) (assignmentExpressions := assignmentExpressions)
    (context := context) (scope := scope) (position := position) (expected := expected) (syntaxTree := syntaxTree)
    (closed := closed) (residual := residual) (sourceSignatures := sourceSignatures) (declarations := declarations)
    (fuel := fuel) (type := type) (code := code) (selfReason := selfReason) (nativeType := nativeType)
    (projection := projection) (accepted := accepted) (nativeTyped := nativeTyped)

theorem tree_of_typed_position_with_residual (residualMode : Bool)
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
    {context : SourceSemantics.Context} {scope : Scope} {position : Position} {expected : TypeSystem.Ty}
    (syntaxTree : Syntax source expressionSyntax context position expected)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = residualMode)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {fuel : Nat} {type : Ty} {code : Expr} {selfReason : Word} {nativeType : Ty}
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : Accepted policy fuel source scope position type reasonAt selfReason code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType definitions) :
    Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
      context scope position expected type code := by
  obtain ⟨extracted⟩ := extraction_of_typed_position_with_residual residualMode .unconditional
    (AssignmentDiagnosticOrigins.Factory.unchanged .unconditional source invalidOperand) readPolicy binderPolicy allocationPolicy expressions assignments unaryPolicy unique assignmentExpressions syntaxTree closed residual sourceSignatures declarations projection
    (AssignmentDiagnosticOrigins.AcceptedFor.untracked accepted) nativeTyped
  exact extracted.tree

/-- Compatibility entry for the former closed residual scope. -/
theorem tree_of_typed_position
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
    {context : SourceSemantics.Context} {scope : Scope} {position : Position} {expected : TypeSystem.Ty}
    (syntaxTree : Syntax source expressionSyntax context position expected)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {fuel : Nat} {type : Ty} {code : Expr} {selfReason : Word} {nativeType : Ty}
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : Accepted policy fuel source scope position type reasonAt selfReason code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType definitions) :
    Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
      context scope position expected type code := by
  exact tree_of_typed_position_with_residual false (readPolicy := readPolicy) (binderPolicy := binderPolicy)
    (allocationPolicy := allocationPolicy) (expressions := expressions) (assignments := assignments)
    (unaryPolicy := unaryPolicy) (unique := unique) (assignmentExpressions := assignmentExpressions)
    (context := context) (scope := scope) (position := position) (expected := expected) (syntaxTree := syntaxTree)
    (closed := closed) (residual := residual) (sourceSignatures := sourceSignatures) (declarations := declarations)
    (fuel := fuel) (type := type) (code := code) (selfReason := selfReason) (nativeType := nativeType)
    (projection := projection) (accepted := accepted) (nativeTyped := nativeTyped)

theorem extraction_of_typed_flow_with_residual (residualMode : Bool) (diagnosticPolicy : AssignmentDiagnosticPolicy) {tracked : Bool}
    (factory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy source invalidOperand)
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
    {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {statements : List StatementId} {expected : TypeSystem.Ty}
    (syntaxTree : Syntax source expressionSyntax context (.statements mode statements) expected)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = residualMode)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {fuel : Nat} {type : Ty} {code : Expr} {selfReason : Word} {nativeType : Ty}
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope statements type reasonAt mode selfReason = .ok code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType definitions) :
    Nonempty (DiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
      context scope (.statements mode statements) expected type code) := by
  exact extraction_of_typed_position_with_residual residualMode diagnosticPolicy factory readPolicy binderPolicy allocationPolicy expressions assignments unaryPolicy unique assignmentExpressions syntaxTree closed residual sourceSignatures declarations projection accepted nativeTyped

/-- Compatibility entry for the former closed residual scope. -/
theorem extraction_of_typed_flow (diagnosticPolicy : AssignmentDiagnosticPolicy) {tracked : Bool}
    (factory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy source invalidOperand)
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
    {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {statements : List StatementId} {expected : TypeSystem.Ty}
    (syntaxTree : Syntax source expressionSyntax context (.statements mode statements) expected)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {fuel : Nat} {type : Ty} {code : Expr} {selfReason : Word} {nativeType : Ty}
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope statements type reasonAt mode selfReason = .ok code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType definitions) :
    Nonempty (DiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
      context scope (.statements mode statements) expected type code) := by
  exact extraction_of_typed_flow_with_residual false (diagnosticPolicy := diagnosticPolicy) (tracked := tracked)
    (factory := factory) (readPolicy := readPolicy) (binderPolicy := binderPolicy)
    (allocationPolicy := allocationPolicy) (expressions := expressions) (assignments := assignments)
    (unaryPolicy := unaryPolicy) (unique := unique) (assignmentExpressions := assignmentExpressions)
    (context := context) (scope := scope) (mode := mode) (statements := statements) (expected := expected)
    (syntaxTree := syntaxTree) (closed := closed) (residual := residual) (sourceSignatures := sourceSignatures)
    (declarations := declarations) (fuel := fuel) (type := type) (code := code) (selfReason := selfReason)
    (nativeType := nativeType) (projection := projection) (accepted := accepted) (nativeTyped := nativeTyped)

theorem tree_of_typed_flow_with_residual (residualMode : Bool)
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
    {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {statements : List StatementId} {expected : TypeSystem.Ty}
    (syntaxTree : Syntax source expressionSyntax context (.statements mode statements) expected)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = residualMode)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {fuel : Nat} {type : Ty} {code : Expr} {selfReason : Word} {nativeType : Ty}
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope statements type reasonAt mode selfReason = .ok code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType definitions) :
    Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
      context scope (.statements mode statements) expected type code := by
  obtain ⟨extracted⟩ := extraction_of_typed_flow_with_residual residualMode .unconditional
    (AssignmentDiagnosticOrigins.Factory.unchanged .unconditional source invalidOperand) readPolicy binderPolicy allocationPolicy expressions assignments unaryPolicy unique assignmentExpressions syntaxTree closed residual sourceSignatures declarations projection accepted nativeTyped
  exact extracted.tree

/-- Compatibility entry for the former closed residual scope. -/
theorem tree_of_typed_flow
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
    {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {statements : List StatementId} {expected : TypeSystem.Ty}
    (syntaxTree : Syntax source expressionSyntax context (.statements mode statements) expected)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {fuel : Nat} {type : Ty} {code : Expr} {selfReason : Word} {nativeType : Ty}
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope statements type reasonAt mode selfReason = .ok code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType definitions) :
    Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
      context scope (.statements mode statements) expected type code := by
  exact tree_of_typed_flow_with_residual false (readPolicy := readPolicy) (binderPolicy := binderPolicy)
    (allocationPolicy := allocationPolicy) (expressions := expressions) (assignments := assignments)
    (unaryPolicy := unaryPolicy) (unique := unique) (assignmentExpressions := assignmentExpressions)
    (context := context) (scope := scope) (mode := mode) (statements := statements) (expected := expected)
    (syntaxTree := syntaxTree) (closed := closed) (residual := residual) (sourceSignatures := sourceSignatures)
    (declarations := declarations) (fuel := fuel) (type := type) (code := code) (selfReason := selfReason)
    (nativeType := nativeType) (projection := projection) (accepted := accepted) (nativeTyped := nativeTyped)

theorem extraction_of_typed_body_with_residual (residualMode : Bool) (diagnosticPolicy : AssignmentDiagnosticPolicy) {tracked : Bool}
    (factory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy source invalidOperand)
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
    {context : SourceSemantics.Context} {scope : Scope} {statements : List StatementId} {expected : TypeSystem.Ty}
    (syntaxTree : Syntax source expressionSyntax context (.statements true statements) expected)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = residualMode)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {fuel : Nat} {type nativeType : Ty} {code : Expr} {fellThrough escaped : Word}
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope statements type reasonAt fellThrough escaped = .ok code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType definitions) :
    ∃ flow,
      SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope statements type reasonAt true escaped = .ok flow ∧
      ∃ _extracted : DiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements true statements) expected type flow,
      code = LocalControl.finish type (LocalLoop.toControl type flow escaped)
        (if type = .unit then LanguageResult.success .unit else LanguageResult.failure type (.word fellThrough)) := by
  unfold SourceCoreLoops.lowerStatementsWithPolicy at accepted
  obtain ⟨flow, generated, same⟩ := bind_ok accepted
  cases same
  obtain ⟨_, flowTyped⟩ := TypedLexicalWhile.Native.finished_flow nativeTyped
  obtain ⟨extracted⟩ := extraction_of_typed_flow_with_residual residualMode diagnosticPolicy factory readPolicy binderPolicy allocationPolicy expressions assignments unaryPolicy unique assignmentExpressions syntaxTree closed residual sourceSignatures declarations projection generated flowTyped
  exact ⟨flow, generated, extracted, rfl⟩

/-- Compatibility entry for the former closed residual scope. -/
theorem extraction_of_typed_body (diagnosticPolicy : AssignmentDiagnosticPolicy) {tracked : Bool}
    (factory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy source invalidOperand)
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
    {context : SourceSemantics.Context} {scope : Scope} {statements : List StatementId} {expected : TypeSystem.Ty}
    (syntaxTree : Syntax source expressionSyntax context (.statements true statements) expected)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {fuel : Nat} {type nativeType : Ty} {code : Expr} {fellThrough escaped : Word}
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope statements type reasonAt fellThrough escaped = .ok code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType definitions) :
    ∃ flow,
      SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope statements type reasonAt true escaped = .ok flow ∧
      ∃ _extracted : DiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements true statements) expected type flow,
      code = LocalControl.finish type (LocalLoop.toControl type flow escaped)
        (if type = .unit then LanguageResult.success .unit else LanguageResult.failure type (.word fellThrough)) := by
  exact extraction_of_typed_body_with_residual false (diagnosticPolicy := diagnosticPolicy) (tracked := tracked)
    (factory := factory) (readPolicy := readPolicy) (binderPolicy := binderPolicy)
    (allocationPolicy := allocationPolicy) (expressions := expressions) (assignments := assignments)
    (unaryPolicy := unaryPolicy) (unique := unique) (assignmentExpressions := assignmentExpressions)
    (context := context) (scope := scope) (statements := statements) (expected := expected) (syntaxTree := syntaxTree)
    (closed := closed) (residual := residual) (sourceSignatures := sourceSignatures) (declarations := declarations)
    (fuel := fuel) (type := type) (nativeType := nativeType) (code := code) (fellThrough := fellThrough)
    (escaped := escaped) (projection := projection) (accepted := accepted) (nativeTyped := nativeTyped)

theorem tree_of_typed_body_with_residual (residualMode : Bool)
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
    {context : SourceSemantics.Context} {scope : Scope} {statements : List StatementId} {expected : TypeSystem.Ty}
    (syntaxTree : Syntax source expressionSyntax context (.statements true statements) expected)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = residualMode)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {fuel : Nat} {type nativeType : Ty} {code : Expr} {fellThrough escaped : Word}
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope statements type reasonAt fellThrough escaped = .ok code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType definitions) :
    ∃ flow,
      SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope statements type reasonAt true escaped = .ok flow ∧
      Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements true statements) expected type flow ∧
      code = LocalControl.finish type (LocalLoop.toControl type flow escaped)
        (if type = .unit then LanguageResult.success .unit else LanguageResult.failure type (.word fellThrough)) := by
  obtain ⟨flow, generated, extracted, same⟩ := extraction_of_typed_body_with_residual residualMode .unconditional
    (AssignmentDiagnosticOrigins.Factory.unchanged .unconditional source invalidOperand) readPolicy binderPolicy allocationPolicy expressions assignments unaryPolicy unique assignmentExpressions syntaxTree closed residual sourceSignatures declarations projection accepted nativeTyped
  exact ⟨flow, generated, extracted.tree, same⟩

/-- Compatibility entry for the former closed residual scope. -/
theorem tree_of_typed_body
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
    {context : SourceSemantics.Context} {scope : Scope} {statements : List StatementId} {expected : TypeSystem.Ty}
    (syntaxTree : Syntax source expressionSyntax context (.statements true statements) expected)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {fuel : Nat} {type nativeType : Ty} {code : Expr} {fellThrough escaped : Word}
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope statements type reasonAt fellThrough escaped = .ok code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType definitions) :
    ∃ flow,
      SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope statements type reasonAt true escaped = .ok flow ∧
      Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements true statements) expected type flow ∧
      code = LocalControl.finish type (LocalLoop.toControl type flow escaped)
        (if type = .unit then LanguageResult.success .unit else LanguageResult.failure type (.word fellThrough)) := by
  exact tree_of_typed_body_with_residual false (readPolicy := readPolicy) (binderPolicy := binderPolicy)
    (allocationPolicy := allocationPolicy) (expressions := expressions) (assignments := assignments)
    (unaryPolicy := unaryPolicy) (unique := unique) (assignmentExpressions := assignmentExpressions)
    (context := context) (scope := scope) (statements := statements) (expected := expected) (syntaxTree := syntaxTree)
    (closed := closed) (residual := residual) (sourceSignatures := sourceSignatures) (declarations := declarations)
    (fuel := fuel) (type := type) (nativeType := nativeType) (code := code) (fellThrough := fellThrough)
    (escaped := escaped) (projection := projection) (accepted := accepted) (nativeTyped := nativeTyped)

/-- Real prepared diagnostics supply reachable operand laws at authenticated
statement and parent-header positions. Other diagnostic interpretation is residual. -/
theorem extraction_of_prepared_flow_with_residual (residualMode : Bool) {first : Nat} {table : SourceCoreAssignmentFaultSites.Table}
    (prepared : SourceCoreAssignmentFaultSites.prepare source first = .ok table)
    (operandsTyped : AssignmentDiagnosticOrigins.OperandsTyped source)
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
    (assignments : CompatibleAssignmentStatements.AssignmentPolicy policy values invalidProjection (GenericAssignmentDiagnostics.token table) missingDefault)
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
    {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {statements : List StatementId} {expected : TypeSystem.Ty}
    (syntaxTree : Syntax source expressionSyntax context (.statements mode statements) expected)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = residualMode)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {fuel : Nat} {type : Ty} {code : Expr} {selfReason : Word} {nativeType : Ty}
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope statements type reasonAt mode selfReason = .ok code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType definitions) :
    Nonempty (DiagnosticExtraction .reachable layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
      context scope (.statements mode statements) expected type code) := by
  exact extraction_of_typed_flow_with_residual residualMode .reachable (AssignmentDiagnosticOrigins.Factory.prepared operandsTyped prepared) readPolicy binderPolicy allocationPolicy expressions assignments unaryPolicy unique assignmentExpressions syntaxTree closed residual sourceSignatures declarations projection accepted nativeTyped

/-- Compatibility entry for the former closed residual scope. -/
theorem extraction_of_prepared_flow {first : Nat} {table : SourceCoreAssignmentFaultSites.Table}
    (prepared : SourceCoreAssignmentFaultSites.prepare source first = .ok table)
    (operandsTyped : AssignmentDiagnosticOrigins.OperandsTyped source)
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
    (assignments : CompatibleAssignmentStatements.AssignmentPolicy policy values invalidProjection (GenericAssignmentDiagnostics.token table) missingDefault)
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
    {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {statements : List StatementId} {expected : TypeSystem.Ty}
    (syntaxTree : Syntax source expressionSyntax context (.statements mode statements) expected)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {fuel : Nat} {type : Ty} {code : Expr} {selfReason : Word} {nativeType : Ty}
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope statements type reasonAt mode selfReason = .ok code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType definitions) :
    Nonempty (DiagnosticExtraction .reachable layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
      context scope (.statements mode statements) expected type code) := by
  exact extraction_of_prepared_flow_with_residual false (first := first) (table := table) (prepared := prepared)
    (operandsTyped := operandsTyped) (readPolicy := readPolicy) (binderPolicy := binderPolicy)
    (allocationPolicy := allocationPolicy) (expressions := expressions) (assignments := assignments)
    (unaryPolicy := unaryPolicy) (unique := unique) (assignmentExpressions := assignmentExpressions)
    (context := context) (scope := scope) (mode := mode) (statements := statements) (expected := expected)
    (syntaxTree := syntaxTree) (closed := closed) (residual := residual) (sourceSignatures := sourceSignatures)
    (declarations := declarations) (fuel := fuel) (type := type) (code := code) (selfReason := selfReason)
    (nativeType := nativeType) (projection := projection) (accepted := accepted) (nativeTyped := nativeTyped)

/-- Real prepared diagnostics supply reachable operand laws at authenticated
statement and parent-header positions. Other diagnostic interpretation is residual. -/
theorem extraction_of_prepared_body_with_residual (residualMode : Bool) {first : Nat} {table : SourceCoreAssignmentFaultSites.Table}
    (prepared : SourceCoreAssignmentFaultSites.prepare source first = .ok table)
    (operandsTyped : AssignmentDiagnosticOrigins.OperandsTyped source)
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
    (assignments : CompatibleAssignmentStatements.AssignmentPolicy policy values invalidProjection (GenericAssignmentDiagnostics.token table) missingDefault)
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
    {context : SourceSemantics.Context} {scope : Scope} {statements : List StatementId} {expected : TypeSystem.Ty}
    (syntaxTree : Syntax source expressionSyntax context (.statements true statements) expected)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = residualMode)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {fuel : Nat} {type nativeType : Ty} {code : Expr} {fellThrough escaped : Word}
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope statements type reasonAt fellThrough escaped = .ok code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType definitions) :
    ∃ flow,
      SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope statements type reasonAt true escaped = .ok flow ∧
      ∃ _extracted : DiagnosticExtraction .reachable layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements true statements) expected type flow,
      code = LocalControl.finish type (LocalLoop.toControl type flow escaped)
        (if type = .unit then LanguageResult.success .unit else LanguageResult.failure type (.word fellThrough)) := by
  exact extraction_of_typed_body_with_residual residualMode .reachable (AssignmentDiagnosticOrigins.Factory.prepared operandsTyped prepared) readPolicy binderPolicy allocationPolicy expressions assignments unaryPolicy unique assignmentExpressions syntaxTree closed residual sourceSignatures declarations projection accepted nativeTyped

/-- Compatibility entry for the former closed residual scope. -/
theorem extraction_of_prepared_body {first : Nat} {table : SourceCoreAssignmentFaultSites.Table}
    (prepared : SourceCoreAssignmentFaultSites.prepare source first = .ok table)
    (operandsTyped : AssignmentDiagnosticOrigins.OperandsTyped source)
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
    (assignments : CompatibleAssignmentStatements.AssignmentPolicy policy values invalidProjection (GenericAssignmentDiagnostics.token table) missingDefault)
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
    {context : SourceSemantics.Context} {scope : Scope} {statements : List StatementId} {expected : TypeSystem.Ty}
    (syntaxTree : Syntax source expressionSyntax context (.statements true statements) expected)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {fuel : Nat} {type nativeType : Ty} {code : Expr} {fellThrough escaped : Word}
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope statements type reasonAt fellThrough escaped = .ok code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType definitions) :
    ∃ flow,
      SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope statements type reasonAt true escaped = .ok flow ∧
      ∃ _extracted : DiagnosticExtraction .reachable layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements true statements) expected type flow,
      code = LocalControl.finish type (LocalLoop.toControl type flow escaped)
        (if type = .unit then LanguageResult.success .unit else LanguageResult.failure type (.word fellThrough)) := by
  exact extraction_of_prepared_body_with_residual false (first := first) (table := table) (prepared := prepared)
    (operandsTyped := operandsTyped) (readPolicy := readPolicy) (binderPolicy := binderPolicy)
    (allocationPolicy := allocationPolicy) (expressions := expressions) (assignments := assignments)
    (unaryPolicy := unaryPolicy) (unique := unique) (assignmentExpressions := assignmentExpressions)
    (context := context) (scope := scope) (statements := statements) (expected := expected) (syntaxTree := syntaxTree)
    (closed := closed) (residual := residual) (sourceSignatures := sourceSignatures) (declarations := declarations)
    (fuel := fuel) (type := type) (nativeType := nativeType) (code := code) (fellThrough := fellThrough)
    (escaped := escaped) (projection := projection) (accepted := accepted) (nativeTyped := nativeTyped)

/-- The actual fixed policy authenticates the read, allocator and diagnostic callbacks. -/
theorem extraction_of_prepared_policy_body_with_residual (residualMode : Bool) {first : Nat} {table : SourceCoreAssignmentFaultSites.Table}
    (prepared : SourceCoreAssignmentFaultSites.prepare source first = .ok table)
    (operandsTyped : AssignmentDiagnosticOrigins.OperandsTyped source)
    {ledger : List SolvedRequirement} {policyOwner : SourceSpecialization.SpecializationKey}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program}
    (fixedPolicy : policy = SourceCoreCompatibleDataMatches.loopPolicy values ledger table diagnostics policyOwner policy.lowerExpression
      (some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals (layouts.allocatorAt owner active onError)))
      (some definitions))
    (expressions : ∀ sourceContext, sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = residualMode →
      sourceContext.signatures = values.checked.signatures →
      ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations source scope sourceContext → expressionSyntax id →
      source.lookupExpression? id = some node → ExpressionHasType source sourceContext id node.type →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
      certificates sourceContext scope id lowered)
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
    {context : SourceSemantics.Context} {scope : Scope} {statements : List StatementId} {expected : TypeSystem.Ty}
    (syntaxTree : Syntax source expressionSyntax context (.statements true statements) expected)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = residualMode)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {fuel : Nat} {type nativeType : Ty} {code : Expr} {fellThrough escaped : Word}
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope statements type reasonAt fellThrough escaped = .ok code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType definitions) :
    ∃ flow,
      SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope statements type reasonAt true escaped = .ok flow ∧
      ∃ _extracted : DiagnosticExtraction .reachable layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements true statements) expected type flow,
      code = LocalControl.finish type (LocalLoop.toControl type flow escaped)
        (if type = .unit then LanguageResult.success .unit else LanguageResult.failure type (.word fellThrough)) := by
  have assignmentPolicy := fixedPolicy.symm ▸
    CompatibleAssignmentStatements.AssignmentPolicy.actual values ledger table diagnostics policyOwner policy.lowerExpression
      (some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals (layouts.allocatorAt owner active onError))) (some definitions)
  exact extraction_of_prepared_body_with_residual residualMode prepared operandsTyped
    (by rw [fixedPolicy]; rfl)
    (by intro scope binder _; rw [fixedPolicy]; rfl)
    (by rw [fixedPolicy]; rfl)
    expressions assignmentPolicy
    (show CompatibleBitNotStatements.Policy policy values
      (fun site root => diagnostics.placeReason policyOwner site root none)
      (fun site root => table.reasonAt site root .bitNot)
      (fun site root type => diagnostics.placeReason policyOwner site root (some type)) from by rw [fixedPolicy]; rfl)
    unique assignmentExpressions syntaxTree closed residual sourceSignatures declarations projection accepted nativeTyped

/-- Compatibility entry for the former closed residual scope. -/
theorem extraction_of_prepared_policy_body {first : Nat} {table : SourceCoreAssignmentFaultSites.Table}
    (prepared : SourceCoreAssignmentFaultSites.prepare source first = .ok table)
    (operandsTyped : AssignmentDiagnosticOrigins.OperandsTyped source)
    {ledger : List SolvedRequirement} {policyOwner : SourceSpecialization.SpecializationKey}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program}
    (fixedPolicy : policy = SourceCoreCompatibleDataMatches.loopPolicy values ledger table diagnostics policyOwner policy.lowerExpression
      (some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals (layouts.allocatorAt owner active onError)))
      (some definitions))
    (expressions : ∀ sourceContext, sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = false →
      sourceContext.signatures = values.checked.signatures →
      ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations source scope sourceContext → expressionSyntax id →
      source.lookupExpression? id = some node → ExpressionHasType source sourceContext id node.type →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
      certificates sourceContext scope id lowered)
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
    {context : SourceSemantics.Context} {scope : Scope} {statements : List StatementId} {expected : TypeSystem.Ty}
    (syntaxTree : Syntax source expressionSyntax context (.statements true statements) expected)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {fuel : Nat} {type nativeType : Ty} {code : Expr} {fellThrough escaped : Word}
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope statements type reasonAt fellThrough escaped = .ok code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType definitions) :
    ∃ flow,
      SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope statements type reasonAt true escaped = .ok flow ∧
      ∃ _extracted : DiagnosticExtraction .reachable layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements true statements) expected type flow,
      code = LocalControl.finish type (LocalLoop.toControl type flow escaped)
        (if type = .unit then LanguageResult.success .unit else LanguageResult.failure type (.word fellThrough)) := by
  exact extraction_of_prepared_policy_body_with_residual false (first := first) (table := table) (prepared := prepared)
    (operandsTyped := operandsTyped) (ledger := ledger) (policyOwner := policyOwner) (diagnostics := diagnostics)
    (fixedPolicy := fixedPolicy) (expressions := expressions) (unique := unique)
    (assignmentExpressions := assignmentExpressions) (context := context) (scope := scope) (statements := statements)
    (expected := expected) (syntaxTree := syntaxTree) (closed := closed) (residual := residual)
    (sourceSignatures := sourceSignatures) (declarations := declarations) (fuel := fuel) (type := type)
    (nativeType := nativeType) (code := code) (fellThrough := fellThrough) (escaped := escaped)
    (projection := projection) (accepted := accepted) (nativeTyped := nativeTyped)

end Solcore.SourceSemantics.CoreLowering.GenericImperativeFor
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GenericImperativeForMeaning
/-! Finite preservation and completed reflection for mixed assignments, while
loops, lexical bindings and scoped control. Concrete expression and statement
trees discharge every child meaning. Native typing is a separate static receipt;
scoped exits restore the source context while retaining effects and live cells. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericImperativeFor
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedAllocationCompletion CoreProof
open TypedScopedStatements (Executes)
open GenericImperative (assignment_preserves assignment_reflects assignment_preserves_reachable assignment_reflects_reachable)
open GenericImperativeWhile (conditional_preserves conditional_reflects while_preserves while_reflects)
open TypedLexicalWhile hiding Syntax Tree Scope ValuesContext absentRequest initializedRequest sequence conditional_preserves conditional_reflects while_preserves while_reflects
open TypedLexicalControl (LexicalResult source_view_absent source_view_initialized allocate_absent allocate_initialized sequence_rename valid_extend)

private theorem breaking_view {program : Program} {context finalContext : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : StatementId} {node : StatementNode} {rest : List StatementId} {mode : Bool}
    {outcome : Dynamic.ControlOutcome}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node) (form : node.form = .breakStmt)
    (trace : Executes mode program context evidence source environment before (id :: rest) finalContext outcome after) :
    finalContext = context ∧ outcome = .breaking environment ∧ after = before := by
  have contains := lookupStatement?_sound found
  have notTail : mode = true → rest = [] → ∀ expression, node.form ≠ .expression expression false := by
    intro _ _ expression; simp [form]
  cases TypedScopedStatements.source_view trace with
  | control executed =>
    rcases ScalarStatementViews.cons_view mode unique contains notTail executed with ⟨_, _, _, head, _⟩ | ⟨head, _⟩
    · obtain ⟨_, impossible, _⟩ := ScalarStatementViews.breaking unique contains form head; cases impossible
    · exact ScalarStatementViews.breaking unique contains form head
  | fault failed =>
    rcases ScalarStatementViews.cons_fault_view mode unique contains notTail failed with ⟨_, head⟩ | ⟨_, _, _, head, _⟩
    · exact False.elim (ScalarStatementViews.breaking_cannot_fault unique contains form head)
    · obtain ⟨_, impossible, _⟩ := ScalarStatementViews.breaking unique contains form head; cases impossible

private theorem continuing_view {program : Program} {context finalContext : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : StatementId} {node : StatementNode} {rest : List StatementId} {mode : Bool}
    {outcome : Dynamic.ControlOutcome}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node) (form : node.form = .continueStmt)
    (trace : Executes mode program context evidence source environment before (id :: rest) finalContext outcome after) :
    finalContext = context ∧ outcome = .continuing environment ∧ after = before := by
  have contains := lookupStatement?_sound found
  have notTail : mode = true → rest = [] → ∀ expression, node.form ≠ .expression expression false := by
    intro _ _ expression; simp [form]
  cases TypedScopedStatements.source_view trace with
  | control executed =>
    rcases ScalarStatementViews.cons_view mode unique contains notTail executed with ⟨_, _, _, head, _⟩ | ⟨head, _⟩
    · obtain ⟨_, impossible, _⟩ := ScalarStatementViews.continuing unique contains form head; cases impossible
    · exact ScalarStatementViews.continuing unique contains form head
  | fault failed =>
    rcases ScalarStatementViews.cons_fault_view mode unique contains notTail failed with ⟨_, head⟩ | ⟨_, _, _, head, _⟩
    · exact False.elim (ScalarStatementViews.continuing_cannot_fault unique contains form head)
    · obtain ⟨_, impossible, _⟩ := ScalarStatementViews.continuing unique contains form head; cases impossible

variable {administrative : Core.Context} {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource}
  {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {solved : List SolvedRequirement}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry}

variable (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  (meaning : ∀ context, CompatibleExpressionLiterals.ContextValid solved context evidence →
    TypedGenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (certificates context) faults)
  (reflection : ∀ context, CompatibleExpressionLiterals.ContextValid solved context evidence →
    TypedGenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (certificates context) faults)

variable {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)

abbrev PreservesAtFor (diagnosticPolicy : AssignmentDiagnosticPolicy) (context : SourceSemantics.Context) (scope : Scope) (position : Position)
    (expected : TypeSystem.Ty) (type : Ty) (code : Expr) : Prop :=
  match position with
  | .statements mode statements => Preserves functions program evidence (registry := registry) (source := source)
      (context := context) (scope := scope) (faults := faults) (solved := solved) (frameLayout := frame)
      (globals := globals) (administrative := administrative) mode statements expected type code
  | .initializers items condition post statements => PreservingHeaderFor (diagnosticPolicy := diagnosticPolicy) (certificates := certificates) functions program evidence
      (layouts := layouts) (owner := owner) (active := active) (frameLayout := frame) (globals := globals)
      (onError := onError) (source := source) (solved := solved)
      (administrative := administrative) (registry := registry) (faults := faults)
      context scope items condition post statements expected type code

abbrev PreservesAt (context : SourceSemantics.Context) (scope : Scope) (position : Position)
    (expected : TypeSystem.Ty) (type : Ty) (code : Expr) : Prop :=
  match position with
  | .statements mode statements => Preserves functions program evidence (registry := registry) (source := source)
      (context := context) (scope := scope) (faults := faults) (solved := solved) (frameLayout := frame)
      (globals := globals) (administrative := administrative) mode statements expected type code
  | .initializers items condition post statements => PreservingHeader (certificates := certificates) functions program evidence
      (layouts := layouts) (owner := owner) (active := active) (frameLayout := frame) (globals := globals)
      (onError := onError) (source := source) (solved := solved)
      (administrative := administrative) (registry := registry) (faults := faults)
      context scope items condition post statements expected type code

abbrev ReflectsAtFor (diagnosticPolicy : AssignmentDiagnosticPolicy) (context : SourceSemantics.Context) (scope : Scope) (position : Position)
    (expected : TypeSystem.Ty) (type : Ty) (code : Expr) : Prop :=
  match position with
  | .statements mode statements => Reflects functions program evidence (registry := registry) (source := source)
      (context := context) (scope := scope) (faults := faults) (solved := solved) (frameLayout := frame)
      (globals := globals) (administrative := administrative) mode statements expected type code
  | .initializers items condition post statements => ReflectingHeaderFor (diagnosticPolicy := diagnosticPolicy) (certificates := certificates) functions program evidence
      (layouts := layouts) (owner := owner) (active := active) (frameLayout := frame) (globals := globals)
      (onError := onError) (source := source) (solved := solved)
      (administrative := administrative) (registry := registry) (faults := faults)
      context scope items condition post statements expected type code

abbrev ReflectsAt (context : SourceSemantics.Context) (scope : Scope) (position : Position)
    (expected : TypeSystem.Ty) (type : Ty) (code : Expr) : Prop :=
  match position with
  | .statements mode statements => Reflects functions program evidence (registry := registry) (source := source)
      (context := context) (scope := scope) (faults := faults) (solved := solved) (frameLayout := frame)
      (globals := globals) (administrative := administrative) mode statements expected type code
  | .initializers items condition post statements => ReflectingHeader (certificates := certificates) functions program evidence
      (layouts := layouts) (owner := owner) (active := active) (frameLayout := frame) (globals := globals)
      (onError := onError) (source := source) (solved := solved)
      (administrative := administrative) (registry := registry) (faults := faults)
      context scope items condition post statements expected type code

private theorem sequence_stopped_preserves (unique : NodeOccurrencesUnique source) {context : SourceSemantics.Context} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {scope : Scope} {mode : Bool} {id : StatementId} {node : StatementNode}
    {rest : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {head body : Expr}
    (found : source.lookupStatement? id = some node)
    (notTail : ∀ expression, node.form ≠ .expression expression false)
    (first : HeadPreserves functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative) (scope := scope) id expected type head)
    (stops : ReachableStatementContinuations.StatementTerminates source id) :
    Preserves functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative) (scope := scope) mode (id :: rest) expected type (LocalLoop.sequence type head body) := by
  intro valid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext
    environments heaps locals agrees actualTyped reference read unmapped trace
  cases TypedScopedStatements.source_view trace with
  | control executed =>
    rcases ScalarStatementViews.cons_view mode unique (lookupStatement?_sound found) (fun _ _ => notTail) executed with
      ⟨_, _, _, headTrace, tailTrace⟩ | ⟨headTrace, terminal⟩
    · cases stops headTrace
    · obtain ⟨rfl, _, value, finalStore, finalMap, finalWorld, headEval, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
        first valid environments heaps locals agrees actualTyped reference read unmapped (.control headTrace)
      cases represented with
      | fallthrough _ => cases terminal
      | returned payload => exact ⟨_, finalStore, finalMap, finalWorld,
          by rw [LoopRenaming.sequence]; exact LocalLoop.sequence_returned _ headEval,
          .returned payload, finalHeaps, maps, worlds, frame, metadata,
          _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
      | fault matched => exact ⟨_, finalStore, finalMap, finalWorld,
          by rw [LoopRenaming.sequence]; exact LocalLoop.sequence_failure _ headEval,
          .fault matched, finalHeaps, maps, worlds, frame, metadata,
          _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
      | breaking next => exact ⟨_, finalStore, finalMap, finalWorld,
          by rw [LoopRenaming.sequence]; exact LocalLoop.sequence_transfer _ headEval,
          .breaking next, finalHeaps, maps, worlds, frame, metadata,
          _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
      | continuing next => exact ⟨_, finalStore, finalMap, finalWorld,
          by rw [LoopRenaming.sequence]; exact LocalLoop.sequence_transfer _ headEval,
          .continuing next, finalHeaps, maps, worlds, frame, metadata,
          _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
  | fault failed =>
    rcases ScalarStatementViews.cons_fault_view mode unique (lookupStatement?_sound found) (fun _ _ => notTail) failed with
      ⟨rfl, headTrace⟩ | ⟨_, _, _, headTrace, tailTrace⟩
    · obtain ⟨_, _, value, finalStore, finalMap, finalWorld, headEval, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
        first valid environments heaps locals agrees actualTyped reference read unmapped (.fault headTrace)
      cases represented with
      | fault matched => exact ⟨_, finalStore, finalMap, finalWorld,
          by rw [LoopRenaming.sequence]; exact LocalLoop.sequence_failure _ headEval,
          .fault matched, finalHeaps, maps, worlds, frame, metadata,
          _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
    · cases stops headTrace

private theorem sequence_stopped_reflects (_unique : NodeOccurrencesUnique source) {context : SourceSemantics.Context} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {scope : Scope} {mode : Bool} {id : StatementId} {node : StatementNode}
    {rest : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {head body : Expr}
    (found : source.lookupStatement? id = some node)
    (notTail : ∀ expression, node.form ≠ .expression expression false)
    (first : HeadReflects functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative) (scope := scope) id expected type head)
    (stops : ReachableStatementContinuations.StatementTerminates source id) :
    Reflects functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative) (scope := scope) mode (id :: rest) expected type (LocalLoop.sequence type head body) := by
  intro valid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees actualTyped reference read unmapped evaluated
  obtain ⟨wholeSize, original⟩ := evaluation_has_size evaluated
  rw [LoopRenaming.sequence] at evaluated original
  obtain ⟨headSize, middleStore, headValue, headSmaller, headSized⟩ := original.bind_computation
  have headEval := headSized.sound
  obtain ⟨outcome, middle, middleMap, middleWorld, headTrace, restores, represented, middleHeaps, maps, worlds, frame, metadata⟩ :=
    first valid environments heaps locals agrees actualTyped reference read unmapped headEval
  cases represented with
  | fallthrough next =>
    cases headTrace with | control headTrace => cases stops headTrace
  | returned payload =>
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated (LocalLoop.sequence_returned _ headEval)
    exact ⟨context, _, middle, middleMap, middleWorld, terminal_outcome program evidence found notTail headTrace (.returned _),
      .returned payload, middleHeaps, maps, worlds, frame, metadata,
      _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
  | fault matched =>
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated (LocalLoop.sequence_failure _ headEval)
    exact ⟨context, _, middle, middleMap, middleWorld, terminal_outcome program evidence found notTail headTrace (.fault _),
      .fault matched, middleHeaps, maps, worlds, frame, metadata,
      _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
  | breaking next =>
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated (LocalLoop.sequence_transfer _ headEval)
    exact ⟨context, _, middle, middleMap, middleWorld, terminal_outcome program evidence found notTail headTrace (.breaking _),
      .breaking next, middleHeaps, maps, worlds, frame, metadata,
      _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
  | continuing next =>
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated (LocalLoop.sequence_transfer _ headEval)
    exact ⟨context, _, middle, middleMap, middleWorld, terminal_outcome program evidence found notTail headTrace (.continuing _),
      .continuing next, middleHeaps, maps, worlds, frame, metadata,
      _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩

include definitions registered extension meaning faithful observations in
theorem Tree.preservesAt_for [FunctionCalls.FaultTokens faults] (diagnosticPolicy : AssignmentDiagnosticPolicy) (unique : NodeOccurrencesUnique source)
    {context : SourceSemantics.Context} {scope : Scope} {position : Position}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source expressionSyntax certificates ambient.definitions administrative
      context scope position expected type code)
    (errors : Tree.ErrorsFor diagnosticPolicy registry faults tree) :
    PreservesAtFor (diagnosticPolicy := diagnosticPolicy) (certificates := certificates) functions program evidence (layouts := layouts) (owner := owner) (active := active)
      (frame := frame) (globals := globals) (onError := onError)
      (source := source) (solved := solved) (administrative := administrative)
      (registry := registry) (faults := faults) context scope position expected type code := by
  induction errors with
  | @body context scope mode statements expected type code syntaxTree body =>
    intro contextValid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext
      environments heaps locals agrees actualTyped reference read unmapped trace
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, related, finalHeaps, maps, worlds, preservation, metadata, lexical⟩ :=
      body.preserves functions definitions registered program evidence meaning contextValid unique environments heaps locals agrees actualTyped reference read unmapped trace
    exact ⟨value, finalStore, finalMap, finalWorld, evaluated, FlowRep.of_lexical related, finalHeaps, maps, worlds, preservation, metadata, lexical⟩
  | @uninitialized context nextContext scope mode id node binder rest expected type body payload found form mono extended ordinary projected allocation annotation same tail tailErrors ih =>
    intro contextValid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext
      environments heaps locals agrees actualTyped reference read unmapped trace
    obtain ⟨location, middle, allocated, tailTrace⟩ := source_view_absent unique found form mono extended trace
    obtain ⟨captured, allocationEval, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped, nextReference, nextRead, preservation⟩ :=
      allocate_absent functions definitions registered mono extended ordinary projected allocation annotation same
        environments heaps locals agrees actualTyped reference read allocated
    obtain ⟨value, finalStore, finalMap, finalWorld, completed, represented, finalHeaps, maps, worlds, finalFrame, metadata, lexical⟩ :=
      ih (valid_extend contextValid extended) nextEnvironments nextHeaps nextLocals nextAgrees nextTyped nextReference nextRead
        (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1 tailTrace
    exact ⟨value, finalStore, finalMap, finalWorld, .letE allocationEval completed, represented, finalHeaps,
      (show LocationMap.Extends mapping (mapping ++ [store.length + 2]) from ⟨_, rfl⟩).trans maps,
      (show WorldExtends world (world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload]) from ⟨_, rfl⟩).trans worlds,
      preservation.trans finalFrame, (Dynamic.HeapMetadataExtend.of_allocation allocated).trans metadata, lexical.bind extended⟩
  | @initialized context nextContext scope mode id node binder initializer initializerNode lowered body rest expected type found form mono extended ordinary initialFound sourceType initial allocation annotation same remaining remainingErrors ih =>
    intro contextValid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext
      environments heaps locals agrees actualTyped reference read unmapped trace
    rw [sequence_rename]
    rcases source_view_initialized unique found form mono extended trace with ⟨reason, rfl, rfl, failed⟩ |
        ⟨sourceValue, location, middle, allocatedHeap, initialTrace, allocated, tailTrace⟩
    · obtain ⟨value, finalStore, finalMap, finalWorld, initialEval, represented, finalHeaps, maps, worlds, preservation, metadata⟩ :=
        meaning _ contextValid initial initialFound
          environments heaps locals agrees actualTyped (.fault failed)
      cases represented with
      | fault matched => exact ⟨_, finalStore, finalMap, finalWorld, LanguageResult.bind_failure _ initialEval,
          .fault matched, finalHeaps, maps, worlds, preservation, metadata, _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
    · obtain ⟨value, middleStore, middleMap, middleWorld, initialEval, represented, middleHeaps, maps, worlds, preservation, metadata⟩ :=
        meaning _ contextValid initial initialFound
          environments heaps locals agrees actualTyped (.value initialTrace)
      cases represented with
      | value payload =>
        have frameRead := (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read
        obtain ⟨captured, allocationEval, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped, nextReference, nextRead, allocationFrame⟩ :=
          allocate_initialized functions definitions registered mono extended ordinary allocation annotation same (sourceType ▸ payload)
            (environments.extend maps worlds) middleHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds) reference frameRead allocated
        obtain ⟨result, finalStore, finalMap, finalWorld, completed, related, finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, lexical⟩ :=
          ih (valid_extend contextValid extended)
            nextEnvironments nextHeaps nextLocals nextAgrees nextTyped nextReference nextRead
              (allocationFrame contextLocation (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
                (List.getElem?_eq_some_iff.mp frameRead).1).1 tailTrace
        exact ⟨result, finalStore, finalMap, finalWorld,
          LanguageResult.bind_success _ initialEval (.letE allocationEval completed), related, finalHeaps,
          maps.trans ((show LocationMap.Extends middleMap (middleMap ++ [middleStore.length + 2]) from ⟨_, rfl⟩).trans finalMaps),
          worlds.trans ((show WorldExtends middleWorld (middleWorld ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType lowered.type]) from ⟨_, rfl⟩).trans finalWorlds),
          preservation.trans (allocationFrame.trans finalFrame), metadata.trans ((Dynamic.HeapMetadataExtend.of_allocation allocated).trans finalMetadata), lexical.bind extended⟩
  | @discard context scope mode id node expression expressionNode semi rest expected lowered type body found form guard expressionFound child remaining remainingErrors ih =>
    intro contextValid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext
      environments heaps locals agrees actualTyped reference read unmapped trace
    rcases TypedScopedStatements.discard_view unique (lookupStatement?_sound found) form guard trace with ⟨reason, rfl, rfl, failed⟩ | ⟨sourceValue, middle, childTrace, tail⟩
    · obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
        meaning _ contextValid child expressionFound
          environments heaps locals agrees actualTyped (.fault failed)
      cases represented with
      | fault matched =>
        exact ⟨_, finalStore, finalMap, finalWorld, by rw [LoopRenaming.discard]; exact LocalSequence.discard_failure _ evaluated,
          .fault matched, finalHeaps, maps, worlds, frame, metadata,
          _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
    · obtain ⟨value, middleStore, middleMap, middleWorld, first, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata⟩ :=
        meaning _ contextValid child expressionFound
          environments heaps locals agrees actualTyped (.value childTrace)
      cases represented with
      | @value _ coreValue payload =>
        obtain ⟨value, finalStore, finalMap, finalWorld, second, represented, finalHeaps, maps, worlds, frame, metadata, lexical⟩ :=
          ih contextValid (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
            (GenericExpressionMeaning.agree_prefix agrees coreValue)
            (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) reference
            ((firstFrame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
            (firstFrame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1 tail
        refine ⟨value, finalStore, finalMap, finalWorld, ?_, represented, finalHeaps,
          firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata, lexical⟩
        rw [LoopRenaming.discard]
        rw [GenericExpressionMeaning.rename_prefix] at second
        exact LocalSequence.discard_success _ first second

  | @block context scope mode id node statements rest expected type innerCode body found form inner remaining innerErrors remainingErrors innerIH remainingIH =>
    intro contextValid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext
      environments heaps locals agrees actualTyped reference read unmapped trace
    exact sequence_preserves (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame) (globals := globals) (unique := unique) found (by intro expression; simp [form])
      (block_preserves (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame) (globals := globals) (unique := unique) found form innerIH) remainingIH
      contextValid environments heaps locals agrees actualTyped reference read unmapped trace
  | @ifThen context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body found form conditionFound conditionType conditionTree thenTree elseTree remaining thenErrors elseErrors remainingErrors thenIH elseIH remainingIH =>
    intro contextValid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext
      environments heaps locals agrees actualTyped reference read unmapped trace
    exact sequence_preserves (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame) (globals := globals) (unique := unique) found (by intro expression; simp [form])
      (conditional_preserves (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame) (globals := globals) (meaning := meaning context) (unique := unique) found form conditionFound conditionType conditionTree thenIH elseIH) remainingIH
      contextValid environments heaps locals agrees actualTyped reference read unmapped trace

  | @terminalBlock context scope mode id node statements rest expected type innerCode body exactUnique found form inner stops issued innerErrors innerIH =>
    intro contextValid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext
      environments heaps locals agrees actualTyped reference read unmapped trace
    exact sequence_stopped_preserves unique (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame) (globals := globals) found (by intro expression; simp [form])
      (block_preserves (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame) (globals := globals) (unique := unique) found form innerIH) (GenericLexicalStatements.block_terminates exactUnique found form stops)
      contextValid environments heaps locals agrees actualTyped reference read unmapped trace
  | @terminalIf context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body exactUnique found form conditionFound conditionType conditionTree thenTree elseTree thenStops elseStops issued thenErrors elseErrors thenIH elseIH =>
    intro contextValid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext
      environments heaps locals agrees actualTyped reference read unmapped trace
    exact sequence_stopped_preserves unique (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame) (globals := globals) found (by intro expression; simp [form])
      (conditional_preserves (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame) (globals := globals) (meaning := meaning context) (unique := unique) found form conditionFound conditionType conditionTree thenIH elseIH) (GenericLexicalStatements.conditional_terminates exactUnique found form thenStops elseStops)
      contextValid environments heaps locals agrees actualTyped reference read unmapped trace

  | @breaking context scope mode id node rest expected type found form =>
    intro contextValid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext
      environments heaps locals agrees actualTyped reference read unmapped trace
    obtain ⟨rfl, rfl, rfl⟩ := breaking_view unique found form trace
    exact ⟨_, store, mapping, world, by simpa only [LoopRenaming.breaking] using LocalLoop.breaking_evaluates _ actual store,
      .breaking environment, heaps, .refl _, .refl _, .refl _ _, .refl _, _, _, _, .here, environments, locals⟩

  | @continuing context scope mode id node rest expected type found form =>
    intro contextValid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext
      environments heaps locals agrees actualTyped reference read unmapped trace
    obtain ⟨rfl, rfl, rfl⟩ := continuing_view unique found form trace
    exact ⟨_, store, mapping, world, by simpa only [LoopRenaming.continuing] using LocalLoop.continuing_evaluates _ actual store,
      .continuing environment, heaps, .refl _, .refl _, .refl _ _, .refl _, _, _, _, .here, environments, locals⟩

  | @whileLoop context scope mode id node condition conditionNode statements rest expected type conditionCode loopCode body selfReason found form conditionFound conditionType conditionTree loopTree nativeTyped remaining loopErrors remainingErrors loopIH restIH =>
    intro contextValid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext
      environments heaps locals agrees actualTyped reference read unmapped trace
    exact sequence_preserves (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame) (globals := globals) (unique := unique) found (by intro expression; simp [form])
      (while_preserves functions program evidence (meaning context contextValid) found form conditionFound conditionTree nativeTyped unique loopIH) restIH
      contextValid environments heaps locals agrees actualTyped reference read unmapped trace

  | @assign context scope mode id node assignment operator rhs rest expected type body found form head remaining remainingErrors headErrors ih =>
    intro contextValid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext
      environments heaps locals agrees actualTyped reference read unmapped trace
    exact assignment_preserves_reachable functions extension program evidence (meaning context) faithful observations
      found form head (GenericAssignmentStatements.Head.ErrorsFor.reachable headErrors) unique ih contextValid environments heaps locals agrees actualTyped reference read unmapped trace

  | @bitNot context scope mode id node assignment rest expected type body found form head remaining remainingErrors headErrors ih =>
    intro contextValid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext
      environments heaps locals agrees actualTyped reference read unmapped trace
    exact CompatibleBitNotStatements.assignment_preserves functions program evidence
      found form head headErrors unique ih contextValid environments heaps locals agrees actualTyped reference read unmapped trace

  | @forLoop context scope mode id node initializer condition post statements rest expected type initialCode body found form initial remaining initialErrors remainingErrors initialIH restIH =>
    intro contextValid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext
      environments heaps locals agrees actualTyped reference read unmapped trace
    exact sequence_preserves (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame) (globals := globals) (unique := unique) found (by intro expression; simp [form])
      (header_preserves_reachable functions definitions registered extension program evidence meaning faithful observations unique found form (by rcases initialIH with ⟨header, errors⟩; exact ⟨header, GenericForHeader.Tree.ErrorsFor.reachable errors⟩)) restIH
      contextValid environments heaps locals agrees actualTyped reference read unmapped trace
  | @initializersDone context scope condition conditionNode post statements expected type conditionCode bodyCode postCode selfReason conditionFound conditionType conditionTree loopTree postTree nativeTyped loopErrors postErrors loopIH =>
    have completed := loop_preserves_reachable functions extension program evidence unique meaning definitions registered faithful observations
      conditionFound conditionTree nativeTyped postTree (GenericForHeader.Tree.ErrorsFor.reachable postErrors) loopIH
    exact ⟨.nil completed, GenericForHeader.Tree.ErrorsFor.nil (policy := diagnosticPolicy) (next := completed)⟩
  | @initializerUninitialized context nextContext scope binder rest body payload condition post statements expected type mono extended ordinary projected allocation annotation same remaining remainingErrors ih =>
    obtain ⟨header, errors⟩ := ih
    exact ⟨.uninitialized mono extended ordinary projected allocation annotation same header, .uninitialized (monomorphic := mono) (extended := extended) (ordinary := ordinary) (projected := projected) (allocation := allocation) (annotation := annotation) (same := same) errors⟩
  | @initializerInitialized context nextContext scope binder initializer initializerNode lowered body rest condition post statements expected type mono extended ordinary found sourceType child allocation annotation same remaining remainingErrors ih =>
    obtain ⟨header, errors⟩ := ih
    exact ⟨.initialized mono extended ordinary found sourceType child allocation annotation same header, .initialized (monomorphic := mono) (extended := extended) (ordinary := ordinary) (initializerFound := found) (sourceType := sourceType) (initial := child) (allocation := allocation) (annotation := annotation) (same := same) errors⟩
  | @initializerDiscard context scope expression expressionNode rest lowered body condition post statements expected type found child remaining remainingErrors ih =>
    obtain ⟨header, errors⟩ := ih
    exact ⟨.discard found child header, .discard (found := found) (value := child) errors⟩
  | @initializerAssign context scope assignment operator rhs rest body condition post statements expected type head remaining remainingErrors headErrors ih =>
    obtain ⟨header, errors⟩ := ih
    exact ⟨.assign head header, .assign (head := head) errors headErrors⟩

  | @initializerBitNot context scope assignment rest body condition post statements expected type head remaining remainingErrors headErrors ih =>
    obtain ⟨header, errors⟩ := ih
    exact ⟨.bitNot head header, .bitNot (head := head) errors headErrors⟩

include definitions registered extension meaning faithful observations in
/-- Original signature, specialized to the unconditional diagnostic policy. -/
theorem Tree.preservesAt [FunctionCalls.FaultTokens faults] (unique : NodeOccurrencesUnique source)
    {context : SourceSemantics.Context} {scope : Scope} {position : Position}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source expressionSyntax certificates ambient.definitions administrative
      context scope position expected type code)
    (errors : Tree.Errors registry faults tree) :
    PreservesAt (certificates := certificates) functions program evidence (layouts := layouts) (owner := owner) (active := active)
      (frame := frame) (globals := globals) (onError := onError)
      (source := source) (solved := solved) (administrative := administrative)
      (registry := registry) (faults := faults) context scope position expected type code := by
  apply Tree.preservesAt_for (functions := functions) (diagnosticPolicy := .unconditional)
  all_goals assumption

include definitions registered extension meaning reflection faithful observations in
theorem Tree.reflectsAt_for [FunctionCalls.FaultTokens faults] (diagnosticPolicy : AssignmentDiagnosticPolicy) (functionTypes : FunctionRuntimeViews functions) (unique : NodeOccurrencesUnique source)
    {context : SourceSemantics.Context} {scope : Scope} {position : Position}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source expressionSyntax certificates ambient.definitions administrative
      context scope position expected type code)
    (errors : Tree.ErrorsFor diagnosticPolicy registry faults tree) :
    ReflectsAtFor (diagnosticPolicy := diagnosticPolicy) (certificates := certificates) functions program evidence (layouts := layouts) (owner := owner) (active := active)
      (frame := frame) (globals := globals) (onError := onError)
      (source := source) (solved := solved) (administrative := administrative)
      (registry := registry) (faults := faults) context scope position expected type code := by
  induction errors with
  | @body context scope mode statements expected type code syntaxTree body =>
    intro contextValid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
      environments heaps locals agrees actualTyped reference read unmapped evaluated
    obtain ⟨finalContext, outcome, after, finalMap, finalWorld, trace, related, finalHeaps, maps, worlds, preservation, metadata, lexical⟩ :=
      body.reflects functions definitions registered program evidence reflection contextValid environments heaps locals agrees actualTyped reference read unmapped evaluated
    exact ⟨finalContext, outcome, after, finalMap, finalWorld, trace, FlowRep.of_lexical related, finalHeaps, maps, worlds, preservation, metadata, lexical⟩
  | @uninitialized context nextContext scope mode id node binder rest expected type body payload found form mono extended ordinary projected allocation annotation same tail tailErrors ih =>
    intro contextValid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
      environments heaps locals agrees actualTyped reference read unmapped evaluated
    obtain ⟨captured, allocationEval, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped, nextReference, nextRead, preservation⟩ :=
      allocate_absent functions definitions registered mono extended ordinary projected allocation annotation same
        environments heaps locals agrees actualTyped reference read Dynamic.Heap.Allocates.append
    have continuation := (ContinuationAgreement.letE allocationEval).unwrap evaluated
    obtain ⟨resultContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, finalFrame, metadata, lexical⟩ :=
      ih (valid_extend contextValid extended) nextEnvironments nextHeaps nextLocals nextAgrees nextTyped nextReference nextRead
        (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1 continuation
    exact ⟨resultContext, outcome, after, finalMap, finalWorld,
      TypedScopedStatements.prepend (lookupStatement?_sound found) (by intro _ _ expression; simp [form]) (.letUninitialized (lookupStatement?_sound found) form mono extended .append) trace,
      represented, finalHeaps,
      (show LocationMap.Extends mapping (mapping ++ [store.length + 2]) from ⟨_, rfl⟩).trans maps,
      (show WorldExtends world (world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload]) from ⟨_, rfl⟩).trans worlds,
      preservation.trans finalFrame, (Dynamic.HeapMetadataExtend.of_allocation Dynamic.Heap.Allocates.append).trans metadata, lexical.bind extended⟩
  | @initialized context nextContext scope mode id node binder initializer initializerNode lowered body rest expected type found form mono extended ordinary initialFound sourceType initial allocation annotation same remaining remainingErrors ih =>
    intro contextValid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
      environments heaps locals agrees actualTyped reference read unmapped evaluated
    rw [sequence_rename] at evaluated
    have input : ∃ input middle, Evaluates actual store (lowered.expression.rename ξ) input middle := by
      cases evaluated with
      | caseLeft initial branch | caseRight initial branch => exact ⟨_, _, initial⟩
    obtain ⟨input, middleStore, initialEval⟩ := input
    obtain ⟨sourceOutcome, middle, middleMap, middleWorld, initialTrace, represented, middleHeaps, maps, worlds, preservation, metadata⟩ :=
      reflection _ contextValid initial initialFound
        environments heaps locals agrees actualTyped initialEval
    cases represented with
    | fault matched =>
      cases initialTrace with | fault failed =>
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated (LanguageResult.bind_failure _ initialEval)
        exact ⟨context, _, middle, middleMap, middleWorld, TypedScopedStatements.head_fault mode rest (.letInitializer (lookupStatement?_sound found) form mono failed),
          .fault matched, middleHeaps, maps, worlds, preservation, metadata, _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
    | value payload =>
      cases initialTrace with | value initialTrace =>
        have frameRead := (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read
        obtain ⟨captured, allocationEval, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped, nextReference, nextRead, allocationFrame⟩ :=
          allocate_initialized functions definitions registered mono extended ordinary allocation annotation same (sourceType ▸ payload)
            (environments.extend maps worlds) middleHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds) reference frameRead .append
        have tailEval := (ContinuationAgreement.letE allocationEval).unwrap ((ContinuationAgreement.bind initialEval).unwrap evaluated)
        obtain ⟨resultContext, outcome, after, finalMap, finalWorld, trace, related, finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, lexical⟩ :=
          ih (valid_extend contextValid extended)
            nextEnvironments nextHeaps nextLocals nextAgrees nextTyped nextReference nextRead
              (allocationFrame contextLocation (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
                (List.getElem?_eq_some_iff.mp frameRead).1).1 tailEval
        exact ⟨resultContext, outcome, after, finalMap, finalWorld,
          TypedScopedStatements.prepend (lookupStatement?_sound found) (by intro _ _ expression; simp [form]) (.letInitialized (lookupStatement?_sound found) form initialTrace mono extended .append) trace,
          related, finalHeaps,
          maps.trans ((show LocationMap.Extends middleMap (middleMap ++ [middleStore.length + 2]) from ⟨_, rfl⟩).trans finalMaps),
          worlds.trans ((show WorldExtends middleWorld (middleWorld ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType lowered.type]) from ⟨_, rfl⟩).trans finalWorlds),
          preservation.trans (allocationFrame.trans finalFrame), metadata.trans ((Dynamic.HeapMetadataExtend.of_allocation Dynamic.Heap.Allocates.append).trans finalMetadata), lexical.bind extended⟩
  | @discard context scope mode id node expression expressionNode semi rest expected lowered type body found form guard expressionFound child remaining remainingErrors ih =>
    intro contextValid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
      environments heaps locals agrees actualTyped reference read unmapped evaluated
    rw [LoopRenaming.discard] at evaluated
    have complete := evaluated
    cases evaluated with
    | caseLeft childEvaluation branch =>
      obtain ⟨childOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
        reflection _ contextValid child expressionFound
          environments heaps locals agrees actualTyped childEvaluation
      cases represented with
      | fault matched =>
        cases trace with
        | fault failed =>
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete (LocalSequence.discard_failure _ childEvaluation)
          exact ⟨context, _, after, finalMap, finalWorld, TypedScopedStatements.head_fault mode rest (.expression (lookupStatement?_sound found) form failed),
            .fault matched, finalHeaps, maps, worlds, frame, metadata,
            _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
    | caseRight childEvaluation branch =>
      obtain ⟨childOutcome, middle, middleMap, middleWorld, trace, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata⟩ :=
        reflection _ contextValid child expressionFound
          environments heaps locals agrees actualTyped childEvaluation
      cases represented with
      | @value _ coreValue payload =>
        cases trace with
        | value childTrace =>
          obtain ⟨resultContext, outcome, after, finalMap, finalWorld, tail, represented, finalHeaps, maps, worlds, frame, metadata, lexical⟩ :=
            ih contextValid (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (GenericExpressionMeaning.agree_prefix agrees _)
              (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) reference
              ((firstFrame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
              (firstFrame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
              (by simpa only [GenericExpressionMeaning.rename_prefix] using branch)
          exact ⟨resultContext, outcome, after, finalMap, finalWorld,
            TypedScopedStatements.prepend (lookupStatement?_sound found) (TypedScopedStatements.not_tail form guard) (.expression (lookupStatement?_sound found) form childTrace) tail,
            represented, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata, lexical⟩

  | @block context scope mode id node statements rest expected type innerCode body found form inner remaining innerErrors remainingErrors innerIH remainingIH =>
    intro contextValid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
      environments heaps locals agrees actualTyped reference read unmapped evaluated
    exact sequence_reflects (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame) (globals := globals) found (by intro expression; simp [form])
      (block_reflects (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame) (globals := globals) found form innerIH) remainingIH
      contextValid environments heaps locals agrees actualTyped reference read unmapped evaluated
  | @ifThen context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body found form conditionFound conditionType conditionTree thenTree elseTree remaining thenErrors elseErrors remainingErrors thenIH elseIH remainingIH =>
    intro contextValid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
      environments heaps locals agrees actualTyped reference read unmapped evaluated
    exact sequence_reflects (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame) (globals := globals) found (by intro expression; simp [form])
      (conditional_reflects (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame) (globals := globals) (reflection := reflection context) found form conditionFound conditionType conditionTree thenIH elseIH) remainingIH
      contextValid environments heaps locals agrees actualTyped reference read unmapped evaluated

  | @terminalBlock context scope mode id node statements rest expected type innerCode body exactUnique found form inner stops issued innerErrors innerIH =>
    intro contextValid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
      environments heaps locals agrees actualTyped reference read unmapped evaluated
    exact sequence_stopped_reflects unique (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame) (globals := globals) found (by intro expression; simp [form])
      (block_reflects (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame) (globals := globals) found form innerIH) (GenericLexicalStatements.block_terminates exactUnique found form stops)
      contextValid environments heaps locals agrees actualTyped reference read unmapped evaluated
  | @terminalIf context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body exactUnique found form conditionFound conditionType conditionTree thenTree elseTree thenStops elseStops issued thenErrors elseErrors thenIH elseIH =>
    intro contextValid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
      environments heaps locals agrees actualTyped reference read unmapped evaluated
    exact sequence_stopped_reflects unique (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame) (globals := globals) found (by intro expression; simp [form])
      (conditional_reflects (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame) (globals := globals) (reflection := reflection context) found form conditionFound conditionType conditionTree thenIH elseIH) (GenericLexicalStatements.conditional_terminates exactUnique found form thenStops elseStops)
      contextValid environments heaps locals agrees actualTyped reference read unmapped evaluated

  | @breaking context scope mode id node rest expected type found form =>
    intro contextValid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
      environments heaps locals agrees actualTyped reference read unmapped evaluated
    have nativeEval : Evaluates actual store ((LocalLoop.breaking type).rename ξ) (LocalLoop.breakingValue type) store := by
      simpa only [LoopRenaming.breaking] using LocalLoop.breaking_evaluates type actual store
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated nativeEval
    exact ⟨_, _, before, mapping, world,
      TypedScopedStatements.terminal_intro _ _ (lookupStatement?_sound found) (by intro expression; simp [form])
        (.breakStmt (lookupStatement?_sound found) form) (.breaking environment),
      .breaking environment, heaps, .refl _, .refl _, .refl _ _, .refl _, _, _, _, .here, environments, locals⟩

  | @continuing context scope mode id node rest expected type found form =>
    intro contextValid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
      environments heaps locals agrees actualTyped reference read unmapped evaluated
    have nativeEval : Evaluates actual store ((LocalLoop.continuing type).rename ξ) (LocalLoop.continuingValue type) store := by
      simpa only [LoopRenaming.continuing] using LocalLoop.continuing_evaluates type actual store
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated nativeEval
    exact ⟨_, _, before, mapping, world,
      TypedScopedStatements.terminal_intro _ _ (lookupStatement?_sound found) (by intro expression; simp [form])
        (.continueStmt (lookupStatement?_sound found) form) (.continuing environment),
      .continuing environment, heaps, .refl _, .refl _, .refl _ _, .refl _, _, _, _, .here, environments, locals⟩

  | @whileLoop context scope mode id node condition conditionNode statements rest expected type conditionCode loopCode body selfReason found form conditionFound conditionType conditionTree loopTree nativeTyped remaining loopErrors remainingErrors loopIH restIH =>
    intro contextValid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
      environments heaps locals agrees actualTyped reference read unmapped evaluated
    exact sequence_reflects (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame) (globals := globals) found (by intro expression; simp [form])
      (while_reflects functions program evidence (reflection context contextValid) found form conditionFound conditionTree nativeTyped loopIH
        (fun executed => loopTree.control_not_fault unique executed)) restIH
      contextValid environments heaps locals agrees actualTyped reference read unmapped evaluated

  | @assign context scope mode id node assignment operator rhs rest expected type body found form head remaining remainingErrors headErrors ih =>
    intro contextValid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
      environments heaps locals agrees actualTyped reference read unmapped evaluated
    exact assignment_reflects_reachable functions extension program evidence (meaning context) (reflection context) faithful observations functionTypes
      found form head (GenericAssignmentStatements.Head.ErrorsFor.reachable headErrors) unique ih contextValid environments heaps locals agrees actualTyped reference read unmapped evaluated

  | @bitNot context scope mode id node assignment rest expected type body found form head remaining remainingErrors headErrors ih =>
    intro contextValid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
      environments heaps locals agrees actualTyped reference read unmapped evaluated
    exact CompatibleBitNotStatements.assignment_reflects functions program evidence
      found form head headErrors unique ih contextValid environments heaps locals agrees actualTyped reference read unmapped evaluated

  | @forLoop context scope mode id node initializer condition post statements rest expected type initialCode body found form initial remaining initialErrors remainingErrors initialIH restIH =>
    intro contextValid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
      environments heaps locals agrees actualTyped reference read unmapped evaluated
    exact sequence_reflects (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame) (globals := globals) found (by intro expression; simp [form])
      (header_reflects_reachable functions definitions registered extension program evidence meaning reflection faithful observations functionTypes unique found form (by rcases initialIH with ⟨header, errors⟩; exact ⟨header, GenericForHeader.Tree.ErrorsFor.reachable errors⟩)) restIH
      contextValid environments heaps locals agrees actualTyped reference read unmapped evaluated
  | @initializersDone context scope condition conditionNode post statements expected type conditionCode bodyCode postCode selfReason conditionFound conditionType conditionTree loopTree postTree nativeTyped loopErrors postErrors loopIH =>
    have completed := loop_reflects_reachable functions extension program evidence unique meaning reflection definitions registered faithful observations functionTypes
      conditionFound conditionTree nativeTyped postTree (GenericForHeader.Tree.ErrorsFor.reachable postErrors) loopIH (fun executed => loopTree.control_not_fault unique executed)
    exact ⟨.nil completed, GenericForHeader.Tree.ErrorsFor.nil (policy := diagnosticPolicy) (next := completed)⟩
  | @initializerUninitialized context nextContext scope binder rest body payload condition post statements expected type mono extended ordinary projected allocation annotation same remaining remainingErrors ih =>
    obtain ⟨header, errors⟩ := ih
    exact ⟨.uninitialized mono extended ordinary projected allocation annotation same header, .uninitialized (monomorphic := mono) (extended := extended) (ordinary := ordinary) (projected := projected) (allocation := allocation) (annotation := annotation) (same := same) errors⟩
  | @initializerInitialized context nextContext scope binder initializer initializerNode lowered body rest condition post statements expected type mono extended ordinary found sourceType child allocation annotation same remaining remainingErrors ih =>
    obtain ⟨header, errors⟩ := ih
    exact ⟨.initialized mono extended ordinary found sourceType child allocation annotation same header, .initialized (monomorphic := mono) (extended := extended) (ordinary := ordinary) (initializerFound := found) (sourceType := sourceType) (initial := child) (allocation := allocation) (annotation := annotation) (same := same) errors⟩
  | @initializerDiscard context scope expression expressionNode rest lowered body condition post statements expected type found child remaining remainingErrors ih =>
    obtain ⟨header, errors⟩ := ih
    exact ⟨.discard found child header, .discard (found := found) (value := child) errors⟩
  | @initializerAssign context scope assignment operator rhs rest body condition post statements expected type head remaining remainingErrors headErrors ih =>
    obtain ⟨header, errors⟩ := ih
    exact ⟨.assign head header, .assign (head := head) errors headErrors⟩

  | @initializerBitNot context scope assignment rest body condition post statements expected type head remaining remainingErrors headErrors ih =>
    obtain ⟨header, errors⟩ := ih
    exact ⟨.bitNot head header, .bitNot (head := head) errors headErrors⟩

include definitions registered extension meaning reflection faithful observations in
/-- Original signature, specialized to the unconditional diagnostic policy. -/
theorem Tree.reflectsAt [FunctionCalls.FaultTokens faults] (functionTypes : FunctionRuntimeViews functions) (unique : NodeOccurrencesUnique source)
    {context : SourceSemantics.Context} {scope : Scope} {position : Position}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source expressionSyntax certificates ambient.definitions administrative
      context scope position expected type code)
    (errors : Tree.Errors registry faults tree) :
    ReflectsAt (certificates := certificates) functions program evidence (layouts := layouts) (owner := owner) (active := active)
      (frame := frame) (globals := globals) (onError := onError)
      (source := source) (solved := solved) (administrative := administrative)
      (registry := registry) (faults := faults) context scope position expected type code := by
  apply Tree.reflectsAt_for (functions := functions) (tree := tree) (diagnosticPolicy := .unconditional)
  all_goals assumption

include definitions registered extension meaning faithful observations in
theorem Tree.preserves_reachable [FunctionCalls.FaultTokens faults] {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source expressionSyntax certificates ambient.definitions administrative
      context scope (.statements mode statements) expected type code)
    (errors : Tree.ReachableErrors registry faults tree)
    (contextValid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (unique : NodeOccurrencesUnique source)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    {outcome : Dynamic.ControlOutcome} {resultContext : SourceSemantics.Context}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (trace : Executes mode program context evidence source environment before statements resultContext outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment resultContext after := by
  exact tree.preservesAt_for (diagnosticPolicy := .reachable) functions definitions registered extension program evidence meaning faithful observations unique errors
    contextValid environments heaps locals agrees actualTyped reference read unmapped trace

include definitions registered extension meaning faithful observations in
/-- Original signature, specialized to the unconditional diagnostic policy. -/
theorem Tree.preserves [FunctionCalls.FaultTokens faults] {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source expressionSyntax certificates ambient.definitions administrative
      context scope (.statements mode statements) expected type code)
    (errors : Tree.Errors registry faults tree)
    (contextValid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (unique : NodeOccurrencesUnique source)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    {outcome : Dynamic.ControlOutcome} {resultContext : SourceSemantics.Context}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (trace : Executes mode program context evidence source environment before statements resultContext outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment resultContext after := by
  apply Tree.preserves_reachable (functions := functions) (tree := tree) (errors := errors.reachable)
  all_goals assumption

include definitions registered extension meaning reflection faithful observations in
theorem Tree.reflects_reachable [FunctionCalls.FaultTokens faults] (functionTypes : FunctionRuntimeViews functions) {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source expressionSyntax certificates ambient.definitions administrative
      context scope (.statements mode statements) expected type code)
    (errors : Tree.ReachableErrors registry faults tree)
    (contextValid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (unique : NodeOccurrencesUnique source)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame} {value : Value}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ resultContext outcome after finalMap finalWorld,
      Executes mode program context evidence source environment before statements resultContext outcome after ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment resultContext after := by
  exact tree.reflectsAt_for (diagnosticPolicy := .reachable) functions definitions registered extension program evidence meaning reflection faithful observations functionTypes unique errors
    contextValid environments heaps locals agrees actualTyped reference read unmapped evaluated

include definitions registered extension meaning reflection faithful observations in
/-- Original signature, specialized to the unconditional diagnostic policy. -/
theorem Tree.reflects [FunctionCalls.FaultTokens faults] (functionTypes : FunctionRuntimeViews functions) {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source expressionSyntax certificates ambient.definitions administrative
      context scope (.statements mode statements) expected type code)
    (errors : Tree.Errors registry faults tree)
    (contextValid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (unique : NodeOccurrencesUnique source)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame} {value : Value}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ resultContext outcome after finalMap finalWorld,
      Executes mode program context evidence source environment before statements resultContext outcome after ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment resultContext after := by
  apply Tree.reflects_reachable (functions := functions) (tree := tree) (errors := errors.reachable)
  all_goals assumption

end Solcore.SourceSemantics.CoreLowering.GenericImperativeFor
end
