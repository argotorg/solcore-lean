import Solcore.SourceSemantics.CoreLowering.EmittedDiagnosticExtraction
import Solcore.SourceSemantics.CoreLowering.EmittedDiagnosticTokenPlan
import Solcore.SourceSemantics.CoreLowering.EmittedForHeaderTokenExtraction

/-! Finite constructor adapters retain the original complete extraction and
its plan while carrying authentic unary token sites to that same witness. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericImperativeMatch
open Core Frontend SourceInference
open EmittedDiagnosticPlan EmittedDiagnosticTokenPlan
open TypedLexicalWhile (absentRequest initializedRequest sequence)
variable {tracked : Bool} {diagnosticPolicy : AssignmentDiagnosticPolicy}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Syntax.ValueAssignOp → Word}
abbrev TokenExtractionFor (diagnosticPolicy : AssignmentDiagnosticPolicy) (layouts : SourceCoreAllocationLayouts.Prepared)
    (owner : SourceSpecialization.SpecializationKey) (active : TypeSystem.Substitution)
    (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (values : ValuesContext) (source : TypedSource)
    (factory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy source invalidOperand)
    (invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word) (expressionSyntax : ExpressionId → Prop)
    (certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate)
    (definitions : DataEnvironment) (administrative : Core.Context) (solved : List SolvedRequirement)
    (context : SourceSemantics.Context) (scope : Scope) (position : Position)
    (expected : TypeSystem.Ty) (type : Ty) (code : Expr) :=
  EmittedDiagnosticTokenPlan.Produced factory invalidUnary (ExtractionFor diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved context scope position expected type code) (fun receipt => receipt.diagnostics)
namespace TokenExtractionFor
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource} {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {definitions : DataEnvironment} {administrative : Core.Context} {solved : List SolvedRequirement} {diagnosticPolicy : AssignmentDiagnosticPolicy}

variable {tracked : Bool} {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Syntax.ValueAssignOp → Word}
  {invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {factory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy source invalidOperand}
def body
    {context scope mode statements expected type code}
    (syntaxTree : GenericLexicalStatements.Syntax source expressionSyntax context mode statements expected)
    (body : GenericLexicalStatements.Tree layouts owner active frame globals onError values source certificates context scope mode statements expected type code) :
    TokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary expressionSyntax certificates definitions administrative solved
        context scope (.statements mode statements) expected type code := by
  exact ⟨ProducedExtractionFor.body (factory := factory) syntaxTree body, .pure⟩

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
    (remaining : TokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary expressionSyntax certificates definitions administrative solved
        nextContext ((binder.id, payload) :: scope) (.statements mode rest) expected type body) :
    TokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary expressionSyntax certificates definitions administrative solved
        context scope (.statements mode (id :: rest)) expected type (.letE annotation.expression body) := by
  exact ⟨ProducedExtractionFor.uninitialized (factory := factory) found form monomorphic extended ordinary projected allocation annotation same remaining.toProduced, remaining.tokens⟩

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
    (remaining : TokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary expressionSyntax certificates definitions administrative solved nextContext ((binder.id, lowered.type) :: scope) (.statements mode rest) expected type body) :
    TokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary expressionSyntax certificates definitions administrative solved
        context scope (.statements mode (id :: rest)) expected type (sequence type lowered.expression annotation.expression body) := by
  exact ⟨ProducedExtractionFor.initialized (factory := factory) found form monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining.toProduced, remaining.tokens⟩

def discard
    {context scope mode id node expression expressionNode semicolon rest expected lowered type body}
    (found : source.lookupStatement? id = some node)
    (form : node.form = .expression expression semicolon)
    (notTail : (!semicolon && mode && rest.isEmpty) = false)
    (expressionFound : source.lookupExpression? expression = some expressionNode)
    (value : certificates context scope expression lowered)
    (remaining : TokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary expressionSyntax certificates definitions administrative solved context scope (.statements mode rest) expected type body) :
    TokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary expressionSyntax certificates definitions administrative solved context scope (.statements mode (id :: rest)) expected type
        (LocalSequence.discard (LocalLoop.controlType type) lowered.expression body) := by
  exact ⟨ProducedExtractionFor.discard (factory := factory) found form notTail expressionFound value remaining.toProduced, remaining.tokens⟩

def block
    {context scope mode id node statements rest expected type innerCode body}
    (found : source.lookupStatement? id = some node)
    (form : node.form = .block statements)
    (inner : TokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary expressionSyntax certificates definitions administrative solved context scope (.statements false statements) expected type innerCode)
    (remaining : TokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary expressionSyntax certificates definitions administrative solved context scope (.statements mode rest) expected type body) :
    TokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary expressionSyntax certificates definitions administrative solved context scope (.statements mode (id :: rest)) expected type
        (LocalLoop.sequence type innerCode body) := by
  exact ⟨ProducedExtractionFor.block (factory := factory) found form inner.toProduced remaining.toProduced, .pair inner.tokens remaining.tokens⟩

def ifThen
    {context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body}
    (found : source.lookupStatement? id = some node)
    (form : node.form = .ifThen condition thenBody elseBody)
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionType : conditionNode.type = .bool)
    (conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩)
    (thenTree : TokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary expressionSyntax certificates definitions administrative solved context scope (.statements false thenBody) expected type thenCode)
    (elseTree : TokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary expressionSyntax certificates definitions administrative solved context scope (.statements false (elseBody.getD [])) expected type elseCode)
    (remaining : TokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary expressionSyntax certificates definitions administrative solved context scope (.statements mode rest) expected type body) :
    TokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary expressionSyntax certificates definitions administrative solved context scope (.statements mode (id :: rest)) expected type
        (LocalLoop.sequence type (LocalLoop.conditional type conditionCode thenCode elseCode) body) := by
  exact ⟨ProducedExtractionFor.ifThen (factory := factory) found form conditionFound conditionType conditionTree thenTree.toProduced elseTree.toProduced remaining.toProduced, .pair thenTree.tokens (.pair elseTree.tokens remaining.tokens)⟩

def breaking
    {context scope mode id node rest expected type}
    (found : source.lookupStatement? id = some node)
    (form : node.form = .breakStmt) :
    TokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary expressionSyntax certificates definitions administrative solved
        context scope (.statements mode (id :: rest)) expected type (LocalLoop.breaking type) := by
  exact ⟨ProducedExtractionFor.breaking (factory := factory) found form, .pure⟩

def continuing
    {context scope mode id node rest expected type}
    (found : source.lookupStatement? id = some node)
    (form : node.form = .continueStmt) :
    TokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary expressionSyntax certificates definitions administrative solved
        context scope (.statements mode (id :: rest)) expected type (LocalLoop.continuing type) := by
  exact ⟨ProducedExtractionFor.continuing (factory := factory) found form, .pure⟩

def whileLoop
    {context scope mode id node condition conditionNode statements rest expected type conditionCode loopCode body selfReason}
    (found : source.lookupStatement? id = some node)
    (form : node.form = .whileLoop condition statements)
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionType : conditionNode.type = .bool)
    (conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩)
    (loopBody : TokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary expressionSyntax certificates definitions administrative solved
        context scope (.statements false statements) expected type loopCode)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        (LocalLoop.whileLoop type conditionCode loopCode selfReason) (LocalLoop.resultType type) definitions)
    (remaining : TokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary expressionSyntax certificates definitions administrative solved
        context scope (.statements mode rest) expected type body) :
    TokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary expressionSyntax certificates definitions administrative solved
        context scope (.statements mode (id :: rest)) expected type
        (LocalLoop.sequence type (LocalLoop.whileLoop type conditionCode loopCode selfReason) body) := by
  exact ⟨ProducedExtractionFor.whileLoop (factory := factory) found form conditionFound conditionType conditionTree loopBody.toProduced nativeTyped remaining.toProduced, .pair loopBody.tokens remaining.tokens⟩

def assign
    {context scope mode id node assignment operator rhs rest expected type body}
    (found : source.lookupStatement? id = some node)
    (form : node.form = .assignValue assignment operator rhs)
    (head : GenericAssignmentStatements.Head values source context (certificates context) scope administrative definitions assignment operator rhs)
    (site : SourceCoreElaboration.ErrorSite)
    (origin : AssignmentDiagnosticOrigins.OccursFor tracked source site assignment operator rhs)
    (same : head.invalid = invalidOperand site assignment.target.root operator)
    (sourceTyped : ∀ binder, SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder →
      SourceProjectionsHaveType source context binder.scheme.body assignment.target.projections assignment.target.type)
    (rightTyped : ExpressionHasType source context rhs assignment.target.type)
    (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
      SourceCoreRawMetadata.runtimeType assignment.target.type = .integer)
    (remaining : TokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary expressionSyntax certificates definitions administrative solved
        context scope (.statements mode rest) expected type body) :
    TokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary expressionSyntax certificates definitions administrative solved
        context scope (.statements mode (id :: rest)) expected type (head.emit body (LocalLoop.controlType type)) := by
  exact ⟨ProducedExtractionFor.assign (factory := factory) found form head site origin same sourceTyped rightTyped profile remaining.toProduced, .pair remaining.tokens (.assignment head site origin same sourceTyped rightTyped profile)⟩

def bitNot
    {context scope mode id node assignment rest expected type body}
    (found : source.lookupStatement? id = some node)
    (form : node.form = .assignBitNot assignment)
    (head : CompatibleBitNotStatements.Head context scope assignment)
    (writable : ∀ binder, SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder →
      WritableLocal context assignment.target.root binder.scheme.body)
    (bare : assignment.target.projections = [])
    (profile : SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
      SourceCoreRawMetadata.runtimeType assignment.target.type = .integer)
    (site : SourceCoreElaboration.ErrorSite)
    (origin : EmittedDiagnosticTokenPlan.UnaryOccursFor tracked source site assignment)
    (same : head.invalid = invalidUnary site assignment.target.root)
    (remaining : TokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary expressionSyntax certificates definitions administrative solved
        context scope (.statements mode rest) expected type body) :
    TokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary expressionSyntax certificates definitions administrative solved
        context scope (.statements mode (id :: rest)) expected type (head.emit body (LocalLoop.controlType type)) := by
  exact ⟨ProducedExtractionFor.bitNot (factory := factory) found form head writable bare profile remaining.toProduced, .pair remaining.tokens (.unary head writable bare profile site origin same)⟩

def forLoop
    {context scope mode id node initializer condition post statements rest expected type initialCode body}
    (found : source.lookupStatement? id = some node)
    (form : node.form = .forLoop initializer condition post statements)
    (initial : TokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary expressionSyntax certificates definitions administrative solved context scope (.initializers initializer condition post statements) expected type initialCode)
    (remaining : TokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary expressionSyntax certificates definitions administrative solved context scope (.statements mode rest) expected type body) :
    TokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary expressionSyntax certificates definitions administrative solved context scope (.statements mode (id :: rest)) expected type (LocalLoop.sequence type initialCode body) := by
  exact ⟨ProducedExtractionFor.forLoop (factory := factory) found form initial.toProduced remaining.toProduced, .pair initial.tokens remaining.tokens⟩

def initializersDone
    {context scope condition conditionNode post statements expected type conditionCode bodyCode postCode selfReason}
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionType : conditionNode.type = .bool)
    (conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩)
    (loopBody : TokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary expressionSyntax certificates definitions administrative solved context scope (.statements false statements) expected type bodyCode)
    (postTree : GenericForHeader.TokenDiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary certificates definitions administrative
        type (TypedForHeader.Fallthrough type) context scope post postCode)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        (LocalLoop.iterate type conditionCode bodyCode postCode selfReason) (LocalLoop.resultType type) definitions) :
    TokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary expressionSyntax certificates definitions administrative solved context scope (.initializers [] condition post statements) expected type
        (LocalLoop.iterate type conditionCode bodyCode postCode selfReason) := by
  exact ⟨ProducedExtractionFor.initializersDone (factory := factory) conditionFound conditionType conditionTree loopBody.toProduced postTree.toProduced nativeTyped, .pair loopBody.tokens postTree.tokens⟩

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
    (remaining : TokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary expressionSyntax certificates definitions administrative solved
        nextContext ((binder.id, payload) :: scope) (.initializers rest condition post statements) expected type body) :
    TokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary expressionSyntax certificates definitions administrative solved
        context scope (.initializers (.letDecl binder none :: rest) condition post statements) expected type (.letE annotation.expression body) := by
  exact ⟨ProducedExtractionFor.initializerUninitialized (factory := factory) monomorphic extended ordinary projected allocation annotation same remaining.toProduced, remaining.tokens⟩

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
    (remaining : TokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary expressionSyntax certificates definitions administrative solved
        nextContext ((binder.id, lowered.type) :: scope) (.initializers rest condition post statements) expected type body) :
    TokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary expressionSyntax certificates definitions administrative solved
        context scope (.initializers (.letDecl binder (some initializer) :: rest) condition post statements) expected type (sequence type lowered.expression annotation.expression body) := by
  exact ⟨ProducedExtractionFor.initializerInitialized (factory := factory) monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining.toProduced, remaining.tokens⟩

def initializerDiscard
    {context scope expression expressionNode rest lowered body condition post statements expected type}
    (found : source.lookupExpression? expression = some expressionNode)
    (value : certificates context scope expression lowered)
    (remaining : TokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary expressionSyntax certificates definitions administrative solved
        context scope (.initializers rest condition post statements) expected type body) :
    TokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary expressionSyntax certificates definitions administrative solved
        context scope (.initializers (.expression expression :: rest) condition post statements) expected type (LocalSequence.discard (LocalLoop.controlType type) lowered.expression body) := by
  exact ⟨ProducedExtractionFor.initializerDiscard (factory := factory) found value remaining.toProduced, remaining.tokens⟩

def initializerAssign
    {context scope assignment operator rhs rest body condition post statements expected type}
    (head : GenericAssignmentStatements.Head values source context (certificates context) scope administrative definitions assignment operator rhs)
    (site : SourceCoreElaboration.ErrorSite)
    (origin : AssignmentDiagnosticOrigins.OccursFor tracked source site assignment operator rhs)
    (same : head.invalid = invalidOperand site assignment.target.root operator)
    (sourceTyped : ∀ binder, SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder →
      SourceProjectionsHaveType source context binder.scheme.body assignment.target.projections assignment.target.type)
    (rightTyped : ExpressionHasType source context rhs assignment.target.type)
    (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
      SourceCoreRawMetadata.runtimeType assignment.target.type = .integer)
    (remaining : TokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary expressionSyntax certificates definitions administrative solved
        context scope (.initializers rest condition post statements) expected type body) :
    TokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary expressionSyntax certificates definitions administrative solved
        context scope (.initializers (.assignValue assignment operator rhs :: rest) condition post statements) expected type (head.emit body (LocalLoop.controlType type)) := by
  exact ⟨ProducedExtractionFor.initializerAssign (factory := factory) head site origin same sourceTyped rightTyped profile remaining.toProduced, .pair remaining.tokens (.assignment head site origin same sourceTyped rightTyped profile)⟩

def initializerBitNot
    {context scope assignment rest body condition post statements expected type}
    (head : CompatibleBitNotStatements.Head context scope assignment)
    (writable : ∀ binder, SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder →
      WritableLocal context assignment.target.root binder.scheme.body)
    (bare : assignment.target.projections = [])
    (profile : SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
      SourceCoreRawMetadata.runtimeType assignment.target.type = .integer)
    (site : SourceCoreElaboration.ErrorSite)
    (origin : EmittedDiagnosticTokenPlan.UnaryOccursFor tracked source site assignment)
    (same : head.invalid = invalidUnary site assignment.target.root)
    (remaining : TokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary expressionSyntax certificates definitions administrative solved
        context scope (.initializers rest condition post statements) expected type body) :
    TokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary expressionSyntax certificates definitions administrative solved
        context scope (.initializers (.assignBitNot assignment :: rest) condition post statements) expected type (head.emit body (LocalLoop.controlType type)) := by
  exact ⟨ProducedExtractionFor.initializerBitNot (factory := factory) head writable bare profile remaining.toProduced, .pair remaining.tokens (.unary head writable bare profile site origin same)⟩

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
        TokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary expressionSyntax certificates definitions administrative solved
          childContext request.scope (.statements false request.statements) expected type request.code)
    (remaining : TokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary expressionSyntax certificates definitions administrative solved
        context scope (.statements mode rest) expected type body)
    (sameLedger : compilation.solvedRequirements = solved) :
    TokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary expressionSyntax certificates definitions administrative solved
        context scope (.statements mode (id :: rest)) expected type (LocalLoop.sequence type matched body) := by
  exact ⟨ProducedExtractionFor.matchWith (factory := factory) found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary (fun request member childContext related => (children request member childContext related).toProduced) remaining.toProduced sameLedger, .pair (.selected (fun request member childContext related => (children request member childContext related).tokens)) remaining.tokens⟩
end TokenExtractionFor
end Solcore.SourceSemantics.CoreLowering.GenericImperativeMatch
