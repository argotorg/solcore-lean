import Solcore.SourceSemantics.CoreLowering.EmittedForHeaderDiagnosticExtraction
import Solcore.SourceSemantics.CoreLowering.GenericImperativeMatchPreparedDiagnostics
namespace Solcore.SourceSemantics.CoreLowering.GenericImperativeMatch
open Core Frontend SourceInference
open EmittedDiagnosticPlan
variable {tracked : Bool} {diagnosticPolicy : AssignmentDiagnosticPolicy}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Syntax.ValueAssignOp → Word}
abbrev ProducedExtractionFor (diagnosticPolicy : AssignmentDiagnosticPolicy) (layouts : SourceCoreAllocationLayouts.Prepared)
    (owner : SourceSpecialization.SpecializationKey) (active : TypeSystem.Substitution)
    (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (values : ValuesContext) (source : TypedSource)
    (factory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy source invalidOperand) (expressionSyntax : ExpressionId → Prop)
    (certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate)
    (definitions : DataEnvironment) (administrative : Core.Context) (solved : List SolvedRequirement)
    (context : SourceSemantics.Context) (scope : Scope) (position : Position)
    (expected : TypeSystem.Ty) (type : Ty) (code : Expr) :=
  EmittedDiagnosticPlan.Produced factory (ExtractionFor diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved context scope position expected type code) (fun receipt => receipt.diagnostics)
namespace ProducedExtractionFor
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource} {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {definitions : DataEnvironment} {administrative : Core.Context} {solved : List SolvedRequirement} {diagnosticPolicy : AssignmentDiagnosticPolicy}

variable {tracked : Bool} {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Syntax.ValueAssignOp → Word}
  {factory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy source invalidOperand}
def body
    {context scope mode statements expected type code}
    (syntaxTree : GenericLexicalStatements.Syntax source expressionSyntax context mode statements expected)
    (body : GenericLexicalStatements.Tree layouts owner active frame globals onError values source certificates context scope mode statements expected type code) :
    ProducedExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory expressionSyntax certificates definitions administrative solved
        context scope (.statements mode statements) expected type code := by
  refine ⟨ExtractionFor.body (diagnosticPolicy := diagnosticPolicy) syntaxTree body, .pure, ?_⟩
  intro registry faults
  rfl

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
    (remaining : ProducedExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory expressionSyntax certificates definitions administrative solved
        nextContext ((binder.id, payload) :: scope) (.statements mode rest) expected type body) :
    ProducedExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory expressionSyntax certificates definitions administrative solved
        context scope (.statements mode (id :: rest)) expected type (.letE annotation.expression body) := by
  refine ⟨ExtractionFor.uninitialized (diagnosticPolicy := diagnosticPolicy) found form monomorphic extended ordinary projected allocation annotation same remaining.original, remaining.plan, ?_⟩
  intro registry faults
  dsimp only [ExtractionFor.uninitialized, EmittedDiagnosticPlan.Plan.requirements]
  rw [remaining.equation registry faults]

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
    (remaining : ProducedExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory expressionSyntax certificates definitions administrative solved nextContext ((binder.id, lowered.type) :: scope) (.statements mode rest) expected type body) :
    ProducedExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory expressionSyntax certificates definitions administrative solved
        context scope (.statements mode (id :: rest)) expected type (sequence type lowered.expression annotation.expression body) := by
  refine ⟨ExtractionFor.initialized (diagnosticPolicy := diagnosticPolicy) found form monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining.original, remaining.plan, ?_⟩
  intro registry faults
  dsimp only [ExtractionFor.initialized, EmittedDiagnosticPlan.Plan.requirements]
  rw [remaining.equation registry faults]

def discard
    {context scope mode id node expression expressionNode semicolon rest expected lowered type body}
    (found : source.lookupStatement? id = some node)
    (form : node.form = .expression expression semicolon)
    (notTail : (!semicolon && mode && rest.isEmpty) = false)
    (expressionFound : source.lookupExpression? expression = some expressionNode)
    (value : certificates context scope expression lowered)
    (remaining : ProducedExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory expressionSyntax certificates definitions administrative solved context scope (.statements mode rest) expected type body) :
    ProducedExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory expressionSyntax certificates definitions administrative solved context scope (.statements mode (id :: rest)) expected type
        (LocalSequence.discard (LocalLoop.controlType type) lowered.expression body) := by
  refine ⟨ExtractionFor.discard (diagnosticPolicy := diagnosticPolicy) found form notTail expressionFound value remaining.original, remaining.plan, ?_⟩
  intro registry faults
  dsimp only [ExtractionFor.discard, EmittedDiagnosticPlan.Plan.requirements]
  rw [remaining.equation registry faults]

def block
    {context scope mode id node statements rest expected type innerCode body}
    (found : source.lookupStatement? id = some node)
    (form : node.form = .block statements)
    (inner : ProducedExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory expressionSyntax certificates definitions administrative solved context scope (.statements false statements) expected type innerCode)
    (remaining : ProducedExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory expressionSyntax certificates definitions administrative solved context scope (.statements mode rest) expected type body) :
    ProducedExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory expressionSyntax certificates definitions administrative solved context scope (.statements mode (id :: rest)) expected type
        (LocalLoop.sequence type innerCode body) := by
  refine ⟨ExtractionFor.block (diagnosticPolicy := diagnosticPolicy) found form inner.original remaining.original, .pair inner.plan remaining.plan, ?_⟩
  intro registry faults
  dsimp only [ExtractionFor.block, EmittedDiagnosticPlan.Plan.requirements]
  rw [remaining.equation registry faults, inner.equation registry faults]

def ifThen
    {context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body}
    (found : source.lookupStatement? id = some node)
    (form : node.form = .ifThen condition thenBody elseBody)
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionType : conditionNode.type = .bool)
    (conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩)
    (thenTree : ProducedExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory expressionSyntax certificates definitions administrative solved context scope (.statements false thenBody) expected type thenCode)
    (elseTree : ProducedExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory expressionSyntax certificates definitions administrative solved context scope (.statements false (elseBody.getD [])) expected type elseCode)
    (remaining : ProducedExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory expressionSyntax certificates definitions administrative solved context scope (.statements mode rest) expected type body) :
    ProducedExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory expressionSyntax certificates definitions administrative solved context scope (.statements mode (id :: rest)) expected type
        (LocalLoop.sequence type (LocalLoop.conditional type conditionCode thenCode elseCode) body) := by
  refine ⟨ExtractionFor.ifThen (diagnosticPolicy := diagnosticPolicy) found form conditionFound conditionType conditionTree thenTree.original elseTree.original remaining.original, .pair thenTree.plan (.pair elseTree.plan remaining.plan), ?_⟩
  intro registry faults
  dsimp only [ExtractionFor.ifThen, EmittedDiagnosticPlan.Plan.requirements]
  rw [remaining.equation registry faults, thenTree.equation registry faults, elseTree.equation registry faults]

def breaking
    {context scope mode id node rest expected type}
    (found : source.lookupStatement? id = some node)
    (form : node.form = .breakStmt) :
    ProducedExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory expressionSyntax certificates definitions administrative solved
        context scope (.statements mode (id :: rest)) expected type (LocalLoop.breaking type) := by
  refine ⟨ExtractionFor.breaking (diagnosticPolicy := diagnosticPolicy) found form, .pure, ?_⟩
  intro registry faults
  rfl

def continuing
    {context scope mode id node rest expected type}
    (found : source.lookupStatement? id = some node)
    (form : node.form = .continueStmt) :
    ProducedExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory expressionSyntax certificates definitions administrative solved
        context scope (.statements mode (id :: rest)) expected type (LocalLoop.continuing type) := by
  refine ⟨ExtractionFor.continuing (diagnosticPolicy := diagnosticPolicy) found form, .pure, ?_⟩
  intro registry faults
  rfl

def whileLoop
    {context scope mode id node condition conditionNode statements rest expected type conditionCode loopCode body selfReason}
    (found : source.lookupStatement? id = some node)
    (form : node.form = .whileLoop condition statements)
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionType : conditionNode.type = .bool)
    (conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩)
    (loopBody : ProducedExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory expressionSyntax certificates definitions administrative solved
        context scope (.statements false statements) expected type loopCode)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        (LocalLoop.whileLoop type conditionCode loopCode selfReason) (LocalLoop.resultType type) definitions)
    (remaining : ProducedExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory expressionSyntax certificates definitions administrative solved
        context scope (.statements mode rest) expected type body) :
    ProducedExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory expressionSyntax certificates definitions administrative solved
        context scope (.statements mode (id :: rest)) expected type
        (LocalLoop.sequence type (LocalLoop.whileLoop type conditionCode loopCode selfReason) body) := by
  refine ⟨ExtractionFor.whileLoop (diagnosticPolicy := diagnosticPolicy) found form conditionFound conditionType conditionTree loopBody.original nativeTyped remaining.original, .pair loopBody.plan remaining.plan, ?_⟩
  intro registry faults
  dsimp only [ExtractionFor.whileLoop, EmittedDiagnosticPlan.Plan.requirements]
  rw [remaining.equation registry faults, loopBody.equation registry faults]

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
    (remaining : ProducedExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory expressionSyntax certificates definitions administrative solved
        context scope (.statements mode rest) expected type body) :
    ProducedExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory expressionSyntax certificates definitions administrative solved
        context scope (.statements mode (id :: rest)) expected type (head.emit body (LocalLoop.controlType type)) := by
  refine ⟨PreparedDiagnostics.assign (diagnosticPolicy := diagnosticPolicy) found form head (factory.residual head) (factory.materialize head site origin same) remaining.original, .pair remaining.plan (.assignment head site origin same sourceTyped rightTyped profile), ?_⟩
  intro registry faults
  dsimp only [PreparedDiagnostics.assign, EmittedDiagnosticPlan.Plan.requirements, ExtractionFor.assign]
  rw [remaining.equation registry faults]

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
    (remaining : ProducedExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory expressionSyntax certificates definitions administrative solved
        context scope (.statements mode rest) expected type body) :
    ProducedExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory expressionSyntax certificates definitions administrative solved
        context scope (.statements mode (id :: rest)) expected type (head.emit body (LocalLoop.controlType type)) := by
  refine ⟨ExtractionFor.bitNot (diagnosticPolicy := diagnosticPolicy) found form head remaining.original, .pair remaining.plan (.unary head writable bare profile), ?_⟩
  intro registry faults
  dsimp only [ExtractionFor.bitNot, EmittedDiagnosticPlan.Plan.requirements]
  rw [remaining.equation registry faults]

def forLoop
    {context scope mode id node initializer condition post statements rest expected type initialCode body}
    (found : source.lookupStatement? id = some node)
    (form : node.form = .forLoop initializer condition post statements)
    (initial : ProducedExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory expressionSyntax certificates definitions administrative solved context scope (.initializers initializer condition post statements) expected type initialCode)
    (remaining : ProducedExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory expressionSyntax certificates definitions administrative solved context scope (.statements mode rest) expected type body) :
    ProducedExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory expressionSyntax certificates definitions administrative solved context scope (.statements mode (id :: rest)) expected type (LocalLoop.sequence type initialCode body) := by
  refine ⟨ExtractionFor.forLoop (diagnosticPolicy := diagnosticPolicy) found form initial.original remaining.original, .pair initial.plan remaining.plan, ?_⟩
  intro registry faults
  dsimp only [ExtractionFor.forLoop, EmittedDiagnosticPlan.Plan.requirements]
  rw [remaining.equation registry faults, initial.equation registry faults]

def initializersDone
    {context scope condition conditionNode post statements expected type conditionCode bodyCode postCode selfReason}
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionType : conditionNode.type = .bool)
    (conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩)
    (loopBody : ProducedExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory expressionSyntax certificates definitions administrative solved context scope (.statements false statements) expected type bodyCode)
    (postTree : GenericForHeader.ProducedDiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source factory certificates definitions administrative
        type (TypedForHeader.Fallthrough type) context scope post postCode)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        (LocalLoop.iterate type conditionCode bodyCode postCode selfReason) (LocalLoop.resultType type) definitions) :
    ProducedExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory expressionSyntax certificates definitions administrative solved context scope (.initializers [] condition post statements) expected type
        (LocalLoop.iterate type conditionCode bodyCode postCode selfReason) := by
  refine ⟨PreparedDiagnostics.initializersDone (diagnosticPolicy := diagnosticPolicy) conditionFound conditionType conditionTree loopBody.original postTree.original nativeTyped, .pair loopBody.plan postTree.plan, ?_⟩
  intro registry faults
  dsimp only [PreparedDiagnostics.initializersDone, EmittedDiagnosticPlan.Plan.requirements, ExtractionFor.initializersDone]
  rw [loopBody.equation registry faults, postTree.equation registry faults]

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
    (remaining : ProducedExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory expressionSyntax certificates definitions administrative solved
        nextContext ((binder.id, payload) :: scope) (.initializers rest condition post statements) expected type body) :
    ProducedExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory expressionSyntax certificates definitions administrative solved
        context scope (.initializers (.letDecl binder none :: rest) condition post statements) expected type (.letE annotation.expression body) := by
  refine ⟨ExtractionFor.initializerUninitialized (diagnosticPolicy := diagnosticPolicy) monomorphic extended ordinary projected allocation annotation same remaining.original, remaining.plan, ?_⟩
  intro registry faults
  dsimp only [ExtractionFor.initializerUninitialized, EmittedDiagnosticPlan.Plan.requirements]
  rw [remaining.equation registry faults]

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
    (remaining : ProducedExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory expressionSyntax certificates definitions administrative solved
        nextContext ((binder.id, lowered.type) :: scope) (.initializers rest condition post statements) expected type body) :
    ProducedExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory expressionSyntax certificates definitions administrative solved
        context scope (.initializers (.letDecl binder (some initializer) :: rest) condition post statements) expected type (sequence type lowered.expression annotation.expression body) := by
  refine ⟨ExtractionFor.initializerInitialized (diagnosticPolicy := diagnosticPolicy) monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining.original, remaining.plan, ?_⟩
  intro registry faults
  dsimp only [ExtractionFor.initializerInitialized, EmittedDiagnosticPlan.Plan.requirements]
  rw [remaining.equation registry faults]

def initializerDiscard
    {context scope expression expressionNode rest lowered body condition post statements expected type}
    (found : source.lookupExpression? expression = some expressionNode)
    (value : certificates context scope expression lowered)
    (remaining : ProducedExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory expressionSyntax certificates definitions administrative solved
        context scope (.initializers rest condition post statements) expected type body) :
    ProducedExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory expressionSyntax certificates definitions administrative solved
        context scope (.initializers (.expression expression :: rest) condition post statements) expected type (LocalSequence.discard (LocalLoop.controlType type) lowered.expression body) := by
  refine ⟨ExtractionFor.initializerDiscard (diagnosticPolicy := diagnosticPolicy) found value remaining.original, remaining.plan, ?_⟩
  intro registry faults
  dsimp only [ExtractionFor.initializerDiscard, EmittedDiagnosticPlan.Plan.requirements]
  rw [remaining.equation registry faults]

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
    (remaining : ProducedExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory expressionSyntax certificates definitions administrative solved
        context scope (.initializers rest condition post statements) expected type body) :
    ProducedExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory expressionSyntax certificates definitions administrative solved
        context scope (.initializers (.assignValue assignment operator rhs :: rest) condition post statements) expected type (head.emit body (LocalLoop.controlType type)) := by
  refine ⟨PreparedDiagnostics.initializerAssign (diagnosticPolicy := diagnosticPolicy) head (factory.residual head) (factory.materialize head site origin same) remaining.original, .pair remaining.plan (.assignment head site origin same sourceTyped rightTyped profile), ?_⟩
  intro registry faults
  dsimp only [PreparedDiagnostics.initializerAssign, EmittedDiagnosticPlan.Plan.requirements, ExtractionFor.initializerAssign]
  rw [remaining.equation registry faults]

def initializerBitNot
    {context scope assignment rest body condition post statements expected type}
    (head : CompatibleBitNotStatements.Head context scope assignment)
    (writable : ∀ binder, SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder →
      WritableLocal context assignment.target.root binder.scheme.body)
    (bare : assignment.target.projections = [])
    (profile : SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
      SourceCoreRawMetadata.runtimeType assignment.target.type = .integer)
    (remaining : ProducedExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory expressionSyntax certificates definitions administrative solved
        context scope (.initializers rest condition post statements) expected type body) :
    ProducedExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory expressionSyntax certificates definitions administrative solved
        context scope (.initializers (.assignBitNot assignment :: rest) condition post statements) expected type (head.emit body (LocalLoop.controlType type)) := by
  refine ⟨ExtractionFor.initializerBitNot (diagnosticPolicy := diagnosticPolicy) head remaining.original, .pair remaining.plan (.unary head writable bare profile), ?_⟩
  intro registry faults
  dsimp only [ExtractionFor.initializerBitNot, EmittedDiagnosticPlan.Plan.requirements]
  rw [remaining.equation registry faults]

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
        ProducedExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory expressionSyntax certificates definitions administrative solved
          childContext request.scope (.statements false request.statements) expected type request.code)
    (remaining : ProducedExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory expressionSyntax certificates definitions administrative solved
        context scope (.statements mode rest) expected type body)
    (sameLedger : compilation.solvedRequirements = solved) :
    ProducedExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory expressionSyntax certificates definitions administrative solved
        context scope (.statements mode (id :: rest)) expected type (LocalLoop.sequence type matched body) := by
  refine ⟨ExtractionFor.matchWith (diagnosticPolicy := diagnosticPolicy) found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary (fun request member childContext related => (children request member childContext related).original) remaining.original sameLedger, .pair (.selected requests context (resolution.hiddenScrutinee :: scope.map Prod.fst) scrutineeNode.type resolution.cases resolution.defaultBody (fun request member childContext related => (children request member childContext related).plan)) remaining.plan, ?_⟩
  intro registry faults
  dsimp only [ExtractionFor.matchWith, EmittedDiagnosticPlan.Plan.requirements]
  simp only [Produced.equation]
end ProducedExtractionFor
end Solcore.SourceSemantics.CoreLowering.GenericImperativeMatch
