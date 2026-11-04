import Solcore.SourceSemantics.CoreLowering.Internal.Diagnostics.EmittedForHeaders
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.GenericImperativeMatchReady
import Solcore.SourceSemantics.CoreLowering.Internal.Diagnostics.EmittedPlans
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.GenericImperativeFor
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.PlaceReflection
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.AssignmentHeads

/-!
# Emitted diagnostics of matches

Extraction of diagnostics from emitted code and matches, with their tokens and coupling, and the diagnostic origins of projected bit-not updates.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.EmittedDiagnosticExtraction
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
      SourceCoreRawMetadata.runtimeType assignment.target.type = .integer ∧ operator.wordOnly = false)
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
      SourceCoreRawMetadata.runtimeType assignment.target.type = .integer ∧ operator.wordOnly = false)
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.EmittedMatchTokenExtraction
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
      SourceCoreRawMetadata.runtimeType assignment.target.type = .integer ∧ operator.wordOnly = false)
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
      SourceCoreRawMetadata.runtimeType assignment.target.type = .integer ∧ operator.wordOnly = false)
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.EmittedMatchCoupling
/-! Joint static receipts bind each actual compiler Tree to its retained Plan.
Assignments share one complete head in both indices; selected children keep
exact request membership and scoped contexts. Consumers recurse this receipt. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericImperativeMatch
open Core Frontend SourceInference
open EmittedDiagnosticPlan
open TypedLexicalWhile (absentRequest initializedRequest sequence)
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource}
  {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate} {definitions : DataEnvironment} {administrative : Core.Context}

variable {tracked : Bool} {diagnosticPolicy : AssignmentDiagnosticPolicy}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Syntax.ValueAssignOp → Word}
inductive Coupled (factory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy source invalidOperand)
    (invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word)
    (missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word) :
    {context : SourceSemantics.Context} → {scope : Scope} → {position : Position} →
    {expected : TypeSystem.Ty} → {type : Ty} → {code : Expr} →
    Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
      context scope position expected type code → Plan factory → Prop where
  | body {context scope mode statements expected type code}
      {syntaxTree : GenericLexicalStatements.Syntax source expressionSyntax context mode statements expected}
      {body : GenericLexicalStatements.Tree layouts owner active frame globals onError values source certificates context scope mode statements expected type code}
      : Coupled factory invalidProjection missingDefault (.body syntaxTree body) .pure

  | uninitialized {context nextContext scope mode id node binder rest expected type body payload}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .letDecl binder none}
      {monomorphic : binder.scheme.quantified = []}
      {extended : BinderExtends source.owner context binder nextContext}
      {ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false}
      {projected : values.checked.catalog.project binder.scheme.body = .ok payload}
      {allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (absentRequest source scope binder payload)}
      {annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
        (layouts.allocatorAt owner active onError) (absentRequest source scope binder payload)}
      {same : annotation.original = allocation.expression}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        nextContext ((binder.id, payload) :: scope) (.statements mode rest) expected type body}
      {remainingPlan : Plan factory}
      (remainingCoupled : Coupled factory invalidProjection missingDefault remaining remainingPlan)
      : Coupled factory invalidProjection missingDefault (.uninitialized found form monomorphic extended ordinary projected allocation annotation same remaining) remainingPlan

  | initialized {context nextContext scope mode id node binder initializer initializerNode lowered body rest expected type}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .letDecl binder (some initializer)}
      {monomorphic : binder.scheme.quantified = []}
      {extended : BinderExtends source.owner context binder nextContext}
      {ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false}
      {initializerFound : source.lookupExpression? initializer = some initializerNode}
      {sourceType : initializerNode.type = binder.scheme.body}
      {initial : certificates context scope initializer lowered}
      {allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (initializedRequest source scope binder lowered.type)}
      {annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
        (layouts.allocatorAt owner active onError) (initializedRequest source scope binder lowered.type)}
      {same : annotation.original = allocation.expression}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative nextContext ((binder.id, lowered.type) :: scope) (.statements mode rest) expected type body}
      {remainingPlan : Plan factory}
      (remainingCoupled : Coupled factory invalidProjection missingDefault remaining remainingPlan)
      : Coupled factory invalidProjection missingDefault (.initialized found form monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining) remainingPlan

  | discard {context scope mode id node expression expressionNode semicolon rest expected lowered type body}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .expression expression semicolon}
      {notTail : (!semicolon && mode && rest.isEmpty) = false}
      {expressionFound : source.lookupExpression? expression = some expressionNode}
      {value : certificates context scope expression lowered}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode rest) expected type body}
      {remainingPlan : Plan factory}
      (remainingCoupled : Coupled factory invalidProjection missingDefault remaining remainingPlan)
      : Coupled factory invalidProjection missingDefault (.discard found form notTail expressionFound value remaining) remainingPlan

  | block {context scope mode id node statements rest expected type innerCode body}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .block statements}
      {inner : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements false statements) expected type innerCode}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode rest) expected type body}
      {innerPlan : Plan factory}
      (innerCoupled : Coupled factory invalidProjection missingDefault inner innerPlan)
      {remainingPlan : Plan factory}
      (remainingCoupled : Coupled factory invalidProjection missingDefault remaining remainingPlan)
      : Coupled factory invalidProjection missingDefault (.block found form inner remaining) (.pair innerPlan remainingPlan)

  | ifThen {context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .ifThen condition thenBody elseBody}
      {conditionFound : source.lookupExpression? condition = some conditionNode}
      {conditionType : conditionNode.type = .bool}
      {conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩}
      {thenTree : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements false thenBody) expected type thenCode}
      {elseTree : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements false (elseBody.getD [])) expected type elseCode}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode rest) expected type body}
      {thenTreePlan : Plan factory}
      (thenTreeCoupled : Coupled factory invalidProjection missingDefault thenTree thenTreePlan)
      {elseTreePlan : Plan factory}
      (elseTreeCoupled : Coupled factory invalidProjection missingDefault elseTree elseTreePlan)
      {remainingPlan : Plan factory}
      (remainingCoupled : Coupled factory invalidProjection missingDefault remaining remainingPlan)
      : Coupled factory invalidProjection missingDefault (.ifThen found form conditionFound conditionType conditionTree thenTree elseTree remaining) (.pair thenTreePlan (.pair elseTreePlan remainingPlan))

  | breaking {context scope mode id node rest expected type}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .breakStmt}
      : Coupled factory invalidProjection missingDefault (.breaking (context := context) (scope := scope) (mode := mode) (rest := rest) (expected := expected) (type := type) found form) .pure

  | continuing {context scope mode id node rest expected type}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .continueStmt}
      : Coupled factory invalidProjection missingDefault (.continuing (context := context) (scope := scope) (mode := mode) (rest := rest) (expected := expected) (type := type) found form) .pure

  | whileLoop {context scope mode id node condition conditionNode statements rest expected type conditionCode loopCode body selfReason}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .whileLoop condition statements}
      {conditionFound : source.lookupExpression? condition = some conditionNode}
      {conditionType : conditionNode.type = .bool}
      {conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩}
      {loopBody : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements false statements) expected type loopCode}
      {nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        (LocalLoop.whileLoop type conditionCode loopCode selfReason) (LocalLoop.resultType type) definitions}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode rest) expected type body}
      {loopBodyPlan : Plan factory}
      (loopBodyCoupled : Coupled factory invalidProjection missingDefault loopBody loopBodyPlan)
      {remainingPlan : Plan factory}
      (remainingCoupled : Coupled factory invalidProjection missingDefault remaining remainingPlan)
      : Coupled factory invalidProjection missingDefault (.whileLoop found form conditionFound conditionType conditionTree loopBody nativeTyped remaining) (.pair loopBodyPlan remainingPlan)

  | assign {context scope mode id node assignment operator rhs rest expected type body}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .assignValue assignment operator rhs}
      {head : GenericAssignmentStatements.Head values source context (certificates context) scope administrative definitions assignment operator rhs}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode rest) expected type body}
      {remainingPlan : Plan factory}
      (remainingCoupled : Coupled factory invalidProjection missingDefault remaining remainingPlan)
      (site : SourceCoreElaboration.ErrorSite)
      (origin : AssignmentDiagnosticOrigins.OccursFor tracked source site assignment operator rhs)
      (sameToken : head.invalid = invalidOperand site assignment.target.root operator)
      (sourceTyped : ∀ binder, SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder →
        SourceProjectionsHaveType source context binder.scheme.body assignment.target.projections assignment.target.type)
      (rightTyped : ExpressionHasType source context rhs assignment.target.type)
      (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
        SourceCoreRawMetadata.runtimeType assignment.target.type = .integer ∧ operator.wordOnly = false)
      (fuel : Nat)
      (prepared : head.PreparedAt site fuel (invalidProjection site assignment.target.root) (missingDefault site assignment.target.root))
      : Coupled factory invalidProjection missingDefault (.assign found form head remaining) (.pair remainingPlan (.assignment head site origin sameToken sourceTyped rightTyped profile))

  | bitNot {context scope mode id node assignment rest expected type body}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .assignBitNot assignment}
      {head : CompatibleBitNotStatements.Head context scope assignment}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode rest) expected type body}
      {remainingPlan : Plan factory}
      (remainingCoupled : Coupled factory invalidProjection missingDefault remaining remainingPlan)
      (writable : ∀ binder, SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder →
        WritableLocal context assignment.target.root binder.scheme.body)
      (bare : assignment.target.projections = [])
      (profile : SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
        SourceCoreRawMetadata.runtimeType assignment.target.type = .integer)
      : Coupled factory invalidProjection missingDefault (.bitNot found form head remaining) (.pair remainingPlan (.unary head writable bare profile))

  | forLoop {context scope mode id node initializer condition post statements rest expected type initialCode body}
      {found : source.lookupStatement? id = some node} {form : node.form = .forLoop initializer condition post statements}
      {initial : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.initializers initializer condition post statements) expected type initialCode}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode rest) expected type body}
      {initialPlan : Plan factory}
      (initialCoupled : Coupled factory invalidProjection missingDefault initial initialPlan) {remainingPlan : Plan factory}
      (remainingCoupled : Coupled factory invalidProjection missingDefault remaining remainingPlan) :
      Coupled factory invalidProjection missingDefault (.forLoop found form initial remaining) (.pair initialPlan remainingPlan)

  | initializersDone {context scope condition conditionNode post statements expected type conditionCode bodyCode postCode selfReason}
      {conditionFound : source.lookupExpression? condition = some conditionNode}
      {conditionType : conditionNode.type = .bool}
      {conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩}
      {loopBody : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements false statements) expected type bodyCode}
      {postTree : GenericForHeader.Tree layouts owner active frame globals onError values source certificates definitions administrative
        type (TypedForHeader.Fallthrough type) context scope post postCode}
      {nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        (LocalLoop.iterate type conditionCode bodyCode postCode selfReason) (LocalLoop.resultType type) definitions}
      {loopBodyPlan : Plan factory}
      (loopCoupled : Coupled factory invalidProjection missingDefault loopBody loopBodyPlan) {postTreePlan : Plan factory}
      (postCoupled : GenericForHeader.Coupled factory invalidProjection missingDefault postTree postTreePlan) :
      Coupled factory invalidProjection missingDefault (.initializersDone conditionFound conditionType conditionTree loopBody postTree nativeTyped) (.pair loopBodyPlan postTreePlan)

  | initializerUninitialized {context nextContext scope binder rest body payload condition post statements expected type}
      {monomorphic : binder.scheme.quantified = []}
      {extended : BinderExtends source.owner context binder nextContext}
      {ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false}
      {projected : values.checked.catalog.project binder.scheme.body = .ok payload}
      {allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (absentRequest source scope binder payload)}
      {annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
        (layouts.allocatorAt owner active onError) (absentRequest source scope binder payload)}
      {same : annotation.original = allocation.expression}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        nextContext ((binder.id, payload) :: scope) (.initializers rest condition post statements) expected type body}
      {remainingPlan : Plan factory}
      (remainingCoupled : Coupled factory invalidProjection missingDefault remaining remainingPlan)
      : Coupled factory invalidProjection missingDefault (.initializerUninitialized monomorphic extended ordinary projected allocation annotation same remaining) remainingPlan

  | initializerInitialized {context nextContext scope binder initializer initializerNode lowered body rest condition post statements expected type}
      {monomorphic : binder.scheme.quantified = []}
      {extended : BinderExtends source.owner context binder nextContext}
      {ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false}
      {initializerFound : source.lookupExpression? initializer = some initializerNode}
      {sourceType : initializerNode.type = binder.scheme.body}
      {initial : certificates context scope initializer lowered}
      {allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (initializedRequest source scope binder lowered.type)}
      {annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
        (layouts.allocatorAt owner active onError) (initializedRequest source scope binder lowered.type)}
      {same : annotation.original = allocation.expression}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        nextContext ((binder.id, lowered.type) :: scope) (.initializers rest condition post statements) expected type body}
      {remainingPlan : Plan factory}
      (remainingCoupled : Coupled factory invalidProjection missingDefault remaining remainingPlan)
      : Coupled factory invalidProjection missingDefault (.initializerInitialized monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining) remainingPlan

  | initializerDiscard {context scope expression expressionNode rest lowered body condition post statements expected type}
      {found : source.lookupExpression? expression = some expressionNode}
      {value : certificates context scope expression lowered}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.initializers rest condition post statements) expected type body}
      {remainingPlan : Plan factory}
      (remainingCoupled : Coupled factory invalidProjection missingDefault remaining remainingPlan)
      : Coupled factory invalidProjection missingDefault (.initializerDiscard found value remaining) remainingPlan

  | initializerAssign {context scope assignment operator rhs rest body condition post statements expected type}
      {head : GenericAssignmentStatements.Head values source context (certificates context) scope administrative definitions assignment operator rhs}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.initializers rest condition post statements) expected type body}
      {remainingPlan : Plan factory}
      (remainingCoupled : Coupled factory invalidProjection missingDefault remaining remainingPlan)
      (site : SourceCoreElaboration.ErrorSite)
      (origin : AssignmentDiagnosticOrigins.OccursFor tracked source site assignment operator rhs)
      (sameToken : head.invalid = invalidOperand site assignment.target.root operator)
      (sourceTyped : ∀ binder, SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder →
        SourceProjectionsHaveType source context binder.scheme.body assignment.target.projections assignment.target.type)
      (rightTyped : ExpressionHasType source context rhs assignment.target.type)
      (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
        SourceCoreRawMetadata.runtimeType assignment.target.type = .integer ∧ operator.wordOnly = false)
      (fuel : Nat)
      (prepared : head.PreparedAt site fuel (invalidProjection site assignment.target.root) (missingDefault site assignment.target.root))
      : Coupled factory invalidProjection missingDefault (.initializerAssign head remaining) (.pair remainingPlan (.assignment head site origin sameToken sourceTyped rightTyped profile))

  | initializerBitNot {context scope assignment rest body condition post statements expected type}
      {head : CompatibleBitNotStatements.Head context scope assignment}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.initializers rest condition post statements) expected type body}
      {remainingPlan : Plan factory}
      (remainingCoupled : Coupled factory invalidProjection missingDefault remaining remainingPlan)
      (writable : ∀ binder, SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder →
        WritableLocal context assignment.target.root binder.scheme.body)
      (bare : assignment.target.projections = [])
      (profile : SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
        SourceCoreRawMetadata.runtimeType assignment.target.type = .integer)
      : Coupled factory invalidProjection missingDefault (.initializerBitNot head remaining) (.pair remainingPlan (.unary head writable bare profile))

  | matchWith {context scope mode id node resolution scrutineeNode rest expected type matched body selfReason control caseFacts}
      {found : source.lookupStatement? id = some node} {form : node.form = .matchWith resolution}
      {scrutineeFound : source.lookupExpression? resolution.scrutinee = some scrutineeNode}
      {scrutineeTyped : ExpressionHasType source context resolution.scrutinee scrutineeNode.type}
      {casesTyped : MatchCasesHaveType source control context scrutineeNode.type resolution.cases caseFacts}
      {defaultTyped : ∀ statements, resolution.defaultBody = some statements →
        ∃ finalContext facts, StatementsHaveType source control context statements finalContext facts}
      {compilation : SourceCoreCompatibleDataMatches.Context}
      {sameValues : compilation.values = values} {sameDefinitions : compilation.definitions = definitions}
      {allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
        (layouts.allocatorAt owner active onError))}
      {requests : List GenericMatchChildren.Request}
      {receipt : CompatibleMatchCertificates.Certificate compilation source scope id resolution type selfReason
        (certificates context) (GenericMatchChildren.Occurs requests) matched}
      {ordinary : CompatibleMatchSelectionPrefix.Ordinary receipt}
      {children : ∀ request, request ∈ requests → ∀ childContext,
        GenericMatchChildren.ScopedContextFor source context (resolution.hiddenScrutinee :: scope.map Prod.fst) scrutineeNode.type resolution.cases resolution.defaultBody request childContext →
        Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
          childContext request.scope (.statements false request.statements) expected type request.code}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode rest) expected type body}
      {childPlans : ∀ request, request ∈ requests → ∀ childContext,
        GenericMatchChildren.ScopedContextFor source context (resolution.hiddenScrutinee :: scope.map Prod.fst) scrutineeNode.type resolution.cases resolution.defaultBody request childContext → Plan factory}
      (childCoupled : ∀ request member childContext valid, Coupled factory invalidProjection missingDefault
        (children request member childContext valid) (childPlans request member childContext valid))
      {remainingPlan : Plan factory}
      (remainingCoupled : Coupled factory invalidProjection missingDefault remaining remainingPlan) :
      Coupled factory invalidProjection missingDefault (.matchWith found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation
        sameValues sameDefinitions allocator requests receipt ordinary children remaining) (.pair (.selected requests context (resolution.hiddenScrutinee :: scope.map Prod.fst) scrutineeNode.type resolution.cases resolution.defaultBody childPlans) remainingPlan)

  | terminalBlock {context scope mode id node statements rest expected type innerCode suffix}
      {unique : NodeOccurrencesUnique source}
      {found : source.lookupStatement? id = some node} {form : node.form = .block statements}
      {inner : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements false statements) expected type innerCode}
      {stops : GenericLexicalStatements.Stopped source statements}
      {issued : GenericLexicalStatements.IssuedSuffix source scope mode rest type suffix}
      {innerPlan : Plan factory}
      (innerCoupled : Coupled factory invalidProjection missingDefault inner innerPlan) :
      Coupled factory invalidProjection missingDefault (.terminalBlock unique found form inner stops issued) innerPlan

  | terminalIf {context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode suffix}
      {unique : NodeOccurrencesUnique source}
      {found : source.lookupStatement? id = some node} {form : node.form = .ifThen condition thenBody (some elseBody)}
      {conditionFound : source.lookupExpression? condition = some conditionNode}
      {conditionType : conditionNode.type = .bool}
      {conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩}
      {thenTree : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements false thenBody) expected type thenCode}
      {elseTree : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements false elseBody) expected type elseCode}
      {thenStops : GenericLexicalStatements.Stopped source thenBody}
      {elseStops : GenericLexicalStatements.Stopped source elseBody}
      {issued : GenericLexicalStatements.IssuedSuffix source scope mode rest type suffix}
      {thenTreePlan : Plan factory}
      (thenCoupled : Coupled factory invalidProjection missingDefault thenTree thenTreePlan)
      {elseTreePlan : Plan factory}
      (elseCoupled : Coupled factory invalidProjection missingDefault elseTree elseTreePlan) :
      Coupled factory invalidProjection missingDefault
        (.terminalIf unique found form conditionFound conditionType conditionTree thenTree elseTree thenStops elseStops issued) (.pair thenTreePlan elseTreePlan)

  | terminalMatch {context scope mode id node resolution scrutineeNode rest expected type matched suffix selfReason control caseFacts}
      {unique : NodeOccurrencesUnique source}
      {found : source.lookupStatement? id = some node} {form : node.form = .matchWith resolution}
      {scrutineeFound : source.lookupExpression? resolution.scrutinee = some scrutineeNode}
      {scrutineeTyped : ExpressionHasType source context resolution.scrutinee scrutineeNode.type}
      {casesTyped : MatchCasesHaveType source control context scrutineeNode.type resolution.cases caseFacts}
      {defaultTyped : ∀ statements, resolution.defaultBody = some statements →
        ∃ finalContext facts, StatementsHaveType source control context statements finalContext facts}
      {compilation : SourceCoreCompatibleDataMatches.Context}
      {sameValues : compilation.values = values} {sameDefinitions : compilation.definitions = definitions}
      {allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
        (layouts.allocatorAt owner active onError))}
      {requests : List GenericMatchChildren.Request}
      {receipt : CompatibleMatchCertificates.Certificate compilation source scope id resolution type selfReason
        (certificates context) (GenericMatchChildren.Occurs requests) matched}
      {ordinary : CompatibleMatchSelectionPrefix.Ordinary receipt}
      {children : ∀ request, request ∈ requests → ∀ childContext,
        GenericMatchChildren.ScopedContextFor source context (resolution.hiddenScrutinee :: scope.map Prod.fst) scrutineeNode.type resolution.cases resolution.defaultBody request childContext →
        Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
          childContext request.scope (.statements false request.statements) expected type request.code}
      {stops : ReachableMatchContinuations.DefaultStopped source id resolution}
      {issued : GenericLexicalStatements.IssuedSuffix source scope mode rest type suffix}
      {childPlans : ∀ request, request ∈ requests → ∀ childContext,
        GenericMatchChildren.ScopedContextFor source context (resolution.hiddenScrutinee :: scope.map Prod.fst) scrutineeNode.type resolution.cases resolution.defaultBody request childContext → Plan factory}
      (childCoupled : ∀ request member childContext valid, Coupled factory invalidProjection missingDefault
        (children request member childContext valid) (childPlans request member childContext valid))
      :
      Coupled factory invalidProjection missingDefault (.terminalMatch unique found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation
        sameValues sameDefinitions allocator requests receipt ordinary children stops issued) (.selected requests context (resolution.hiddenScrutinee :: scope.map Prod.fst) scrutineeNode.type resolution.cases resolution.defaultBody childPlans)
end Solcore.SourceSemantics.CoreLowering.GenericImperativeMatch
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.EmittedMatchCoupledExtraction
/-! Finite adapters retain the original extraction and actual preparation.
The joint receipt shares each chosen head with both Tree and Plan, and keeps
the corresponding receipt for every actual child. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericImperativeMatch
open Core Frontend SourceInference
open EmittedDiagnosticPlan EmittedDiagnosticTokenPlan
open TypedLexicalWhile (absentRequest initializedRequest sequence)
variable {tracked : Bool} {diagnosticPolicy : AssignmentDiagnosticPolicy}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Syntax.ValueAssignOp → Word}
structure CoupledTokenExtractionFor (diagnosticPolicy : AssignmentDiagnosticPolicy) (layouts : SourceCoreAllocationLayouts.Prepared)
    (owner : SourceSpecialization.SpecializationKey) (active : TypeSystem.Substitution)
    (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (values : ValuesContext) (source : TypedSource)
    (factory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy source invalidOperand)
    (invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word)
    (invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word)
    (missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word) (expressionSyntax : ExpressionId → Prop)
    (certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate)
    (definitions : DataEnvironment) (administrative : Core.Context) (solved : List SolvedRequirement)
    (context : SourceSemantics.Context) (scope : Scope) (position : Position)
    (expected : TypeSystem.Ty) (type : Ty) (code : Expr) where
  original : EmittedDiagnosticPreparedPlan.Produced factory invalidUnary invalidProjection missingDefault (ExtractionFor diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved context scope position expected type code) (fun receipt => receipt.diagnostics)
  coupled : Coupled factory invalidProjection missingDefault original.original.original.tree original.original.plan
namespace CoupledTokenExtractionFor
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource} {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {definitions : DataEnvironment} {administrative : Core.Context} {solved : List SolvedRequirement} {diagnosticPolicy : AssignmentDiagnosticPolicy}

variable {tracked : Bool} {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Syntax.ValueAssignOp → Word}
  {invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}
  {factory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy source invalidOperand}
def body
    {context scope mode statements expected type code}
    (syntaxTree : GenericLexicalStatements.Syntax source expressionSyntax context mode statements expected)
    (body : GenericLexicalStatements.Tree layouts owner active frame globals onError values source certificates context scope mode statements expected type code) :
    CoupledTokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary invalidProjection missingDefault expressionSyntax certificates definitions administrative solved
        context scope (.statements mode statements) expected type code := by
  exact ⟨⟨TokenExtractionFor.body (factory := factory) syntaxTree body, True.intro⟩, .body (syntaxTree := syntaxTree) (body := body)⟩

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
    (remaining : CoupledTokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary invalidProjection missingDefault expressionSyntax certificates definitions administrative solved
        nextContext ((binder.id, payload) :: scope) (.statements mode rest) expected type body) :
    CoupledTokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary invalidProjection missingDefault expressionSyntax certificates definitions administrative solved
        context scope (.statements mode (id :: rest)) expected type (.letE annotation.expression body) := by
  exact ⟨⟨TokenExtractionFor.uninitialized (factory := factory) found form monomorphic extended ordinary projected allocation annotation same remaining.original.original, remaining.original.prepared⟩, .uninitialized (found := found) (form := form) (monomorphic := monomorphic) (extended := extended) (ordinary := ordinary) (projected := projected) (allocation := allocation) (annotation := annotation) (same := same) (remaining := remaining.original.original.original.tree) remaining.coupled⟩

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
    (remaining : CoupledTokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary invalidProjection missingDefault expressionSyntax certificates definitions administrative solved nextContext ((binder.id, lowered.type) :: scope) (.statements mode rest) expected type body) :
    CoupledTokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary invalidProjection missingDefault expressionSyntax certificates definitions administrative solved
        context scope (.statements mode (id :: rest)) expected type (sequence type lowered.expression annotation.expression body) := by
  exact ⟨⟨TokenExtractionFor.initialized (factory := factory) found form monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining.original.original, remaining.original.prepared⟩, .initialized (found := found) (form := form) (monomorphic := monomorphic) (extended := extended) (ordinary := ordinary) (initializerFound := initializerFound) (sourceType := sourceType) (initial := initial) (allocation := allocation) (annotation := annotation) (same := same) (remaining := remaining.original.original.original.tree) remaining.coupled⟩

def discard
    {context scope mode id node expression expressionNode semicolon rest expected lowered type body}
    (found : source.lookupStatement? id = some node)
    (form : node.form = .expression expression semicolon)
    (notTail : (!semicolon && mode && rest.isEmpty) = false)
    (expressionFound : source.lookupExpression? expression = some expressionNode)
    (value : certificates context scope expression lowered)
    (remaining : CoupledTokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary invalidProjection missingDefault expressionSyntax certificates definitions administrative solved context scope (.statements mode rest) expected type body) :
    CoupledTokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary invalidProjection missingDefault expressionSyntax certificates definitions administrative solved context scope (.statements mode (id :: rest)) expected type
        (LocalSequence.discard (LocalLoop.controlType type) lowered.expression body) := by
  exact ⟨⟨TokenExtractionFor.discard (factory := factory) found form notTail expressionFound value remaining.original.original, remaining.original.prepared⟩, .discard (found := found) (form := form) (notTail := notTail) (expressionFound := expressionFound) (value := value) (remaining := remaining.original.original.original.tree) remaining.coupled⟩

def block
    {context scope mode id node statements rest expected type innerCode body}
    (found : source.lookupStatement? id = some node)
    (form : node.form = .block statements)
    (inner : CoupledTokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary invalidProjection missingDefault expressionSyntax certificates definitions administrative solved context scope (.statements false statements) expected type innerCode)
    (remaining : CoupledTokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary invalidProjection missingDefault expressionSyntax certificates definitions administrative solved context scope (.statements mode rest) expected type body) :
    CoupledTokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary invalidProjection missingDefault expressionSyntax certificates definitions administrative solved context scope (.statements mode (id :: rest)) expected type
        (LocalLoop.sequence type innerCode body) := by
  exact ⟨⟨TokenExtractionFor.block (factory := factory) found form inner.original.original remaining.original.original, ⟨inner.original.prepared, remaining.original.prepared⟩⟩, .block (found := found) (form := form) (inner := inner.original.original.original.tree) (remaining := remaining.original.original.original.tree) inner.coupled remaining.coupled⟩

def ifThen
    {context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body}
    (found : source.lookupStatement? id = some node)
    (form : node.form = .ifThen condition thenBody elseBody)
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionType : conditionNode.type = .bool)
    (conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩)
    (thenTree : CoupledTokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary invalidProjection missingDefault expressionSyntax certificates definitions administrative solved context scope (.statements false thenBody) expected type thenCode)
    (elseTree : CoupledTokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary invalidProjection missingDefault expressionSyntax certificates definitions administrative solved context scope (.statements false (elseBody.getD [])) expected type elseCode)
    (remaining : CoupledTokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary invalidProjection missingDefault expressionSyntax certificates definitions administrative solved context scope (.statements mode rest) expected type body) :
    CoupledTokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary invalidProjection missingDefault expressionSyntax certificates definitions administrative solved context scope (.statements mode (id :: rest)) expected type
        (LocalLoop.sequence type (LocalLoop.conditional type conditionCode thenCode elseCode) body) := by
  exact ⟨⟨TokenExtractionFor.ifThen (factory := factory) found form conditionFound conditionType conditionTree thenTree.original.original elseTree.original.original remaining.original.original, ⟨thenTree.original.prepared, elseTree.original.prepared, remaining.original.prepared⟩⟩, .ifThen (found := found) (form := form) (conditionFound := conditionFound) (conditionType := conditionType) (conditionTree := conditionTree) (thenTree := thenTree.original.original.original.tree) (elseTree := elseTree.original.original.original.tree) (remaining := remaining.original.original.original.tree) thenTree.coupled elseTree.coupled remaining.coupled⟩

def breaking
    {context scope mode id node rest expected type}
    (found : source.lookupStatement? id = some node)
    (form : node.form = .breakStmt) :
    CoupledTokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary invalidProjection missingDefault expressionSyntax certificates definitions administrative solved
        context scope (.statements mode (id :: rest)) expected type (LocalLoop.breaking type) := by
  exact ⟨⟨TokenExtractionFor.breaking (factory := factory) found form, True.intro⟩, .breaking (found := found) (form := form)⟩

def continuing
    {context scope mode id node rest expected type}
    (found : source.lookupStatement? id = some node)
    (form : node.form = .continueStmt) :
    CoupledTokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary invalidProjection missingDefault expressionSyntax certificates definitions administrative solved
        context scope (.statements mode (id :: rest)) expected type (LocalLoop.continuing type) := by
  exact ⟨⟨TokenExtractionFor.continuing (factory := factory) found form, True.intro⟩, .continuing (found := found) (form := form)⟩

def whileLoop
    {context scope mode id node condition conditionNode statements rest expected type conditionCode loopCode body selfReason}
    (found : source.lookupStatement? id = some node)
    (form : node.form = .whileLoop condition statements)
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionType : conditionNode.type = .bool)
    (conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩)
    (loopBody : CoupledTokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary invalidProjection missingDefault expressionSyntax certificates definitions administrative solved
        context scope (.statements false statements) expected type loopCode)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        (LocalLoop.whileLoop type conditionCode loopCode selfReason) (LocalLoop.resultType type) definitions)
    (remaining : CoupledTokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary invalidProjection missingDefault expressionSyntax certificates definitions administrative solved
        context scope (.statements mode rest) expected type body) :
    CoupledTokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary invalidProjection missingDefault expressionSyntax certificates definitions administrative solved
        context scope (.statements mode (id :: rest)) expected type
        (LocalLoop.sequence type (LocalLoop.whileLoop type conditionCode loopCode selfReason) body) := by
  exact ⟨⟨TokenExtractionFor.whileLoop (factory := factory) found form conditionFound conditionType conditionTree loopBody.original.original nativeTyped remaining.original.original, ⟨loopBody.original.prepared, remaining.original.prepared⟩⟩, .whileLoop (found := found) (form := form) (conditionFound := conditionFound) (conditionType := conditionType) (conditionTree := conditionTree) (loopBody := loopBody.original.original.original.tree) (nativeTyped := nativeTyped) (remaining := remaining.original.original.original.tree) loopBody.coupled remaining.coupled⟩

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
      SourceCoreRawMetadata.runtimeType assignment.target.type = .integer ∧ operator.wordOnly = false)
    (headFuel : Nat)
    (prepared : head.PreparedAt site headFuel (invalidProjection site assignment.target.root)
      (missingDefault site assignment.target.root))
    (remaining : CoupledTokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary invalidProjection missingDefault expressionSyntax certificates definitions administrative solved
        context scope (.statements mode rest) expected type body) :
    CoupledTokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary invalidProjection missingDefault expressionSyntax certificates definitions administrative solved
        context scope (.statements mode (id :: rest)) expected type (head.emit body (LocalLoop.controlType type)) := by
  exact ⟨⟨TokenExtractionFor.assign (factory := factory) found form head site origin same sourceTyped rightTyped profile remaining.original.original, ⟨remaining.original.prepared, headFuel, prepared⟩⟩, .assign (found := found) (form := form) (head := head) (remaining := remaining.original.original.original.tree) remaining.coupled site origin same sourceTyped rightTyped profile headFuel prepared⟩

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
    (remaining : CoupledTokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary invalidProjection missingDefault expressionSyntax certificates definitions administrative solved
        context scope (.statements mode rest) expected type body) :
    CoupledTokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary invalidProjection missingDefault expressionSyntax certificates definitions administrative solved
        context scope (.statements mode (id :: rest)) expected type (head.emit body (LocalLoop.controlType type)) := by
  exact ⟨⟨TokenExtractionFor.bitNot (factory := factory) found form head writable bare profile site origin same remaining.original.original, ⟨remaining.original.prepared, True.intro⟩⟩, .bitNot (found := found) (form := form) (head := head) (remaining := remaining.original.original.original.tree) remaining.coupled writable bare profile⟩

def forLoop
    {context scope mode id node initializer condition post statements rest expected type initialCode body}
    (found : source.lookupStatement? id = some node)
    (form : node.form = .forLoop initializer condition post statements)
    (initial : CoupledTokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary invalidProjection missingDefault expressionSyntax certificates definitions administrative solved context scope (.initializers initializer condition post statements) expected type initialCode)
    (remaining : CoupledTokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary invalidProjection missingDefault expressionSyntax certificates definitions administrative solved context scope (.statements mode rest) expected type body) :
    CoupledTokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary invalidProjection missingDefault expressionSyntax certificates definitions administrative solved context scope (.statements mode (id :: rest)) expected type (LocalLoop.sequence type initialCode body) := by
  exact ⟨⟨TokenExtractionFor.forLoop (factory := factory) found form initial.original.original remaining.original.original, ⟨initial.original.prepared, remaining.original.prepared⟩⟩, .forLoop (found := found) (form := form) (initial := initial.original.original.original.tree) (remaining := remaining.original.original.original.tree) initial.coupled remaining.coupled⟩

def initializersDone
    {context scope condition conditionNode post statements expected type conditionCode bodyCode postCode selfReason}
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionType : conditionNode.type = .bool)
    (conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩)
    (loopBody : CoupledTokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary invalidProjection missingDefault expressionSyntax certificates definitions administrative solved context scope (.statements false statements) expected type bodyCode)
    (postTree : GenericForHeader.CoupledTokenDiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary invalidProjection missingDefault certificates definitions administrative
        type (TypedForHeader.Fallthrough type) context scope post postCode)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        (LocalLoop.iterate type conditionCode bodyCode postCode selfReason) (LocalLoop.resultType type) definitions) :
    CoupledTokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary invalidProjection missingDefault expressionSyntax certificates definitions administrative solved context scope (.initializers [] condition post statements) expected type
        (LocalLoop.iterate type conditionCode bodyCode postCode selfReason) := by
  exact ⟨⟨TokenExtractionFor.initializersDone (factory := factory) conditionFound conditionType conditionTree loopBody.original.original postTree.original.original nativeTyped, ⟨loopBody.original.prepared, postTree.original.prepared⟩⟩, .initializersDone (conditionFound := conditionFound) (conditionType := conditionType) (conditionTree := conditionTree) (loopBody := loopBody.original.original.original.tree) (postTree := postTree.original.original.original.tree) (nativeTyped := nativeTyped) loopBody.coupled postTree.coupled⟩

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
    (remaining : CoupledTokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary invalidProjection missingDefault expressionSyntax certificates definitions administrative solved
        nextContext ((binder.id, payload) :: scope) (.initializers rest condition post statements) expected type body) :
    CoupledTokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary invalidProjection missingDefault expressionSyntax certificates definitions administrative solved
        context scope (.initializers (.letDecl binder none :: rest) condition post statements) expected type (.letE annotation.expression body) := by
  exact ⟨⟨TokenExtractionFor.initializerUninitialized (factory := factory) monomorphic extended ordinary projected allocation annotation same remaining.original.original, remaining.original.prepared⟩, .initializerUninitialized (monomorphic := monomorphic) (extended := extended) (ordinary := ordinary) (projected := projected) (allocation := allocation) (annotation := annotation) (same := same) (remaining := remaining.original.original.original.tree) remaining.coupled⟩

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
    (remaining : CoupledTokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary invalidProjection missingDefault expressionSyntax certificates definitions administrative solved
        nextContext ((binder.id, lowered.type) :: scope) (.initializers rest condition post statements) expected type body) :
    CoupledTokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary invalidProjection missingDefault expressionSyntax certificates definitions administrative solved
        context scope (.initializers (.letDecl binder (some initializer) :: rest) condition post statements) expected type (sequence type lowered.expression annotation.expression body) := by
  exact ⟨⟨TokenExtractionFor.initializerInitialized (factory := factory) monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining.original.original, remaining.original.prepared⟩, .initializerInitialized (monomorphic := monomorphic) (extended := extended) (ordinary := ordinary) (initializerFound := initializerFound) (sourceType := sourceType) (initial := initial) (allocation := allocation) (annotation := annotation) (same := same) (remaining := remaining.original.original.original.tree) remaining.coupled⟩

def initializerDiscard
    {context scope expression expressionNode rest lowered body condition post statements expected type}
    (found : source.lookupExpression? expression = some expressionNode)
    (value : certificates context scope expression lowered)
    (remaining : CoupledTokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary invalidProjection missingDefault expressionSyntax certificates definitions administrative solved
        context scope (.initializers rest condition post statements) expected type body) :
    CoupledTokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary invalidProjection missingDefault expressionSyntax certificates definitions administrative solved
        context scope (.initializers (.expression expression :: rest) condition post statements) expected type (LocalSequence.discard (LocalLoop.controlType type) lowered.expression body) := by
  exact ⟨⟨TokenExtractionFor.initializerDiscard (factory := factory) found value remaining.original.original, remaining.original.prepared⟩, .initializerDiscard (found := found) (value := value) (remaining := remaining.original.original.original.tree) remaining.coupled⟩

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
      SourceCoreRawMetadata.runtimeType assignment.target.type = .integer ∧ operator.wordOnly = false)
    (headFuel : Nat)
    (prepared : head.PreparedAt site headFuel (invalidProjection site assignment.target.root)
      (missingDefault site assignment.target.root))
    (remaining : CoupledTokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary invalidProjection missingDefault expressionSyntax certificates definitions administrative solved
        context scope (.initializers rest condition post statements) expected type body) :
    CoupledTokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary invalidProjection missingDefault expressionSyntax certificates definitions administrative solved
        context scope (.initializers (.assignValue assignment operator rhs :: rest) condition post statements) expected type (head.emit body (LocalLoop.controlType type)) := by
  exact ⟨⟨TokenExtractionFor.initializerAssign (factory := factory) head site origin same sourceTyped rightTyped profile remaining.original.original, ⟨remaining.original.prepared, headFuel, prepared⟩⟩, .initializerAssign (head := head) (remaining := remaining.original.original.original.tree) remaining.coupled site origin same sourceTyped rightTyped profile headFuel prepared⟩

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
    (remaining : CoupledTokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary invalidProjection missingDefault expressionSyntax certificates definitions administrative solved
        context scope (.initializers rest condition post statements) expected type body) :
    CoupledTokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary invalidProjection missingDefault expressionSyntax certificates definitions administrative solved
        context scope (.initializers (.assignBitNot assignment :: rest) condition post statements) expected type (head.emit body (LocalLoop.controlType type)) := by
  exact ⟨⟨TokenExtractionFor.initializerBitNot (factory := factory) head writable bare profile site origin same remaining.original.original, ⟨remaining.original.prepared, True.intro⟩⟩, .initializerBitNot (head := head) (remaining := remaining.original.original.original.tree) remaining.coupled writable bare profile⟩

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
        CoupledTokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary invalidProjection missingDefault expressionSyntax certificates definitions administrative solved
          childContext request.scope (.statements false request.statements) expected type request.code)
    (remaining : CoupledTokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary invalidProjection missingDefault expressionSyntax certificates definitions administrative solved
        context scope (.statements mode rest) expected type body)
    (sameLedger : compilation.solvedRequirements = solved) :
    CoupledTokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary invalidProjection missingDefault expressionSyntax certificates definitions administrative solved
        context scope (.statements mode (id :: rest)) expected type (LocalLoop.sequence type matched body) := by
  exact ⟨⟨TokenExtractionFor.matchWith (factory := factory) found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary (fun request member childContext related => (children request member childContext related).original.original) remaining.original.original sameLedger, ⟨(fun request member childContext related => (children request member childContext related).original.prepared), remaining.original.prepared⟩⟩, .matchWith (found := found) (form := form) (scrutineeFound := scrutineeFound) (scrutineeTyped := scrutineeTyped) (casesTyped := casesTyped) (defaultTyped := defaultTyped) (compilation := compilation) (sameValues := sameValues) (sameDefinitions := sameDefinitions) (allocator := allocator) (requests := requests) (receipt := receipt) (ordinary := ordinary) (children := fun request member childContext related => (children request member childContext related).original.original.original.tree) (remaining := remaining.original.original.original.tree) (fun request member childContext related => (children request member childContext related).coupled) remaining.coupled⟩

def terminalBlock {context scope mode id node statements rest expected type innerCode suffix}
    (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .block statements)
    (child : CoupledTokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary invalidProjection missingDefault expressionSyntax certificates definitions administrative solved context scope (.statements false statements) expected type innerCode)
    (stops : GenericLexicalStatements.Stopped source statements)
    (issued : GenericLexicalStatements.IssuedSuffix source scope mode rest type suffix) :
    CoupledTokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary invalidProjection missingDefault expressionSyntax certificates definitions administrative solved context scope (.statements mode (id :: rest)) expected type (LocalLoop.sequence type innerCode suffix) := by
  let original : TokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary expressionSyntax certificates definitions administrative solved context scope (.statements mode (id :: rest)) expected type (LocalLoop.sequence type innerCode suffix) := by
    refine ⟨⟨⟨.terminalBlock unique found form child.original.original.original.tree stops issued, child.original.original.original.diagnostics, ?_⟩, child.original.original.plan, child.original.original.equation⟩, child.original.original.tokens⟩
    intro registry faults provided
    obtain ⟨errors, ledgers⟩ := child.original.original.original.materialize registry faults provided
    exact ⟨.terminalBlock (unique := unique) (found := found) (form := form)
      (stops := stops) (issued := issued) errors,
      .terminalBlock (unique := unique) (found := found) (form := form)
      (stops := stops) (issued := issued) ledgers⟩
  exact ⟨⟨original, child.original.prepared⟩, .terminalBlock (unique := unique) (found := found) (form := form) (stops := stops) (issued := issued) child.coupled⟩

def terminalIf {context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode suffix}
    (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .ifThen condition thenBody (some elseBody))
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionType : conditionNode.type = .bool)
    (conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩)
    (left : CoupledTokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary invalidProjection missingDefault expressionSyntax certificates definitions administrative solved context scope (.statements false thenBody) expected type thenCode)
    (right : CoupledTokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary invalidProjection missingDefault expressionSyntax certificates definitions administrative solved context scope (.statements false elseBody) expected type elseCode)
    (thenStops : GenericLexicalStatements.Stopped source thenBody)
    (elseStops : GenericLexicalStatements.Stopped source elseBody)
    (issued : GenericLexicalStatements.IssuedSuffix source scope mode rest type suffix) :
    CoupledTokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary invalidProjection missingDefault expressionSyntax certificates definitions administrative solved context scope (.statements mode (id :: rest)) expected type
      (LocalLoop.sequence type (LocalLoop.conditional type conditionCode thenCode elseCode) suffix) := by
  let original : TokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary expressionSyntax certificates definitions administrative solved context scope (.statements mode (id :: rest)) expected type (LocalLoop.sequence type (LocalLoop.conditional type conditionCode thenCode elseCode) suffix) := by
    refine ⟨⟨⟨.terminalIf unique found form conditionFound conditionType conditionTree left.original.original.original.tree right.original.original.original.tree thenStops elseStops issued,
      (fun registry faults => left.original.original.original.diagnostics registry faults ∧ right.original.original.original.diagnostics registry faults), ?_⟩,
      .pair left.original.original.plan right.original.original.plan, by
        intro registry faults
        change (_ ∧ _) = (_ ∧ _)
        rw [left.original.original.equation registry faults, right.original.original.equation registry faults]⟩, .pair left.original.original.tokens right.original.original.tokens⟩
    intro registry faults provided
    obtain ⟨leftErrors, leftLedgers⟩ := left.original.original.original.materialize registry faults provided.1
    obtain ⟨rightErrors, rightLedgers⟩ := right.original.original.original.materialize registry faults provided.2
    exact ⟨.terminalIf (unique := unique) (found := found) (form := form)
      (conditionFound := conditionFound) (conditionType := conditionType) (conditionTree := conditionTree)
      (thenStops := thenStops) (elseStops := elseStops) (issued := issued) leftErrors rightErrors,
      .terminalIf (unique := unique) (found := found) (form := form)
      (conditionFound := conditionFound) (conditionType := conditionType) (conditionTree := conditionTree)
      (thenStops := thenStops) (elseStops := elseStops) (issued := issued) leftLedgers rightLedgers⟩
  exact ⟨⟨original, ⟨left.original.prepared, right.original.prepared⟩⟩, .terminalIf (unique := unique) (found := found) (form := form) (conditionFound := conditionFound) (conditionType := conditionType) (conditionTree := conditionTree) (thenStops := thenStops) (elseStops := elseStops) (issued := issued) left.coupled right.coupled⟩

def terminalMatch {context scope mode id node resolution scrutineeNode rest expected type matched suffix selfReason control caseFacts}
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
        CoupledTokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary invalidProjection missingDefault expressionSyntax certificates definitions administrative solved childContext request.scope (.statements false request.statements) expected type request.code)
    (stops : ReachableMatchContinuations.DefaultStopped source id resolution)
    (issued : GenericLexicalStatements.IssuedSuffix source scope mode rest type suffix)
    (sameLedger : compilation.solvedRequirements = solved) :
    CoupledTokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary invalidProjection missingDefault expressionSyntax certificates definitions administrative solved context scope (.statements mode (id :: rest)) expected type (LocalLoop.sequence type matched suffix) := by
  let original : TokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary expressionSyntax certificates definitions administrative solved context scope (.statements mode (id :: rest)) expected type (LocalLoop.sequence type matched suffix) := by
    refine ⟨⟨⟨.terminalMatch unique found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation
      sameValues sameDefinitions allocator requests receipt ordinary
      (fun request member childContext related => (children request member childContext related).original.original.original.tree) stops issued,
      (fun registry faults => ∀ request member childContext related,
        (children request member childContext related).original.original.original.diagnostics registry faults), ?_⟩,
      .selected requests context (resolution.hiddenScrutinee :: scope.map Prod.fst) scrutineeNode.type resolution.cases resolution.defaultBody
        (fun request member childContext related => (children request member childContext related).original.original.plan), by
        intro registry faults
        simp only [EmittedDiagnosticPlan.Plan.requirements, EmittedDiagnosticPlan.Produced.equation]⟩,
      .selected (fun request member childContext related => (children request member childContext related).original.original.tokens)⟩
    intro registry faults supplied
    let childErrors := fun request member childContext related =>
      ((children request member childContext related).original.original.original.materialize registry faults
        (supplied request member childContext related)).1
    let childLedgers := fun request member childContext related =>
      ((children request member childContext related).original.original.original.materialize registry faults
        (supplied request member childContext related)).2
    exact ⟨.terminalMatch (unique := unique) (found := found) (scrutineeFound := scrutineeFound)
        (scrutineeTyped := scrutineeTyped) (casesTyped := casesTyped) (defaultTyped := defaultTyped)
        (sameValues := sameValues) (allocator := allocator) (receipt := receipt) (ordinary := ordinary)
        (stops := stops) (issued := issued) form sameDefinitions childErrors,
      .terminalMatch (unique := unique) (found := found) (scrutineeFound := scrutineeFound)
        (scrutineeTyped := scrutineeTyped) (casesTyped := casesTyped) (defaultTyped := defaultTyped)
        (sameValues := sameValues) (allocator := allocator) (receipt := receipt) (ordinary := ordinary)
        (stops := stops) (issued := issued) form sameDefinitions sameLedger childLedgers⟩
  exact ⟨⟨original, (fun request member childContext related => (children request member childContext related).original.prepared)⟩, .terminalMatch (unique := unique) (found := found) (form := form) (scrutineeFound := scrutineeFound) (scrutineeTyped := scrutineeTyped) (casesTyped := casesTyped) (defaultTyped := defaultTyped) (compilation := compilation) (sameValues := sameValues) (sameDefinitions := sameDefinitions) (allocator := allocator) (requests := requests) (receipt := receipt) (ordinary := ordinary) (stops := stops) (issued := issued) (children := fun request member childContext related => (children request member childContext related).original.original.original.tree) (fun request member childContext related => (children request member childContext related).coupled)⟩

end CoupledTokenExtractionFor
end Solcore.SourceSemantics.CoreLowering.GenericImperativeMatch
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProjectedBitNotDiagnosticOrigins
/-! Projected unary sites reuse the actual unary occurrence grammar. Their
owning statement supplies the same place diagnostic inventory as compilation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProjectedBitNotDiagnosticOrigins
open Core Frontend SourceInference

abbrev Occurs := GenericAssignmentUnaryDiagnostics.UnaryOccurs
abbrev OccursFor := GenericAssignmentUnaryDiagnostics.UnaryOccursFor
abbrev HeaderOriginFor := AssignmentDiagnosticOrigins.HeaderOriginFor
abbrev ForOriginFor := AssignmentDiagnosticOrigins.ForOriginFor

/-- Statement and header sites retain the authentic parent and target. -/
theorem owning_target {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
    {assignment : AssignmentResolution} (origin : Occurs source site assignment) :
    ∃ node, .statement node ∈ source.nodes ∧ site = .occurrence node.id.occurrence ∧
      assignment ∈ CompatiblePlaceMissingPreparationCoverage.targets node := by
  cases origin with
  | statement found form =>
    refine ⟨_, (lookupStatement?_sound found).1, ?_, ?_⟩
    · exact (congrArg (fun id : StatementId => SourceCoreElaboration.ErrorSite.occurrence id.occurrence)
        (lookupStatement?_sound found).2).symm
    · simp only [CompatiblePlaceMissingPreparationCoverage.targets, form, List.mem_singleton]
  | header found form member =>
    refine ⟨_, (lookupStatement?_sound found).1, ?_, ?_⟩
    · exact (congrArg (fun id : StatementId => SourceCoreElaboration.ErrorSite.occurrence id.occurrence)
        (lookupStatement?_sound found).2).symm
    · rw [CompatiblePlaceMissingPreparationCoverage.targets, form]
      exact List.mem_filterMap.mpr ⟨_, member, rfl⟩

end Solcore.SourceSemantics.CoreLowering.ProjectedBitNotDiagnosticOrigins
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.PreparedProjectedDiagnosticFields
/-! Project a reached diagnostic packet at its actual prepared shape before
specializing the ambient definitions of the mixed caller. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.PreparedProjectedDiagnosticFields
open Core Frontend SourceInference GeneralHeap CompatiblePayload
open SourceCoreCompatibleDataPlaces ProtectedPlaceReachedDiagnostics
universe u v

theorem projected {values : SourceCoreCompatibleValues.Context} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions values.checked.catalog.definitions} {functions : FunctionModel values.checked.catalog ambient}
    {Records : Type v} {protocol : ProtectedStateTransition.Protocol.{u, v} Records}
    {source : TypedSource} {context : SourceSemantics.Context} {certificate : GenericExpressionMeaning.Certificate}
    {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context} {environment : Dynamic.Environment}
    {place : PlaceResolution} {prepared : Prepared} {operator : Syntax.ValueAssignOp} {invalid : Word}
    {initialIndex : ProtectedStateTransition.Index} {initial : protocol.State initialIndex} {faults : FunctionCalls.FaultRep}
    {codes : List SourceCoreBasic.LoweredExpr} {leaf : TypeSystem.Ty}
    {shape : GenericAssignmentStatements.Shape values source context certificate scope administrative
      ambient.definitions place prepared codes leaf}
    (errors : ShapeErrors values registry functions protocol source context certificate scope administrative environment
      place prepared operator invalid initial faults shape)
    (nonempty : place.projections ≠ []) :
    ∃ (sourceTypes : List TypeSystem.Ty) (site : SourceCoreElaboration.ErrorSite)
      (_layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) values source certificate
        scope site place prepared codes sourceTypes leaf administrative),
      ((∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none) ∧
      MissingFor values.checked registry functions protocol source site place prepared leaf initial faults ∧
      UninitializedFor values.checked registry functions protocol environment place prepared initial faults := by
  cases errors with
  | bare operands => exact (nonempty ‹place.projections = []›).elim
  | @projected _ _ sourceTypes site layout ordinary missing uninitialized =>
    exact ⟨sourceTypes, site, layout, ordinary, missing, uninitialized⟩

end Solcore.SourceSemantics.CoreLowering.PreparedProjectedDiagnosticFields
end
