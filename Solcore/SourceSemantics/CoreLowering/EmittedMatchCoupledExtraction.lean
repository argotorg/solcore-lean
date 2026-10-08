import Solcore.SourceSemantics.CoreLowering.EmittedMatchCoupling
import Solcore.SourceSemantics.CoreLowering.EmittedForHeaderCoupledExtraction
import Solcore.SourceSemantics.CoreLowering.EmittedDiagnosticTokenPlan
import Solcore.SourceSemantics.CoreLowering.EmittedForHeaderTokenExtraction

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
      SourceCoreRawMetadata.runtimeType assignment.target.type = .integer)
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
      SourceCoreRawMetadata.runtimeType assignment.target.type = .integer)
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
