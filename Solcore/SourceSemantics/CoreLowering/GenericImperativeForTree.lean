import Solcore.SourceSemantics.CoreLowering.GenericForHeaderPost
import Solcore.SourceSemantics.CoreLowering.GenericAssignmentStatementCertificates
import Solcore.SourceSemantics.CoreLowering.BuiltinLexicalStatements
import Solcore.SourceSemantics.CoreLowering.TypedImperativeForNative
import Solcore.SourceSemantics.CoreLowering.TypedImperativeForTree

/-! One static recursive grammar for lexical control, ordinary assignments and
while/for loops. Expression certificates share the lexical context; header and
body children are inductive fields, with no execution in the compiler receipt. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericImperativeFor
open Core Frontend SourceInference
abbrev Scope := SourceCoreLocalCell.Scope
abbrev ValuesContext := SourceCoreCompatibleValues.Context
abbrev Position := TypedImperativeFor.Position
abbrev absentRequest := TypedLexicalWhile.absentRequest
abbrev initializedRequest := TypedLexicalWhile.initializedRequest
abbrev sequence := TypedLexicalWhile.sequence

inductive Syntax (source : TypedSource) (expressionSyntax : ExpressionId → Prop) :
    SourceSemantics.Context → Position → TypeSystem.Ty → Prop where
  | body {context mode statements expected} (syntaxTree : GenericLexicalStatements.Syntax source expressionSyntax context mode statements expected) :
      Syntax source expressionSyntax context (.statements mode statements) expected
  | uninitialized {context nextContext mode id node binder rest expected}
      (found : source.lookupStatement? id = some node) (form : node.form = .letDecl binder none)
      (declaration : SourceCoreDataPlaces.rootBinder source binder.id = .ok binder)
      (monomorphic : binder.scheme.quantified = [])
      (extended : BinderExtends source.owner context binder nextContext)
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (remaining : Syntax source expressionSyntax nextContext (.statements mode rest) expected) :
      Syntax source expressionSyntax context (.statements mode (id :: rest)) expected

  | initialized {context nextContext mode id node binder initializer initializerNode rest expected}
      (found : source.lookupStatement? id = some node) (form : node.form = .letDecl binder (some initializer))
      (declaration : SourceCoreDataPlaces.rootBinder source binder.id = .ok binder)
      (monomorphic : binder.scheme.quantified = [])
      (extended : BinderExtends source.owner context binder nextContext)
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (initializerFound : source.lookupExpression? initializer = some initializerNode)
      (sourceType : initializerNode.type = binder.scheme.body)
      (initializerTyped : ExpressionHasType source context initializer initializerNode.type)
      (initializerSyntax : expressionSyntax initializer)
      (remaining : Syntax source expressionSyntax nextContext (.statements mode rest) expected) :
      Syntax source expressionSyntax context (.statements mode (id :: rest)) expected
  | discard {context mode id node expression expressionNode semicolon rest expected}
      (found : source.lookupStatement? id = some node) (form : node.form = .expression expression semicolon)
      (notTail : (!semicolon && mode && rest.isEmpty) = false)
      (sourceType : node.type = if semicolon then .unit else expressionNode.type)
      (expressionFound : source.lookupExpression? expression = some expressionNode)
      (typed : ExpressionHasType source context expression expressionNode.type)
      (value : expressionSyntax expression)
      (remaining : Syntax source expressionSyntax context (.statements mode rest) expected) : Syntax source expressionSyntax context (.statements mode (id :: rest)) expected
  | block {context mode id node statements rest expected}
      (found : source.lookupStatement? id = some node) (form : node.form = .block statements)
      (sourceType : node.type = .unit)
      (inner : Syntax source expressionSyntax context (.statements false statements) expected)
      (remaining : Syntax source expressionSyntax context (.statements mode rest) expected) : Syntax source expressionSyntax context (.statements mode (id :: rest)) expected
  | ifThen {context mode id node condition conditionNode thenBody elseBody rest expected}
      (found : source.lookupStatement? id = some node) (form : node.form = .ifThen condition thenBody elseBody)
      (sourceType : node.type = .unit)
      (conditionFound : source.lookupExpression? condition = some conditionNode)
      (conditionType : conditionNode.type = .bool)
      (typed : ExpressionHasType source context condition conditionNode.type)
      (conditionSyntax : expressionSyntax condition)
      (thenSyntax : Syntax source expressionSyntax context (.statements false thenBody) expected)
      (elseSyntax : Syntax source expressionSyntax context (.statements false (elseBody.getD [])) expected)
      (remaining : Syntax source expressionSyntax context (.statements mode rest) expected) : Syntax source expressionSyntax context (.statements mode (id :: rest)) expected

  | breaking {context mode id node rest expected}
      (found : source.lookupStatement? id = some node) (form : node.form = .breakStmt) :
      Syntax source expressionSyntax context (.statements mode (id :: rest)) expected
  | continuing {context mode id node rest expected}
      (found : source.lookupStatement? id = some node) (form : node.form = .continueStmt) :
      Syntax source expressionSyntax context (.statements mode (id :: rest)) expected
  | whileLoop {context mode id node condition conditionNode statements rest expected}
      (found : source.lookupStatement? id = some node) (form : node.form = .whileLoop condition statements)
      (conditionFound : source.lookupExpression? condition = some conditionNode)
      (conditionType : conditionNode.type = .bool)
      (typed : ExpressionHasType source context condition conditionNode.type)
      (conditionSyntax : expressionSyntax condition)
      (loopBody : Syntax source expressionSyntax context (.statements false statements) expected)
      (remaining : Syntax source expressionSyntax context (.statements mode rest) expected) : Syntax source expressionSyntax context (.statements mode (id :: rest)) expected

  | assign {context mode id node assignment operator rhs rest expected}
      (found : source.lookupStatement? id = some node) (form : node.form = .assignValue assignment operator rhs)
      (sourceTyped : ∀ binder, SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder →
        SourceProjectionsHaveType source context binder.scheme.body assignment.target.projections assignment.target.type)
      (writable : ∀ binder, SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder → WritableLocal context assignment.target.root binder.scheme.body)
      (rightTyped : ExpressionHasType source context rhs assignment.target.type)
      (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
        SourceCoreRawMetadata.runtimeType assignment.target.type = .integer)
      (children : ∀ id, id ∈ rhs :: DataPlaceKeyOrder.sourceKeys assignment.target.projections →
        expressionSyntax id ∧ ∃ node, source.lookupExpression? id = some node ∧ ExpressionHasType source context id node.type)
      (remaining : Syntax source expressionSyntax context (.statements mode rest) expected) : Syntax source expressionSyntax context (.statements mode (id :: rest)) expected


  | forLoop {context mode id node initializer condition post statements rest expected}
      (found : source.lookupStatement? id = some node) (form : node.form = .forLoop initializer condition post statements)
      (sourceType : node.type = .unit)
      (initial : Syntax source expressionSyntax context (.initializers initializer condition post statements) expected)
      (remaining : Syntax source expressionSyntax context (.statements mode rest) expected) : Syntax source expressionSyntax context (.statements mode (id :: rest)) expected
  | initializersDone {context condition conditionNode post statements expected}
      (conditionFound : source.lookupExpression? condition = some conditionNode)
      (conditionType : conditionNode.type = .bool)
      (typed : ExpressionHasType source context condition conditionNode.type)
      (conditionSyntax : expressionSyntax condition)
      (loopBody : Syntax source expressionSyntax context (.statements false statements) expected)
      (postSyntax : GenericForHeader.Syntax source expressionSyntax context post) :
      Syntax source expressionSyntax context (.initializers [] condition post statements) expected
  | initializerUninitialized {context nextContext binder rest condition post statements expected}
      (declaration : SourceCoreDataPlaces.rootBinder source binder.id = .ok binder)
      (monomorphic : binder.scheme.quantified = [])
      (extended : BinderExtends source.owner context binder nextContext)
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (remaining : Syntax source expressionSyntax nextContext (.initializers rest condition post statements) expected) : Syntax source expressionSyntax context (.initializers (.letDecl binder none :: rest) condition post statements) expected
  | initializerInitialized {context nextContext binder initializer initializerNode rest condition post statements expected}
      (declaration : SourceCoreDataPlaces.rootBinder source binder.id = .ok binder)
      (monomorphic : binder.scheme.quantified = [])
      (extended : BinderExtends source.owner context binder nextContext)
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (initializerFound : source.lookupExpression? initializer = some initializerNode)
      (sourceType : initializerNode.type = binder.scheme.body)
      (initializerTyped : ExpressionHasType source context initializer initializerNode.type)
      (initializerSyntax : expressionSyntax initializer)
      (remaining : Syntax source expressionSyntax nextContext (.initializers rest condition post statements) expected) : Syntax source expressionSyntax context (.initializers (.letDecl binder (some initializer) :: rest) condition post statements) expected
  | initializerDiscard {context expression expressionNode rest condition post statements expected}
      (found : source.lookupExpression? expression = some expressionNode)
      (typed : ExpressionHasType source context expression expressionNode.type)
      (syntaxTree : expressionSyntax expression)
      (remaining : Syntax source expressionSyntax context (.initializers rest condition post statements) expected) : Syntax source expressionSyntax context (.initializers (.expression expression :: rest) condition post statements) expected
  | initializerAssign {context assignment operator rhs rest condition post statements expected}
      (sourceTyped : ∀ binder, SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder →
        SourceProjectionsHaveType source context binder.scheme.body assignment.target.projections assignment.target.type)
      (writable : ∀ binder, SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder →
        WritableLocal context assignment.target.root binder.scheme.body)
      (rightTyped : ExpressionHasType source context rhs assignment.target.type)
      (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
        SourceCoreRawMetadata.runtimeType assignment.target.type = .integer)
      (children : ∀ id, id ∈ rhs :: DataPlaceKeyOrder.sourceKeys assignment.target.projections →
        expressionSyntax id ∧ ∃ node, source.lookupExpression? id = some node ∧ ExpressionHasType source context id node.type)
      (remaining : Syntax source expressionSyntax context (.initializers rest condition post statements) expected) : Syntax source expressionSyntax context (.initializers (.assignValue assignment operator rhs :: rest) condition post statements) expected
  | bitNot {context mode id node assignment rest expected}
      (found : source.lookupStatement? id = some node) (form : node.form = .assignBitNot assignment)
      (writable : ∀ binder, SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder →
        WritableLocal context assignment.target.root binder.scheme.body)
      (bare : assignment.target.projections = [])
      (profile : SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
        SourceCoreRawMetadata.runtimeType assignment.target.type = .integer)
      (remaining : Syntax source expressionSyntax context (.statements mode rest) expected) :
      Syntax source expressionSyntax context (.statements mode (id :: rest)) expected
  | initializerBitNot {context assignment rest condition post statements expected}
      (writable : ∀ binder, SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder →
        WritableLocal context assignment.target.root binder.scheme.body)
      (bare : assignment.target.projections = [])
      (profile : SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
        SourceCoreRawMetadata.runtimeType assignment.target.type = .integer)
      (remaining : Syntax source expressionSyntax context (.initializers rest condition post statements) expected) :
      Syntax source expressionSyntax context (.initializers (.assignBitNot assignment :: rest) condition post statements) expected

inductive Tree (layouts : SourceCoreAllocationLayouts.Prepared)
    (owner : SourceSpecialization.SpecializationKey) (active : TypeSystem.Substitution)
    (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (values : ValuesContext) (source : TypedSource)
    (expressionSyntax : ExpressionId → Prop)
    (certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate) (definitions : DataEnvironment) (administrative : Core.Context) :
    SourceSemantics.Context → Scope → Position → TypeSystem.Ty → Ty → Expr → Prop where
  | body {context scope mode statements expected type code}
      (syntaxTree : GenericLexicalStatements.Syntax source expressionSyntax context mode statements expected)
      (body : GenericLexicalStatements.Tree layouts owner active frame globals onError values source certificates context scope mode statements expected type code) :
      Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode statements) expected type code
  | uninitialized {context nextContext scope mode id node binder rest expected type body payload}
      (found : source.lookupStatement? id = some node) (form : node.form = .letDecl binder none)
      (monomorphic : binder.scheme.quantified = [])
      (extended : BinderExtends source.owner context binder nextContext)
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (projected : values.checked.catalog.project binder.scheme.body = .ok payload)
      (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (absentRequest source scope binder payload))
      (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
        (layouts.allocatorAt owner active onError) (absentRequest source scope binder payload))
      (same : annotation.original = allocation.expression)
      (remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        nextContext ((binder.id, payload) :: scope) (.statements mode rest) expected type body) :
      Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode (id :: rest)) expected type (.letE annotation.expression body)
  | initialized {context nextContext scope mode id node binder initializer initializerNode lowered body rest expected type}
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
      (remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative nextContext ((binder.id, lowered.type) :: scope) (.statements mode rest) expected type body) :
      Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode (id :: rest)) expected type (sequence type lowered.expression annotation.expression body)

  | discard {context scope mode id node expression expressionNode semicolon rest expected lowered type body}
      (found : source.lookupStatement? id = some node) (form : node.form = .expression expression semicolon)
      (notTail : (!semicolon && mode && rest.isEmpty) = false)
      (expressionFound : source.lookupExpression? expression = some expressionNode)
      (value : certificates context scope expression lowered)
      (remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode rest) expected type body) :
      Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode (id :: rest)) expected type
        (LocalSequence.discard (LocalLoop.controlType type) lowered.expression body)
  | block {context scope mode id node statements rest expected type innerCode body}
      (found : source.lookupStatement? id = some node) (form : node.form = .block statements)
      (inner : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements false statements) expected type innerCode)
      (remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode rest) expected type body) :
      Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode (id :: rest)) expected type
        (LocalLoop.sequence type innerCode body)
  | ifThen {context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body}
      (found : source.lookupStatement? id = some node) (form : node.form = .ifThen condition thenBody elseBody)
      (conditionFound : source.lookupExpression? condition = some conditionNode)
      (conditionType : conditionNode.type = .bool)
      (conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩)
      (thenTree : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements false thenBody) expected type thenCode)
      (elseTree : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements false (elseBody.getD [])) expected type elseCode)
      (remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode rest) expected type body) :
      Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode (id :: rest)) expected type
        (LocalLoop.sequence type (LocalLoop.conditional type conditionCode thenCode elseCode) body)

  | breaking {context scope mode id node rest expected type}
      (found : source.lookupStatement? id = some node) (form : node.form = .breakStmt) :
      Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode (id :: rest)) expected type (LocalLoop.breaking type)
  | continuing {context scope mode id node rest expected type}
      (found : source.lookupStatement? id = some node) (form : node.form = .continueStmt) :
      Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode (id :: rest)) expected type (LocalLoop.continuing type)
  | whileLoop {context scope mode id node condition conditionNode statements rest expected type conditionCode loopCode body selfReason}
      (found : source.lookupStatement? id = some node) (form : node.form = .whileLoop condition statements)
      (conditionFound : source.lookupExpression? condition = some conditionNode)
      (conditionType : conditionNode.type = .bool)
      (conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩)
      (loopBody : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements false statements) expected type loopCode)
      (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        (LocalLoop.whileLoop type conditionCode loopCode selfReason) (LocalLoop.resultType type) definitions)
      (remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode rest) expected type body) :
      Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode (id :: rest)) expected type
        (LocalLoop.sequence type (LocalLoop.whileLoop type conditionCode loopCode selfReason) body)

  | assign {context scope mode id node assignment operator rhs rest expected type body}
      (found : source.lookupStatement? id = some node) (form : node.form = .assignValue assignment operator rhs)
      (head : GenericAssignmentStatements.Head values source context (certificates context) scope administrative definitions assignment operator rhs)
      (remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode rest) expected type body) :
      Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode (id :: rest)) expected type (head.emit body (LocalLoop.controlType type))


  | bitNot {context scope mode id node assignment rest expected type body}
      (found : source.lookupStatement? id = some node) (form : node.form = .assignBitNot assignment)
      (head : CompatibleBitNotStatements.Head context scope assignment)
      (remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode rest) expected type body) :
      Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode (id :: rest)) expected type (head.emit body (LocalLoop.controlType type))


  | forLoop {context scope mode id node initializer condition post statements rest expected type initialCode body}
      (found : source.lookupStatement? id = some node) (form : node.form = .forLoop initializer condition post statements)
      (initial : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.initializers initializer condition post statements) expected type initialCode)
      (remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode rest) expected type body) :
      Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode (id :: rest)) expected type (LocalLoop.sequence type initialCode body)
  | initializersDone {context scope condition conditionNode post statements expected type conditionCode bodyCode postCode selfReason}
      (conditionFound : source.lookupExpression? condition = some conditionNode)
      (conditionType : conditionNode.type = .bool)
      (conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩)
      (loopBody : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements false statements) expected type bodyCode)
      (postTree : GenericForHeader.Tree layouts owner active frame globals onError values source certificates definitions administrative
        type (TypedForHeader.Fallthrough type) context scope post postCode)
      (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        (LocalLoop.iterate type conditionCode bodyCode postCode selfReason) (LocalLoop.resultType type) definitions) :
      Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.initializers [] condition post statements) expected type
        (LocalLoop.iterate type conditionCode bodyCode postCode selfReason)
  | initializerUninitialized {context nextContext scope binder rest body payload condition post statements expected type}
      (monomorphic : binder.scheme.quantified = [])
      (extended : BinderExtends source.owner context binder nextContext)
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (projected : values.checked.catalog.project binder.scheme.body = .ok payload)
      (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (absentRequest source scope binder payload))
      (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
        (layouts.allocatorAt owner active onError) (absentRequest source scope binder payload))
      (same : annotation.original = allocation.expression)
      (remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        nextContext ((binder.id, payload) :: scope) (.initializers rest condition post statements) expected type body) :
      Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.initializers (.letDecl binder none :: rest) condition post statements) expected type (.letE annotation.expression body)
  | initializerInitialized {context nextContext scope binder initializer initializerNode lowered body rest condition post statements expected type}
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
      (remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        nextContext ((binder.id, lowered.type) :: scope) (.initializers rest condition post statements) expected type body) :
      Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.initializers (.letDecl binder (some initializer) :: rest) condition post statements) expected type (sequence type lowered.expression annotation.expression body)
  | initializerDiscard {context scope expression expressionNode rest lowered body condition post statements expected type}
      (found : source.lookupExpression? expression = some expressionNode)
      (value : certificates context scope expression lowered)
      (remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.initializers rest condition post statements) expected type body) :
      Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.initializers (.expression expression :: rest) condition post statements) expected type (LocalSequence.discard (LocalLoop.controlType type) lowered.expression body)
  | initializerAssign {context scope assignment operator rhs rest body condition post statements expected type}
      (head : GenericAssignmentStatements.Head values source context (certificates context) scope administrative definitions assignment operator rhs)
      (remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.initializers rest condition post statements) expected type body) :
      Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.initializers (.assignValue assignment operator rhs :: rest) condition post statements) expected type (head.emit body (LocalLoop.controlType type))

  | initializerBitNot {context scope assignment rest body condition post statements expected type}
      (head : CompatibleBitNotStatements.Head context scope assignment)
      (remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.initializers rest condition post statements) expected type body) :
      Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.initializers (.assignBitNot assignment :: rest) condition post statements) expected type (head.emit body (LocalLoop.controlType type))

namespace Tree
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource}
  {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate} {definitions : DataEnvironment} {administrative : Core.Context}

inductive Errors (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) :
    {context : SourceSemantics.Context} → {scope : Scope} → {position : Position} →
    {expected : TypeSystem.Ty} → {type : Ty} → {code : Expr} →
    Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
      context scope position expected type code → Prop where
  | body {context scope mode statements expected type code}
      {syntaxTree : GenericLexicalStatements.Syntax source expressionSyntax context mode statements expected}
      {body : GenericLexicalStatements.Tree layouts owner active frame globals onError values source certificates context scope mode statements expected type code}
      : Errors registry faults (.body syntaxTree body)
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
      (remainingErrors : Errors registry faults remaining)
      : Errors registry faults (.uninitialized found form monomorphic extended ordinary projected allocation annotation same remaining)
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
      (remainingErrors : Errors registry faults remaining)
      : Errors registry faults (.initialized found form monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining)
  | discard {context scope mode id node expression expressionNode semicolon rest expected lowered type body}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .expression expression semicolon}
      {notTail : (!semicolon && mode && rest.isEmpty) = false}
      {expressionFound : source.lookupExpression? expression = some expressionNode}
      {value : certificates context scope expression lowered}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode rest) expected type body}
      (remainingErrors : Errors registry faults remaining)
      : Errors registry faults (.discard found form notTail expressionFound value remaining)
  | block {context scope mode id node statements rest expected type innerCode body}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .block statements}
      {inner : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements false statements) expected type innerCode}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode rest) expected type body}
      (innerErrors : Errors registry faults inner)
      (remainingErrors : Errors registry faults remaining)
      : Errors registry faults (.block found form inner remaining)
  | ifThen {context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .ifThen condition thenBody elseBody}
      {conditionFound : source.lookupExpression? condition = some conditionNode}
      {conditionType : conditionNode.type = .bool}
      {conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩}
      {thenTree : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements false thenBody) expected type thenCode}
      {elseTree : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements false (elseBody.getD [])) expected type elseCode}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode rest) expected type body}
      (thenTreeErrors : Errors registry faults thenTree)
      (elseTreeErrors : Errors registry faults elseTree)
      (remainingErrors : Errors registry faults remaining)
      : Errors registry faults (.ifThen found form conditionFound conditionType conditionTree thenTree elseTree remaining)
  | breaking {context scope mode id node rest expected type}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .breakStmt}
      : Errors registry faults (.breaking (context := context) (scope := scope) (mode := mode) (rest := rest) (expected := expected) (type := type) found form)
  | continuing {context scope mode id node rest expected type}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .continueStmt}
      : Errors registry faults (.continuing (context := context) (scope := scope) (mode := mode) (rest := rest) (expected := expected) (type := type) found form)
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
      (loopBodyErrors : Errors registry faults loopBody)
      (remainingErrors : Errors registry faults remaining)
      : Errors registry faults (.whileLoop found form conditionFound conditionType conditionTree loopBody nativeTyped remaining)
  | assign {context scope mode id node assignment operator rhs rest expected type body}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .assignValue assignment operator rhs}
      {head : GenericAssignmentStatements.Head values source context (certificates context) scope administrative definitions assignment operator rhs}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode rest) expected type body}
      (remainingErrors : Errors registry faults remaining)
      (headErrors : head.Errors registry faults)
      : Errors registry faults (.assign found form head remaining)

  | bitNot {context scope mode id node assignment rest expected type body}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .assignBitNot assignment}
      {head : CompatibleBitNotStatements.Head context scope assignment}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode rest) expected type body}
      (remainingErrors : Errors registry faults remaining)
      (headErrors : head.Errors faults)
      : Errors registry faults (.bitNot found form head remaining)

  | forLoop {context scope mode id node initializer condition post statements rest expected type initialCode body}
      {found : source.lookupStatement? id = some node} {form : node.form = .forLoop initializer condition post statements}
      {initial : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.initializers initializer condition post statements) expected type initialCode}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements mode rest) expected type body}
      (initialErrors : Errors registry faults initial) (remainingErrors : Errors registry faults remaining) :
      Errors registry faults (.forLoop found form initial remaining)
  | initializersDone {context scope condition conditionNode post statements expected type conditionCode bodyCode postCode selfReason}
      {conditionFound : source.lookupExpression? condition = some conditionNode}
      {conditionType : conditionNode.type = .bool}
      {conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩}
      {loopBody : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative context scope (.statements false statements) expected type bodyCode}
      {postTree : GenericForHeader.Tree layouts owner active frame globals onError values source certificates definitions administrative
        type (TypedForHeader.Fallthrough type) context scope post postCode}
      {nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        (LocalLoop.iterate type conditionCode bodyCode postCode selfReason) (LocalLoop.resultType type) definitions}
      (loopErrors : Errors registry faults loopBody) (postErrors : GenericForHeader.Tree.Errors registry faults postTree) :
      Errors registry faults (.initializersDone conditionFound conditionType conditionTree loopBody postTree nativeTyped)
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
      (remainingErrors : Errors registry faults remaining)
      : Errors registry faults (.initializerUninitialized monomorphic extended ordinary projected allocation annotation same remaining)
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
      (remainingErrors : Errors registry faults remaining)
      : Errors registry faults (.initializerInitialized monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining)
  | initializerDiscard {context scope expression expressionNode rest lowered body condition post statements expected type}
      {found : source.lookupExpression? expression = some expressionNode}
      {value : certificates context scope expression lowered}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.initializers rest condition post statements) expected type body}
      (remainingErrors : Errors registry faults remaining)
      : Errors registry faults (.initializerDiscard found value remaining)
  | initializerAssign {context scope assignment operator rhs rest body condition post statements expected type}
      {head : GenericAssignmentStatements.Head values source context (certificates context) scope administrative definitions assignment operator rhs}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.initializers rest condition post statements) expected type body}
      (remainingErrors : Errors registry faults remaining)
      (headErrors : head.Errors registry faults)
      : Errors registry faults (.initializerAssign head remaining)
  | initializerBitNot {context scope assignment rest body condition post statements expected type}
      {head : CompatibleBitNotStatements.Head context scope assignment}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.initializers rest condition post statements) expected type body}
      (remainingErrors : Errors registry faults remaining)
      (headErrors : head.Errors faults)
      : Errors registry faults (.initializerBitNot head remaining)
end Tree
end Solcore.SourceSemantics.CoreLowering.GenericImperativeFor
