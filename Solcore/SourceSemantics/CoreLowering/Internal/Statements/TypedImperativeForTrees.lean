import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.BitNotStatements
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.TypedForHeaders
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.RenamedBareAssignments
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.LoopRenaming
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.TypedImperativeFor
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.TypedImperative

/-!
# Typed imperative for loops: trees and meaning

Trees, certificates, control shape and meaning of `for` loops.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.TypedImperativeForTree
/-! One recursive grammar for ordinary assignments, lexical control and
while/for loops. Initializer vectors have a separate position index, so
induction reaches each concrete loop body and post without a semantic field. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.TypedImperativeFor
open Core Frontend SourceInference
abbrev Scope := SourceCoreLocalCell.Scope
abbrev ValuesContext := SourceCoreCompatibleValues.Context

inductive Position where
  | statements (mode : Bool) (statements : List StatementId)
  | initializers (items : List ForItemForm) (condition : ExpressionId)
      (post : List ForItemForm) (statements : List StatementId)

abbrev absentRequest (source : TypedSource) (scope : Scope) (binder : TypedBinder) (payload : Ty) :
    SourceCoreSourceCells.Request := ⟨source, scope, Renaming.id, binder, payload, none⟩

abbrev initializedRequest := CompatibleStatementInitialized.request
abbrev sequence := CompatibleStatementInitialized.sequence

inductive Syntax (source : TypedSource) :
    SourceSemantics.Context → Position → TypeSystem.Ty → Prop where
  | body {context mode statements expected} (syntaxTree : TypedLexicalControl.Syntax source context mode statements expected) :
      Syntax source context (.statements mode statements) expected
  | uninitialized {context nextContext mode id node binder rest expected}
      (found : source.lookupStatement? id = some node) (form : node.form = .letDecl binder none)
      (declaration : SourceCoreDataPlaces.rootBinder source binder.id = .ok binder)
      (monomorphic : binder.scheme.quantified = [])
      (extended : BinderExtends source.owner context binder nextContext)
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (remaining : Syntax source nextContext (.statements mode rest) expected) :
      Syntax source context (.statements mode (id :: rest)) expected

  | initialized {context nextContext mode id node binder initializer initializerNode rest expected}
      (found : source.lookupStatement? id = some node) (form : node.form = .letDecl binder (some initializer))
      (declaration : SourceCoreDataPlaces.rootBinder source binder.id = .ok binder)
      (monomorphic : binder.scheme.quantified = [])
      (extended : BinderExtends source.owner context binder nextContext)
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (initializerFound : source.lookupExpression? initializer = some initializerNode)
      (sourceType : initializerNode.type = binder.scheme.body)
      (initializerTyped : ExpressionHasType source context initializer initializerNode.type)
      (initializerSyntax : CompatibleExpressionTyped.Syntax source initializer)
      (remaining : Syntax source nextContext (.statements mode rest) expected) :
      Syntax source context (.statements mode (id :: rest)) expected
  | discard {context mode id node expression expressionNode semicolon rest expected}
      (found : source.lookupStatement? id = some node) (form : node.form = .expression expression semicolon)
      (notTail : (!semicolon && mode && rest.isEmpty) = false)
      (sourceType : node.type = if semicolon then .unit else expressionNode.type)
      (expressionFound : source.lookupExpression? expression = some expressionNode)
      (typed : ExpressionHasType source context expression expressionNode.type)
      (value : CompatibleExpressionTyped.Syntax source expression)
      (remaining : Syntax source context (.statements mode rest) expected) : Syntax source context (.statements mode (id :: rest)) expected
  | block {context mode id node statements rest expected}
      (found : source.lookupStatement? id = some node) (form : node.form = .block statements)
      (sourceType : node.type = .unit)
      (inner : Syntax source context (.statements false statements) expected)
      (remaining : Syntax source context (.statements mode rest) expected) : Syntax source context (.statements mode (id :: rest)) expected
  | ifThen {context mode id node condition conditionNode thenBody elseBody rest expected}
      (found : source.lookupStatement? id = some node) (form : node.form = .ifThen condition thenBody elseBody)
      (sourceType : node.type = .unit)
      (conditionFound : source.lookupExpression? condition = some conditionNode)
      (conditionType : conditionNode.type = .bool)
      (typed : ExpressionHasType source context condition conditionNode.type)
      (conditionSyntax : CompatibleExpressionTyped.Syntax source condition)
      (thenSyntax : Syntax source context (.statements false thenBody) expected)
      (elseSyntax : Syntax source context (.statements false (elseBody.getD [])) expected)
      (remaining : Syntax source context (.statements mode rest) expected) : Syntax source context (.statements mode (id :: rest)) expected

  | breaking {context mode id node rest expected}
      (found : source.lookupStatement? id = some node) (form : node.form = .breakStmt) :
      Syntax source context (.statements mode (id :: rest)) expected
  | continuing {context mode id node rest expected}
      (found : source.lookupStatement? id = some node) (form : node.form = .continueStmt) :
      Syntax source context (.statements mode (id :: rest)) expected
  | whileLoop {context mode id node condition conditionNode statements rest expected}
      (found : source.lookupStatement? id = some node) (form : node.form = .whileLoop condition statements)
      (conditionFound : source.lookupExpression? condition = some conditionNode)
      (conditionType : conditionNode.type = .bool)
      (typed : ExpressionHasType source context condition conditionNode.type)
      (conditionSyntax : CompatibleExpressionTyped.Syntax source condition)
      (loopBody : Syntax source context (.statements false statements) expected)
      (remaining : Syntax source context (.statements mode rest) expected) : Syntax source context (.statements mode (id :: rest)) expected

  | assign {context mode id node assignment operator rhs rest expected}
      (found : source.lookupStatement? id = some node) (form : node.form = .assignValue assignment operator rhs)
      (sourceTyped : ∀ binder, SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder →
        SourceProjectionsHaveType source context binder.scheme.body assignment.target.projections assignment.target.type)
      (writable : ∀ binder, SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder → WritableLocal context assignment.target.root binder.scheme.body)
      (rightTyped : ExpressionHasType source context rhs assignment.target.type)
      (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
        SourceCoreRawMetadata.runtimeType assignment.target.type = .integer ∧ operator.wordOnly = false)
      (remaining : Syntax source context (.statements mode rest) expected) : Syntax source context (.statements mode (id :: rest)) expected


  | forLoop {context mode id node initializer condition post statements rest expected}
      (found : source.lookupStatement? id = some node) (form : node.form = .forLoop initializer condition post statements)
      (sourceType : node.type = .unit)
      (initial : Syntax source context (.initializers initializer condition post statements) expected)
      (remaining : Syntax source context (.statements mode rest) expected) : Syntax source context (.statements mode (id :: rest)) expected
  | initializersDone {context condition conditionNode post statements expected}
      (conditionFound : source.lookupExpression? condition = some conditionNode)
      (conditionType : conditionNode.type = .bool)
      (typed : ExpressionHasType source context condition conditionNode.type)
      (conditionSyntax : CompatibleExpressionTyped.Syntax source condition)
      (loopBody : Syntax source context (.statements false statements) expected)
      (postSyntax : TypedForHeader.Syntax source context post) :
      Syntax source context (.initializers [] condition post statements) expected
  | initializerUninitialized {context nextContext binder rest condition post statements expected}
      (declaration : SourceCoreDataPlaces.rootBinder source binder.id = .ok binder)
      (monomorphic : binder.scheme.quantified = [])
      (extended : BinderExtends source.owner context binder nextContext)
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (remaining : Syntax source nextContext (.initializers rest condition post statements) expected) : Syntax source context (.initializers (.letDecl binder none :: rest) condition post statements) expected
  | initializerInitialized {context nextContext binder initializer initializerNode rest condition post statements expected}
      (declaration : SourceCoreDataPlaces.rootBinder source binder.id = .ok binder)
      (monomorphic : binder.scheme.quantified = [])
      (extended : BinderExtends source.owner context binder nextContext)
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (initializerFound : source.lookupExpression? initializer = some initializerNode)
      (sourceType : initializerNode.type = binder.scheme.body)
      (initializerTyped : ExpressionHasType source context initializer initializerNode.type)
      (initializerSyntax : CompatibleExpressionTyped.Syntax source initializer)
      (remaining : Syntax source nextContext (.initializers rest condition post statements) expected) : Syntax source context (.initializers (.letDecl binder (some initializer) :: rest) condition post statements) expected
  | initializerDiscard {context expression expressionNode rest condition post statements expected}
      (found : source.lookupExpression? expression = some expressionNode)
      (typed : ExpressionHasType source context expression expressionNode.type)
      (syntaxTree : CompatibleExpressionTyped.Syntax source expression)
      (remaining : Syntax source context (.initializers rest condition post statements) expected) : Syntax source context (.initializers (.expression expression :: rest) condition post statements) expected
  | initializerAssign {context assignment operator rhs rest condition post statements expected}
      (sourceTyped : ∀ binder, SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder →
        SourceProjectionsHaveType source context binder.scheme.body assignment.target.projections assignment.target.type)
      (writable : ∀ binder, SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder →
        WritableLocal context assignment.target.root binder.scheme.body)
      (rightTyped : ExpressionHasType source context rhs assignment.target.type)
      (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
        SourceCoreRawMetadata.runtimeType assignment.target.type = .integer ∧ operator.wordOnly = false)
      (remaining : Syntax source context (.initializers rest condition post statements) expected) : Syntax source context (.initializers (.assignValue assignment operator rhs :: rest) condition post statements) expected

inductive Tree (layouts : SourceCoreAllocationLayouts.Prepared)
    (owner : SourceSpecialization.SpecializationKey) (active : TypeSystem.Substitution)
    (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (readFuel : Nat) (values : ValuesContext) (source : TypedSource)
    (solved : List SolvedRequirement)
    (reasonAt : ExpressionId → Word) (definitions : DataEnvironment) (administrative : Core.Context) :
    SourceSemantics.Context → Scope → Position → TypeSystem.Ty → Ty → Expr → Prop where
  | body {context scope mode statements expected type code}
      (syntaxTree : TypedLexicalControl.Syntax source context mode statements expected)
      (body : TypedLexicalControl.Tree layouts owner active frame globals onError readFuel values source solved reasonAt context scope mode statements expected type code) :
      Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative
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
      (remaining : Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative
        nextContext ((binder.id, payload) :: scope) (.statements mode rest) expected type body) :
      Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative
        context scope (.statements mode (id :: rest)) expected type (.letE annotation.expression body)
  | initialized {context nextContext scope mode id node binder initializer initializerNode lowered body rest expected type}
      (found : source.lookupStatement? id = some node) (form : node.form = .letDecl binder (some initializer))
      (monomorphic : binder.scheme.quantified = [])
      (extended : BinderExtends source.owner context binder nextContext)
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (initializerFound : source.lookupExpression? initializer = some initializerNode)
      (sourceType : initializerNode.type = binder.scheme.body)
      (initial : CompatibleExpressionTyped.Tree readFuel values source context solved reasonAt scope initializer lowered)
      (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (initializedRequest source scope binder lowered.type))
      (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
        (layouts.allocatorAt owner active onError) (initializedRequest source scope binder lowered.type))
      (same : annotation.original = allocation.expression)
      (remaining : Tree layouts owner active frame globals onError readFuel values source
        solved reasonAt definitions administrative nextContext ((binder.id, lowered.type) :: scope) (.statements mode rest) expected type body) :
      Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative
        context scope (.statements mode (id :: rest)) expected type (sequence type lowered.expression annotation.expression body)

  | discard {context scope mode id node expression expressionNode semicolon rest expected lowered type body}
      (found : source.lookupStatement? id = some node) (form : node.form = .expression expression semicolon)
      (notTail : (!semicolon && mode && rest.isEmpty) = false)
      (expressionFound : source.lookupExpression? expression = some expressionNode)
      (value : CompatibleExpressionTyped.Tree readFuel values source context solved reasonAt scope expression lowered)
      (remaining : Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative context scope (.statements mode rest) expected type body) :
      Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative context scope (.statements mode (id :: rest)) expected type
        (LocalSequence.discard (LocalLoop.controlType type) lowered.expression body)
  | block {context scope mode id node statements rest expected type innerCode body}
      (found : source.lookupStatement? id = some node) (form : node.form = .block statements)
      (inner : Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative context scope (.statements false statements) expected type innerCode)
      (remaining : Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative context scope (.statements mode rest) expected type body) :
      Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative context scope (.statements mode (id :: rest)) expected type
        (LocalLoop.sequence type innerCode body)
  | ifThen {context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body}
      (found : source.lookupStatement? id = some node) (form : node.form = .ifThen condition thenBody elseBody)
      (conditionFound : source.lookupExpression? condition = some conditionNode)
      (conditionType : conditionNode.type = .bool)
      (conditionTree : CompatibleExpressionTyped.Tree readFuel values source context solved reasonAt scope condition ⟨.bool, conditionCode⟩)
      (thenTree : Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative context scope (.statements false thenBody) expected type thenCode)
      (elseTree : Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative context scope (.statements false (elseBody.getD [])) expected type elseCode)
      (remaining : Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative context scope (.statements mode rest) expected type body) :
      Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative context scope (.statements mode (id :: rest)) expected type
        (LocalLoop.sequence type (LocalLoop.conditional type conditionCode thenCode elseCode) body)

  | breaking {context scope mode id node rest expected type}
      (found : source.lookupStatement? id = some node) (form : node.form = .breakStmt) :
      Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative
        context scope (.statements mode (id :: rest)) expected type (LocalLoop.breaking type)
  | continuing {context scope mode id node rest expected type}
      (found : source.lookupStatement? id = some node) (form : node.form = .continueStmt) :
      Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative
        context scope (.statements mode (id :: rest)) expected type (LocalLoop.continuing type)
  | whileLoop {context scope mode id node condition conditionNode statements rest expected type conditionCode loopCode body selfReason}
      (found : source.lookupStatement? id = some node) (form : node.form = .whileLoop condition statements)
      (conditionFound : source.lookupExpression? condition = some conditionNode)
      (conditionType : conditionNode.type = .bool)
      (conditionTree : CompatibleExpressionTyped.Tree readFuel values source context solved reasonAt scope condition ⟨.bool, conditionCode⟩)
      (loopBody : Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative
        context scope (.statements false statements) expected type loopCode)
      (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        (LocalLoop.whileLoop type conditionCode loopCode selfReason) (LocalLoop.resultType type) definitions)
      (remaining : Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative
        context scope (.statements mode rest) expected type body) :
      Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative
        context scope (.statements mode (id :: rest)) expected type
        (LocalLoop.sequence type (LocalLoop.whileLoop type conditionCode loopCode selfReason) body)

  | assign {context scope mode id node assignment operator rhs rest expected type body}
      (found : source.lookupStatement? id = some node) (form : node.form = .assignValue assignment operator rhs)
      (head : CompatibleAssignmentStatements.Head readFuel values source context solved reasonAt scope administrative definitions assignment operator rhs)
      (remaining : Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative
        context scope (.statements mode rest) expected type body) :
      Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative
        context scope (.statements mode (id :: rest)) expected type (head.emit body (LocalLoop.controlType type))


  | bitNot {context scope mode id node assignment rest expected type body}
      (found : source.lookupStatement? id = some node) (form : node.form = .assignBitNot assignment)
      (head : CompatibleBitNotStatements.Head context scope assignment)
      (remaining : Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative
        context scope (.statements mode rest) expected type body) :
      Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative
        context scope (.statements mode (id :: rest)) expected type (head.emit body (LocalLoop.controlType type))


  | forLoop {context scope mode id node initializer condition post statements rest expected type initialCode body}
      (found : source.lookupStatement? id = some node) (form : node.form = .forLoop initializer condition post statements)
      (initial : Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative context scope (.initializers initializer condition post statements) expected type initialCode)
      (remaining : Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative context scope (.statements mode rest) expected type body) :
      Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative context scope (.statements mode (id :: rest)) expected type (LocalLoop.sequence type initialCode body)
  | initializersDone {context scope condition conditionNode post statements expected type conditionCode bodyCode postCode selfReason}
      (conditionFound : source.lookupExpression? condition = some conditionNode)
      (conditionType : conditionNode.type = .bool)
      (conditionTree : CompatibleExpressionTyped.Tree readFuel values source context solved reasonAt scope condition ⟨.bool, conditionCode⟩)
      (loopBody : Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative context scope (.statements false statements) expected type bodyCode)
      (postTree : TypedForHeader.Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative
        type (TypedForHeader.Fallthrough type) context scope post postCode)
      (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        (LocalLoop.iterate type conditionCode bodyCode postCode selfReason) (LocalLoop.resultType type) definitions) :
      Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative context scope (.initializers [] condition post statements) expected type
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
      (remaining : Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative
        nextContext ((binder.id, payload) :: scope) (.initializers rest condition post statements) expected type body) :
      Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative
        context scope (.initializers (.letDecl binder none :: rest) condition post statements) expected type (.letE annotation.expression body)
  | initializerInitialized {context nextContext scope binder initializer initializerNode lowered body rest condition post statements expected type}
      (monomorphic : binder.scheme.quantified = [])
      (extended : BinderExtends source.owner context binder nextContext)
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (initializerFound : source.lookupExpression? initializer = some initializerNode)
      (sourceType : initializerNode.type = binder.scheme.body)
      (initial : CompatibleExpressionTyped.Tree readFuel values source context solved reasonAt scope initializer lowered)
      (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (initializedRequest source scope binder lowered.type))
      (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
        (layouts.allocatorAt owner active onError) (initializedRequest source scope binder lowered.type))
      (same : annotation.original = allocation.expression)
      (remaining : Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative
        nextContext ((binder.id, lowered.type) :: scope) (.initializers rest condition post statements) expected type body) :
      Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative
        context scope (.initializers (.letDecl binder (some initializer) :: rest) condition post statements) expected type (sequence type lowered.expression annotation.expression body)
  | initializerDiscard {context scope expression expressionNode rest lowered body condition post statements expected type}
      (found : source.lookupExpression? expression = some expressionNode)
      (value : CompatibleExpressionTyped.Tree readFuel values source context solved reasonAt scope expression lowered)
      (remaining : Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative
        context scope (.initializers rest condition post statements) expected type body) :
      Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative
        context scope (.initializers (.expression expression :: rest) condition post statements) expected type (LocalSequence.discard (LocalLoop.controlType type) lowered.expression body)
  | initializerAssign {context scope assignment operator rhs rest body condition post statements expected type}
      (head : CompatibleAssignmentStatements.Head readFuel values source context solved reasonAt scope administrative definitions assignment operator rhs)
      (remaining : Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative
        context scope (.initializers rest condition post statements) expected type body) :
      Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative
        context scope (.initializers (.assignValue assignment operator rhs :: rest) condition post statements) expected type (head.emit body (LocalLoop.controlType type))

  | initializerBitNot {context scope assignment rest body condition post statements expected type}
      (head : CompatibleBitNotStatements.Head context scope assignment)
      (remaining : Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative
        context scope (.initializers rest condition post statements) expected type body) :
      Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative
        context scope (.initializers (.assignBitNot assignment :: rest) condition post statements) expected type (head.emit body (LocalLoop.controlType type))

namespace Tree
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {readFuel : Nat} {values : ValuesContext} {source : TypedSource} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {definitions : DataEnvironment} {administrative : Core.Context}

inductive Errors (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) :
    {context : SourceSemantics.Context} → {scope : Scope} → {position : Position} →
    {expected : TypeSystem.Ty} → {type : Ty} → {code : Expr} →
    Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative
      context scope position expected type code → Prop where
  | body {context scope mode statements expected type code}
      {syntaxTree : TypedLexicalControl.Syntax source context mode statements expected}
      {body : TypedLexicalControl.Tree layouts owner active frame globals onError readFuel values source solved reasonAt context scope mode statements expected type code}
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
      {remaining : Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative
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
      {initial : CompatibleExpressionTyped.Tree readFuel values source context solved reasonAt scope initializer lowered}
      {allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (initializedRequest source scope binder lowered.type)}
      {annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
        (layouts.allocatorAt owner active onError) (initializedRequest source scope binder lowered.type)}
      {same : annotation.original = allocation.expression}
      {remaining : Tree layouts owner active frame globals onError readFuel values source
        solved reasonAt definitions administrative nextContext ((binder.id, lowered.type) :: scope) (.statements mode rest) expected type body}
      (remainingErrors : Errors registry faults remaining)
      : Errors registry faults (.initialized found form monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining)
  | discard {context scope mode id node expression expressionNode semicolon rest expected lowered type body}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .expression expression semicolon}
      {notTail : (!semicolon && mode && rest.isEmpty) = false}
      {expressionFound : source.lookupExpression? expression = some expressionNode}
      {value : CompatibleExpressionTyped.Tree readFuel values source context solved reasonAt scope expression lowered}
      {remaining : Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative context scope (.statements mode rest) expected type body}
      (remainingErrors : Errors registry faults remaining)
      : Errors registry faults (.discard found form notTail expressionFound value remaining)
  | block {context scope mode id node statements rest expected type innerCode body}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .block statements}
      {inner : Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative context scope (.statements false statements) expected type innerCode}
      {remaining : Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative context scope (.statements mode rest) expected type body}
      (innerErrors : Errors registry faults inner)
      (remainingErrors : Errors registry faults remaining)
      : Errors registry faults (.block found form inner remaining)
  | ifThen {context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .ifThen condition thenBody elseBody}
      {conditionFound : source.lookupExpression? condition = some conditionNode}
      {conditionType : conditionNode.type = .bool}
      {conditionTree : CompatibleExpressionTyped.Tree readFuel values source context solved reasonAt scope condition ⟨.bool, conditionCode⟩}
      {thenTree : Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative context scope (.statements false thenBody) expected type thenCode}
      {elseTree : Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative context scope (.statements false (elseBody.getD [])) expected type elseCode}
      {remaining : Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative context scope (.statements mode rest) expected type body}
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
      {conditionTree : CompatibleExpressionTyped.Tree readFuel values source context solved reasonAt scope condition ⟨.bool, conditionCode⟩}
      {loopBody : Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative
        context scope (.statements false statements) expected type loopCode}
      {nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        (LocalLoop.whileLoop type conditionCode loopCode selfReason) (LocalLoop.resultType type) definitions}
      {remaining : Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative
        context scope (.statements mode rest) expected type body}
      (loopBodyErrors : Errors registry faults loopBody)
      (remainingErrors : Errors registry faults remaining)
      : Errors registry faults (.whileLoop found form conditionFound conditionType conditionTree loopBody nativeTyped remaining)
  | assign {context scope mode id node assignment operator rhs rest expected type body}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .assignValue assignment operator rhs}
      {head : CompatibleAssignmentStatements.Head readFuel values source context solved reasonAt scope administrative definitions assignment operator rhs}
      {remaining : Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative
        context scope (.statements mode rest) expected type body}
      (remainingErrors : Errors registry faults remaining)
      (headErrors : head.Errors registry faults)
      : Errors registry faults (.assign found form head remaining)

  | bitNot {context scope mode id node assignment rest expected type body}
      {found : source.lookupStatement? id = some node}
      {form : node.form = .assignBitNot assignment}
      {head : CompatibleBitNotStatements.Head context scope assignment}
      {remaining : Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative
        context scope (.statements mode rest) expected type body}
      (remainingErrors : Errors registry faults remaining)
      (headErrors : head.Errors faults)
      : Errors registry faults (.bitNot found form head remaining)

  | forLoop {context scope mode id node initializer condition post statements rest expected type initialCode body}
      {found : source.lookupStatement? id = some node} {form : node.form = .forLoop initializer condition post statements}
      {initial : Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative context scope (.initializers initializer condition post statements) expected type initialCode}
      {remaining : Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative context scope (.statements mode rest) expected type body}
      (initialErrors : Errors registry faults initial) (remainingErrors : Errors registry faults remaining) :
      Errors registry faults (.forLoop found form initial remaining)
  | initializersDone {context scope condition conditionNode post statements expected type conditionCode bodyCode postCode selfReason}
      {conditionFound : source.lookupExpression? condition = some conditionNode}
      {conditionType : conditionNode.type = .bool}
      {conditionTree : CompatibleExpressionTyped.Tree readFuel values source context solved reasonAt scope condition ⟨.bool, conditionCode⟩}
      {loopBody : Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative context scope (.statements false statements) expected type bodyCode}
      {postTree : TypedForHeader.Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative
        type (TypedForHeader.Fallthrough type) context scope post postCode}
      {nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        (LocalLoop.iterate type conditionCode bodyCode postCode selfReason) (LocalLoop.resultType type) definitions}
      (loopErrors : Errors registry faults loopBody) (postErrors : TypedForHeader.Tree.Errors registry faults postTree) :
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
      {remaining : Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative
        nextContext ((binder.id, payload) :: scope) (.initializers rest condition post statements) expected type body}
      (remainingErrors : Errors registry faults remaining)
      : Errors registry faults (.initializerUninitialized monomorphic extended ordinary projected allocation annotation same remaining)
  | initializerInitialized {context nextContext scope binder initializer initializerNode lowered body rest condition post statements expected type}
      {monomorphic : binder.scheme.quantified = []}
      {extended : BinderExtends source.owner context binder nextContext}
      {ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false}
      {initializerFound : source.lookupExpression? initializer = some initializerNode}
      {sourceType : initializerNode.type = binder.scheme.body}
      {initial : CompatibleExpressionTyped.Tree readFuel values source context solved reasonAt scope initializer lowered}
      {allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (initializedRequest source scope binder lowered.type)}
      {annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
        (layouts.allocatorAt owner active onError) (initializedRequest source scope binder lowered.type)}
      {same : annotation.original = allocation.expression}
      {remaining : Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative
        nextContext ((binder.id, lowered.type) :: scope) (.initializers rest condition post statements) expected type body}
      (remainingErrors : Errors registry faults remaining)
      : Errors registry faults (.initializerInitialized monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining)
  | initializerDiscard {context scope expression expressionNode rest lowered body condition post statements expected type}
      {found : source.lookupExpression? expression = some expressionNode}
      {value : CompatibleExpressionTyped.Tree readFuel values source context solved reasonAt scope expression lowered}
      {remaining : Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative
        context scope (.initializers rest condition post statements) expected type body}
      (remainingErrors : Errors registry faults remaining)
      : Errors registry faults (.initializerDiscard found value remaining)
  | initializerAssign {context scope assignment operator rhs rest body condition post statements expected type}
      {head : CompatibleAssignmentStatements.Head readFuel values source context solved reasonAt scope administrative definitions assignment operator rhs}
      {remaining : Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative
        context scope (.initializers rest condition post statements) expected type body}
      (remainingErrors : Errors registry faults remaining)
      (headErrors : head.Errors registry faults)
      : Errors registry faults (.initializerAssign head remaining)
  | initializerBitNot {context scope assignment rest body condition post statements expected type}
      {head : CompatibleBitNotStatements.Head context scope assignment}
      {remaining : Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative
        context scope (.initializers rest condition post statements) expected type body}
      (remainingErrors : Errors registry faults remaining)
      (headErrors : head.Errors faults)
      : Errors registry faults (.initializerBitNot head remaining)
end Tree
end Solcore.SourceSemantics.CoreLowering.TypedImperativeFor
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.TypedImperativeForCertificates
/-! Extraction follows actual loop-policy success and one enclosing native
HasType receipt. Source typing, expression certificates and policy authenticity
are static inputs; loop and assignment continuation typing are derived here. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.TypedImperativeFor
open Core Frontend SourceInference

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {readFuel : Nat} {values : ValuesContext} {source : TypedSource}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {definitions : DataEnvironment} {administrative : Core.Context}

open CompatibleEncoding (bind_ok)

private theorem read_found {checked : SourceCoreCompatibleCatalog.Checked} {source : TypedSource}
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

private theorem ensure_same {site : SourceCoreElaboration.ErrorSite} {expected actual : Ty}
    (accepted : SourceCoreBasic.ensureType site expected actual = .ok ()) : expected = actual := by
  unfold SourceCoreBasic.ensureType at accepted
  split at accepted
  · assumption
  · cases accepted

variable {policy : SourceCoreLoops.Policy}
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Solcore.Syntax.ValueAssignOp → Word}
  {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}

/-- A graph of the real for continuation, retaining the loop fuel separately
from the shrinking initializer budget. This is static compiler output data. -/
def InitialAccepted (policy : SourceCoreLoops.Policy) (fuel : Nat) (source : TypedSource) (scope : Scope)
    (items : List ForItemForm) (condition : ExpressionId) (post : List ForItemForm) (statements : List StatementId)
    (type : Ty) (reasonAt : ExpressionId → Word) (selfReason : Word) (code : Expr) : Prop :=
  ∃ headerFuel parentSite, ∃ next : Scope → Except SourceCoreBasic.Error Expr,
    SourceCoreLoops.lowerForItems policy parentSite headerFuel source scope items type reasonAt next = .ok code ∧
    ∀ loopScope nextCode, next loopScope = .ok nextCode →
      ∃ conditionCode : SourceCoreBasic.LoweredExpr, ∃ loopCode postCode,
        policy.lowerExpression fuel source loopScope condition reasonAt = .ok conditionCode ∧ conditionCode.type = .bool ∧
        SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source loopScope statements type reasonAt false selfReason = .ok loopCode ∧
        SourceCoreLoops.lowerForItems policy parentSite fuel source loopScope post type reasonAt
          (fun _ => pure (LocalLoop.fallthrough type)) = .ok postCode ∧
        nextCode = LocalLoop.iterate type conditionCode.expression loopCode postCode selfReason

def Accepted (policy : SourceCoreLoops.Policy) (fuel : Nat) (source : TypedSource) (scope : Scope)
    (position : Position) (type : Ty) (reasonAt : ExpressionId → Word) (selfReason : Word) (code : Expr) : Prop :=
  match position with
  | .statements mode statements => SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope statements type reasonAt mode selfReason = .ok code
  | .initializers items condition post statements => InitialAccepted policy fuel source scope items condition post statements type reasonAt selfReason code

/-- This extraction consumes one native typing receipt for the actual output.
Source grammar, expression typing and authenticated allocator policies remain
static inputs, independently of native type equality. -/
theorem tree_of_typed_position
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      policy.lowerBinder source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked source scope binder)
    (allocationPolicy : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (expressions : ∀ sourceContext, sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = false →
      sourceContext.signatures = values.checked.signatures →
      ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations source scope sourceContext → CompatibleExpressionTyped.Syntax source id →
      source.lookupExpression? id = some node → ExpressionHasType source sourceContext id node.type →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
      CompatibleExpressionTyped.Tree readFuel values source sourceContext solved reasonAt scope id lowered)
    (assignments : CompatibleAssignmentStatements.AssignmentPolicy policy values invalidProjection invalidOperand missingDefault)
    (unique : NodeOccurrencesUnique source)
    (assignmentExpressions : ∀ sourceContext scope fuel id lowered,
      sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = false →
      sourceContext.signatures = values.checked.signatures →
      CompatibleExpressionReads.ScopeDeclarations source scope sourceContext →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered → ∃ node,
        source.lookupExpression? id = some node ∧
        CompatibleExpressionTyped.Tree readFuel values source sourceContext solved reasonAt scope id lowered ∧
        HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
          (LanguageResult.resultType lowered.type) definitions)
    {context : SourceSemantics.Context} {scope : Scope} {position : Position} {expected : TypeSystem.Ty}
    (syntaxTree : Syntax source context position expected)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {fuel : Nat} {type : Ty} {code : Expr} {selfReason : Word} {nativeType : Ty}
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : Accepted policy fuel source scope position type reasonAt selfReason code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType definitions) :
    Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative
      context scope position expected type code := by
  induction syntaxTree generalizing scope fuel code nativeType with
  | body syntaxTree => exact .body syntaxTree (TypedLexicalControl.tree_of_flow readPolicy binderPolicy allocationPolicy expressions syntaxTree closed residual sourceSignatures declarations projection accepted)
  | @uninitialized context nextContext mode id node binder rest expected found form declaration monomorphic extended ordinary remaining ih =>
    simp only [Accepted] at accepted
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
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
      exact .uninitialized found form monomorphic extended ordinary (binder_projected (binderPolicy scope binder monomorphic ▸ projected))
        allocation annotation same (ih (by cases extended; exact closed) (by cases extended; exact residual) (by cases extended; exact sourceSignatures)
          (scope_bind payload declarations declaration extended) projection generated (TypedLexicalWhile.Native.absent_child allocation annotation same nativeTyped))

  | @initialized context nextContext mode id node binder initializer initializerNode rest expected found form declaration mono extended ordinary initializerFound sourceType typed initializerSyntax remaining ih =>
    simp only [Accepted] at accepted
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have identical := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      obtain ⟨payload, projected, accepted⟩ := bind_ok accepted
      obtain ⟨lowered, generated, accepted⟩ := bind_ok accepted
      obtain ⟨checked, checkedType, accepted⟩ := bind_ok accepted
      cases checked
      have sameType := ensure_same checkedType
      subst payload
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      simp only [mono, List.isEmpty_nil, ↓reduceIte] at accepted
      simp only [SourceCoreSourceCells.letInitialized, allocationPolicy] at accepted
      obtain ⟨allocationCode, generatedAllocation, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨allocation, annotation, same, rfl⟩ := CallableIndexedAllocationCompletion.accepted_receipts onError generatedAllocation
      exact .initialized found form mono extended ordinary initializerFound sourceType
        (expressions context closed residual sourceSignatures declarations initializerSyntax initializerFound typed generated)
        allocation annotation same
        (ih (by cases extended; exact closed) (by cases extended; exact residual) (by cases extended; exact sourceSignatures)
          (scope_bind lowered.type declarations declaration extended) projection generatedBody (TypedLexicalWhile.Native.initialized_child allocation annotation same nativeTyped))

  | @discard context mode id node expression expressionNode semicolon rest expected found form notTail sourceType expressionFound typed syntaxValue remaining ih =>
    simp only [Accepted] at accepted
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
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
        exact .discard found form notTail expressionFound (expressions context closed residual sourceSignatures declarations syntaxValue expressionFound typed generated)
          (ih closed residual sourceSignatures declarations projection generatedBody tailTyped)

  | @block context mode id node statements rest expected found form sourceType inner remaining innerIH restIH =>
    simp only [Accepted] at accepted
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨innerCode, generatedInner, accepted⟩ := bind_ok accepted
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨⟨_, headTyped⟩, ⟨_, tailTyped⟩⟩ := TypedLexicalWhile.Native.sequence_children nativeTyped
      exact .block found form (innerIH closed residual sourceSignatures declarations projection generatedInner headTyped) (restIH closed residual sourceSignatures declarations projection generatedBody tailTyped)
  | @ifThen context mode id node condition conditionNode thenBody elseBody rest expected found form sourceType conditionFound conditionType typed conditionSyntax thenSyntax elseSyntax remaining thenIH elseIH restIH =>
    simp only [Accepted] at accepted
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨conditionCode, generatedCondition, accepted⟩ := bind_ok accepted
      obtain ⟨checked, checkedCondition, accepted⟩ := bind_ok accepted
      cases checked
      have conditionTypeEq := ensure_same checkedCondition
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
        exact .ifThen found form conditionFound conditionType
          (expressions context closed residual sourceSignatures declarations conditionSyntax conditionFound typed generatedCondition)
          (thenIH closed residual sourceSignatures declarations projection generatedThen thenTyped) (elseIH closed residual sourceSignatures declarations projection generatedElse elseTyped) (restIH closed residual sourceSignatures declarations projection generatedBody tailTyped)
      | some statements =>
        obtain ⟨elseCode, generatedElse, accepted⟩ := bind_ok accepted
        obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
        cases accepted
        obtain ⟨⟨_, branchTyped⟩, ⟨_, tailTyped⟩⟩ := TypedLexicalWhile.Native.sequence_children nativeTyped
        obtain ⟨⟨_, thenTyped⟩, ⟨_, elseTyped⟩⟩ := TypedLexicalWhile.Native.conditional_children branchTyped
        exact .ifThen found form conditionFound conditionType
          (expressions context closed residual sourceSignatures declarations conditionSyntax conditionFound typed generatedCondition)
          (thenIH closed residual sourceSignatures declarations projection generatedThen thenTyped) (elseIH closed residual sourceSignatures declarations projection generatedElse elseTyped) (restIH closed residual sourceSignatures declarations projection generatedBody tailTyped)

  | @breaking context mode id node rest expected found form =>
    simp only [Accepted] at accepted
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      cases accepted
      exact .breaking found form
  | @continuing context mode id node rest expected found form =>
    simp only [Accepted] at accepted
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      cases accepted
      exact .continuing found form
  | @whileLoop context mode id node condition conditionNode statements rest expected found form conditionFound conditionType typed conditionSyntax loopSyntax remaining loopIH restIH =>
    simp only [Accepted] at accepted
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      obtain ⟨conditionCode, generatedCondition, accepted⟩ := bind_ok accepted
      obtain ⟨checked, checkedCondition, accepted⟩ := bind_ok accepted
      cases checked
      have sameType := ensure_same checkedCondition
      rcases conditionCode with ⟨native, code⟩
      dsimp only at sameType
      subst native
      obtain ⟨loopCode, generatedLoop, accepted⟩ := bind_ok accepted
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨⟨_, loopTyped⟩, ⟨_, tailTyped⟩⟩ := TypedLexicalWhile.Native.sequence_children nativeTyped
      obtain ⟨⟨_, loopBodyTyped⟩, loopTyped⟩ := TypedLexicalWhile.Native.while_body loopTyped
      exact .whileLoop found form conditionFound conditionType
        (expressions context closed residual sourceSignatures declarations conditionSyntax conditionFound typed generatedCondition)
        (loopIH closed residual sourceSignatures declarations projection generatedLoop loopBodyTyped)
        loopTyped
        (restIH closed residual sourceSignatures declarations projection generatedBody tailTyped)

  | @assign context mode id node assignment operator rhs rest expected found form sourceTyped writable rightTyped profile remaining ih =>
    simp only [Accepted] at accepted
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
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
      obtain ⟨head, rfl⟩ := CompatibleAssignmentStatements.Head.of_lower unique sourceSignatures sourceTyped writable rightTyped profile
        (fun id lowered generated => assignmentExpressions context scope fuel id lowered closed residual sourceSignatures declarations generated) compiled nativeTyped
      exact .assign found form head (ih closed residual sourceSignatures declarations projection compiledBody (TypedImperative.Native.execute_continuation nativeTyped))

  | @forLoop context mode id node initializer condition post statements rest expected found form sourceType initial remaining initialIH restIH =>
    simp only [Accepted] at accepted
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      obtain ⟨initialCode, generatedInitial, accepted⟩ := bind_ok accepted
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨⟨_, initialTyped⟩, ⟨_, tailTyped⟩⟩ := TypedLexicalWhile.Native.sequence_children nativeTyped
      apply Tree.forLoop found form
      · apply initialIH closed residual sourceSignatures declarations projection (nativeTyped := initialTyped)
        refine ⟨fuel, .occurrence id.occurrence, _, generatedInitial, ?_⟩
        intro loopScope nextCode generated
        obtain ⟨conditionCode, conditionGenerated, generated⟩ := bind_ok generated
        obtain ⟨checked, conditionChecked, generated⟩ := bind_ok generated
        cases checked
        obtain ⟨loopCode, loopGenerated, generated⟩ := bind_ok generated
        obtain ⟨postCode, postGenerated, generated⟩ := bind_ok generated
        cases generated
        exact ⟨conditionCode, loopCode, postCode, conditionGenerated, (ensure_same conditionChecked).symm, loopGenerated, postGenerated, rfl⟩
      · exact restIH closed residual sourceSignatures declarations projection generatedBody tailTyped
  | @initializersDone context condition conditionNode post statements expected conditionFound conditionType typed conditionSyntax loopBody postSyntax loopIH =>
    obtain ⟨headerFuel, parentSite, next, generated, nextReceipt⟩ := accepted
    have nextAccepted : next scope = .ok code := by cases headerFuel <;> exact generated
    obtain ⟨conditionCode, loopCode, postCode, conditionGenerated, conditionChecked, loopGenerated, postGenerated, rfl⟩ :=
      nextReceipt scope code nextAccepted
    rcases conditionCode with ⟨native, expression⟩
    dsimp only at conditionChecked
    subst native
    obtain ⟨⟨_, bodyTyped⟩, ⟨_, postTyped⟩, loopTyped⟩ := Native.iterate_children nativeTyped
    exact .initializersDone conditionFound conditionType
      (expressions context closed residual sourceSignatures declarations conditionSyntax conditionFound typed conditionGenerated)
      (loopIH closed residual sourceSignatures declarations projection loopGenerated bodyTyped)
      (TypedForHeader.tree_of_lowerForItems binderPolicy allocationPolicy assignments unique assignmentExpressions
        (fun _ _ _ _ _ _ _ same => by cases same; rfl) postSyntax closed residual sourceSignatures declarations postGenerated postTyped)
      loopTyped
  | @initializerUninitialized context nextContext binder rest condition post statements expected declaration monomorphic extended ordinary remaining ih =>
    obtain ⟨headerFuel, parentSite, next, accepted, nextReceipt⟩ := accepted
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
      exact .initializerUninitialized monomorphic extended ordinary (binder_projected (binderPolicy scope binder monomorphic ▸ projected))
        allocation annotation same (ih (by cases extended; exact closed) (by cases extended; exact residual) (by cases extended; exact sourceSignatures)
          (scope_bind payload declarations declaration extended) projection ⟨headerFuel, parentSite, next, generated, nextReceipt⟩ (TypedLexicalWhile.Native.absent_child allocation annotation same nativeTyped))
  | @initializerInitialized context nextContext binder initializer initializerNode rest condition post statements expected declaration mono extended ordinary initializerFound sourceType typed initializerSyntax remaining ih =>
    obtain ⟨headerFuel, parentSite, next, accepted, nextReceipt⟩ := accepted
    cases headerFuel with
    | zero => cases accepted
    | succ headerFuel =>
      simp only [SourceCoreLoops.lowerForItems] at accepted
      obtain ⟨payload, projected, accepted⟩ := bind_ok accepted
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      obtain ⟨lowered, generated, accepted⟩ := bind_ok accepted
      obtain ⟨checked, checkedType, accepted⟩ := bind_ok accepted
      cases checked
      have sameType := ensure_same checkedType
      subst payload
      simp only [mono, List.isEmpty_nil, ↓reduceIte] at accepted
      simp only [SourceCoreSourceCells.letInitialized, allocationPolicy] at accepted
      obtain ⟨allocationCode, generatedAllocation, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨allocation, annotation, same, rfl⟩ := CallableIndexedAllocationCompletion.accepted_receipts onError generatedAllocation
      obtain ⟨actualNode, actualFound, initial, _⟩ := assignmentExpressions context scope headerFuel initializer lowered closed residual sourceSignatures declarations generated
      exact .initializerInitialized mono extended ordinary initializerFound sourceType initial allocation annotation same
        (ih (by cases extended; exact closed) (by cases extended; exact residual) (by cases extended; exact sourceSignatures)
          (scope_bind lowered.type declarations declaration extended) projection ⟨headerFuel, parentSite, next, generatedBody, nextReceipt⟩ (TypedLexicalWhile.Native.initialized_child allocation annotation same nativeTyped))
  | @initializerDiscard context expression expressionNode rest condition post statements expected found typed syntaxTree remaining ih =>
    obtain ⟨headerFuel, parentSite, next, accepted, nextReceipt⟩ := accepted
    cases headerFuel with
    | zero => cases accepted
    | succ headerFuel =>
      simp only [SourceCoreLoops.lowerForItems] at accepted
      obtain ⟨lowered, generated, accepted⟩ := bind_ok accepted
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨actualNode, actualFound, child, _⟩ := assignmentExpressions context scope headerFuel expression lowered closed residual sourceSignatures declarations generated
      obtain ⟨_, bodyTyped⟩ := TypedLexicalWhile.Native.discard_child nativeTyped
      exact .initializerDiscard found child (ih closed residual sourceSignatures declarations projection ⟨headerFuel, parentSite, next, generatedBody, nextReceipt⟩ bodyTyped)
  | @initializerAssign context assignment operator rhs rest condition post statements expected sourceTyped writable rightTyped profile remaining ih =>
    obtain ⟨headerFuel, parentSite, next, accepted, nextReceipt⟩ := accepted
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
      obtain ⟨head, rfl⟩ := CompatibleAssignmentStatements.Head.of_lower unique sourceSignatures sourceTyped writable rightTyped profile
        (fun id lowered generated => assignmentExpressions context scope headerFuel id lowered closed residual sourceSignatures declarations generated) compiled nativeTyped
      exact .initializerAssign head (ih closed residual sourceSignatures declarations projection ⟨headerFuel, parentSite, next, generatedBody, nextReceipt⟩ (TypedImperative.Native.execute_continuation nativeTyped))

/-- This extraction consumes one native typing receipt for the actual output.
Source grammar, expression typing and authenticated allocator policies remain
static inputs, independently of native type equality. -/
theorem tree_of_typed_flow
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      policy.lowerBinder source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked source scope binder)
    (allocationPolicy : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (expressions : ∀ sourceContext, sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = false →
      sourceContext.signatures = values.checked.signatures →
      ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations source scope sourceContext → CompatibleExpressionTyped.Syntax source id →
      source.lookupExpression? id = some node → ExpressionHasType source sourceContext id node.type →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
      CompatibleExpressionTyped.Tree readFuel values source sourceContext solved reasonAt scope id lowered)
    (assignments : CompatibleAssignmentStatements.AssignmentPolicy policy values invalidProjection invalidOperand missingDefault)
    (unique : NodeOccurrencesUnique source)
    (assignmentExpressions : ∀ sourceContext scope fuel id lowered,
      sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = false →
      sourceContext.signatures = values.checked.signatures →
      CompatibleExpressionReads.ScopeDeclarations source scope sourceContext →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered → ∃ node,
        source.lookupExpression? id = some node ∧
        CompatibleExpressionTyped.Tree readFuel values source sourceContext solved reasonAt scope id lowered ∧
        HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
          (LanguageResult.resultType lowered.type) definitions)
    {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {statements : List StatementId} {expected : TypeSystem.Ty}
    (syntaxTree : Syntax source context (.statements mode statements) expected)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {fuel : Nat} {type : Ty} {code : Expr} {selfReason : Word} {nativeType : Ty}
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope statements type reasonAt mode selfReason = .ok code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType definitions) :
    Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative
      context scope (.statements mode statements) expected type code := by
  exact tree_of_typed_position readPolicy binderPolicy allocationPolicy expressions assignments unique assignmentExpressions syntaxTree closed residual sourceSignatures declarations projection accepted nativeTyped

/-- The public statement wrapper's real typing exposes its enclosed flow.
This retains the exact emitted finish/toControl equation for body consumers. -/
theorem tree_of_typed_body
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      policy.lowerBinder source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked source scope binder)
    (allocationPolicy : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (expressions : ∀ sourceContext, sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = false →
      sourceContext.signatures = values.checked.signatures →
      ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations source scope sourceContext → CompatibleExpressionTyped.Syntax source id →
      source.lookupExpression? id = some node → ExpressionHasType source sourceContext id node.type →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
      CompatibleExpressionTyped.Tree readFuel values source sourceContext solved reasonAt scope id lowered)
    (assignments : CompatibleAssignmentStatements.AssignmentPolicy policy values invalidProjection invalidOperand missingDefault)
    (unique : NodeOccurrencesUnique source)
    (assignmentExpressions : ∀ sourceContext scope fuel id lowered,
      sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = false →
      sourceContext.signatures = values.checked.signatures →
      CompatibleExpressionReads.ScopeDeclarations source scope sourceContext →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered → ∃ node,
        source.lookupExpression? id = some node ∧
        CompatibleExpressionTyped.Tree readFuel values source sourceContext solved reasonAt scope id lowered ∧
        HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
          (LanguageResult.resultType lowered.type) definitions)
    {context : SourceSemantics.Context} {scope : Scope} {statements : List StatementId} {expected : TypeSystem.Ty}
    (syntaxTree : Syntax source context (.statements true statements) expected)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {fuel : Nat} {type nativeType : Ty} {code : Expr} {fellThrough escaped : Word}
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope statements type reasonAt fellThrough escaped = .ok code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType definitions) :
    ∃ flow,
      SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope statements type reasonAt true escaped = .ok flow ∧
      Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative
        context scope (.statements true statements) expected type flow ∧
      code = LocalControl.finish type (LocalLoop.toControl type flow escaped)
        (if type = .unit then LanguageResult.success .unit else LanguageResult.failure type (.word fellThrough)) := by
  unfold SourceCoreLoops.lowerStatementsWithPolicy at accepted
  obtain ⟨flow, generated, same⟩ := bind_ok accepted
  cases same
  obtain ⟨_, flowTyped⟩ := TypedLexicalWhile.Native.finished_flow nativeTyped
  exact ⟨flow, generated, tree_of_typed_flow readPolicy binderPolicy allocationPolicy expressions
    assignments unique assignmentExpressions syntaxTree closed residual sourceSignatures declarations projection generated flowTyped, rfl⟩

end Solcore.SourceSemantics.CoreLowering.TypedImperativeFor
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.TypedImperativeForControlShape
/-! Successful source control excludes the separate fault judgment for this
recursive grammar, including ordinary assignment heads. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.TypedImperativeFor
open Core Frontend SourceInference
open TypedLexicalWhile (ControlShape while_control_shape)

theorem for_control_shape {program : Program} {context finalContext : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {condition : ExpressionId} {post : List ForItemForm} {statements : List StatementId}
    {outcome : Dynamic.ControlOutcome}
    (trace : Dynamic.ForLoopExecutes program context evidence source environment before condition post statements finalContext outcome after) :
    (∃ next, outcome = .fallthrough next) ∨ (∃ value, outcome = .returned value) := by
  apply LoopStatements.for_induction
    (motive := fun _ _ _ _ _ _ _ _ _ outcome _ =>
      (∃ next, outcome = .fallthrough next) ∨ (∃ value, outcome = .returned value))
    (execution := trace)
  · intros; exact .inl ⟨_, rfl⟩
  · intros; assumption
  · intros; assumption
  · intros; exact .inl ⟨_, rfl⟩
  · intros; exact .inr ⟨_, rfl⟩

def ControlShapeAt (source : TypedSource) : Position → Prop
  | .initializers _ _ _ _ => True
  | .statements mode statements =>
      ∀ {program : Program} {actualContext finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
        {environment : Dynamic.Environment} {before after : Dynamic.Heap} {outcome : Dynamic.ControlOutcome},
        ScalarStatementViews.ListExecutes mode program actualContext evidence source environment before statements finalContext outcome after →
        ControlShape outcome

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {readFuel : Nat} {values : ValuesContext} {source : TypedSource}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {definitions : DataEnvironment} {administrative : Core.Context}

theorem Tree.control_shapeAt {context : SourceSemantics.Context} {scope : Scope} {position : Position}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative
      context scope position expected type code)
    (unique : NodeOccurrencesUnique source) : ControlShapeAt source position := by
  induction tree with
  | body syntaxTree _ =>
    intro program actualContext finalContext evidence environment before after outcome executed
    cases TypedLexicalNamedBody.syntax_control_shape syntaxTree unique executed with
    | fallthrough next _ => exact .fallthrough next
    | returned value => exact .returned value
  | @uninitialized context nextContext scope mode id node binder rest expected type code payload found form mono extended ordinary projected allocation annotation same tail ih =>
    intro program actualContext finalContext evidence environment before after outcome executed
    have contains := lookupStatement?_sound found
    rcases ScalarStatementViews.cons_view mode unique contains (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, _, tail⟩ | ⟨head, terminal⟩
    · exact ih tail
    · obtain ⟨_, _, rfl, _⟩ := ScalarStatementViews.letUninitialized unique contains form head
      cases terminal
  | @initialized context nextContext scope mode id node binder initializer initializerNode lowered code rest expected type found form mono extended ordinary initialFound sourceType initial allocation annotation same tail ih =>
    intro program actualContext finalContext evidence environment before after outcome executed
    have contains := lookupStatement?_sound found
    rcases ScalarStatementViews.cons_view mode unique contains (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, _, tail⟩ | ⟨head, terminal⟩
    · exact ih tail
    · obtain ⟨_, _, _, _, rfl, _, _⟩ := ScalarStatementViews.letInitialized unique contains form mono head
      cases terminal
  | @discard context scope mode id node expression expressionNode semicolon rest expected lowered type code found form guard expressionFound value remaining ih =>
    intro program actualContext finalContext evidence environment before after outcome executed
    have contains := lookupStatement?_sound found
    rcases ScalarStatementViews.cons_view mode unique contains (TypedScopedStatements.not_tail form guard) executed with
      ⟨_, _, _, _, tail⟩ | ⟨head, terminal⟩
    · exact ih tail
    · obtain ⟨_, rfl, _, _⟩ := ScalarStatementViews.expression unique contains form head
      cases terminal
  | @block context scope mode id node statements rest expected type innerCode code found form inner remaining innerIH restIH =>
    intro program actualContext finalContext evidence environment before after outcome executed
    have contains := lookupStatement?_sound found
    rcases ScalarStatementViews.cons_view mode unique contains (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, _, tail⟩ | ⟨head, terminal⟩
    · exact restIH tail
    · obtain ⟨_, _, innerOutcome, rfl, innerTrace⟩ := ScalarStatementViews.block unique contains form head
      exact (innerIH innerTrace).restore environment
  | @ifThen context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode code found form conditionFound conditionType typed thenTree elseTree remaining thenIH elseIH restIH =>
    intro program actualContext finalContext evidence environment before after outcome executed
    have contains := lookupStatement?_sound found
    rcases ScalarStatementViews.cons_view mode unique contains (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, _, tail⟩ | ⟨head, terminal⟩
    · exact restIH tail
    · obtain ⟨_, boolean, _, _, innerOutcome, _, rfl, branchTrace⟩ := ScalarStatementViews.ifThen unique contains form head
      cases boolean with
      | false => exact (elseIH branchTrace).restore environment
      | true => exact (thenIH branchTrace).restore environment
  | @breaking context scope mode id node rest expected type found form =>
    intro program actualContext finalContext evidence environment before after outcome executed
    have contains := lookupStatement?_sound found
    rcases ScalarStatementViews.cons_view mode unique contains (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, head, _⟩ | ⟨head, _⟩
    · obtain ⟨_, impossible, _⟩ := ScalarStatementViews.breaking unique contains form head; cases impossible
    · obtain ⟨_, rfl, _⟩ := ScalarStatementViews.breaking unique contains form head; exact .breaking environment
  | @continuing context scope mode id node rest expected type found form =>
    intro program actualContext finalContext evidence environment before after outcome executed
    have contains := lookupStatement?_sound found
    rcases ScalarStatementViews.cons_view mode unique contains (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, head, _⟩ | ⟨head, _⟩
    · obtain ⟨_, impossible, _⟩ := ScalarStatementViews.continuing unique contains form head; cases impossible
    · obtain ⟨_, rfl, _⟩ := ScalarStatementViews.continuing unique contains form head; exact .continuing environment
  | @whileLoop context scope mode id node condition conditionNode statements rest expected type conditionCode loopCode code reason found form conditionFound conditionType typed loopBody nativeTyped remaining innerIH restIH =>
    intro program actualContext finalContext evidence environment before after outcome executed
    have contains := lookupStatement?_sound found
    rcases ScalarStatementViews.cons_view mode unique contains (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, _, tail⟩ | ⟨head, terminal⟩
    · exact restIH tail
    · obtain ⟨_, _, innerOutcome, rfl, innerTrace⟩ := ScalarStatementViews.whileLoop unique contains form head
      rcases while_control_shape innerTrace with ⟨next, rfl⟩ | ⟨value, rfl⟩
      · exact .fallthrough environment
      · exact .returned value

  | @assign context scope mode id node assignment operator rhs rest expected type body found form head remaining ih =>
    intro program actualContext finalContext evidence environment before after outcome executed
    have contains := lookupStatement?_sound found
    rcases ScalarStatementViews.cons_view mode unique contains (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, _, tail⟩ | ⟨first, terminal⟩
    · exact ih tail
    · obtain ⟨_, rfl, _⟩ := ScalarStatementViews.assignValue unique contains form first
      cases terminal
  | @bitNot context scope mode id node assignment rest expected type body found form head remaining ih =>
    intro program actualContext finalContext evidence environment before after outcome executed
    have contains := lookupStatement?_sound found
    rcases ScalarStatementViews.cons_view mode unique contains (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, _, tail⟩ | ⟨first, terminal⟩
    · exact ih tail
    · obtain ⟨_, rfl, _⟩ := CompatibleBitNotStatements.bitNot_view unique contains form first
      cases terminal
  | @forLoop context scope mode id node initializer condition post statements rest expected type initialCode body found form initial remaining initialIH restIH =>
    intro program actualContext finalContext evidence environment before after outcome executed
    have contains := lookupStatement?_sound found
    rcases ScalarStatementViews.cons_view mode unique contains (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, _, tail⟩ | ⟨head, terminal⟩
    · exact restIH tail
    · obtain ⟨_, _, _, _, _, innerOutcome, rfl, _, loop⟩ := ForSourceViews.success unique contains form head
      rcases for_control_shape loop with ⟨next, rfl⟩ | ⟨value, rfl⟩
      · exact .fallthrough environment
      · exact .returned value
  | initializersDone | initializerUninitialized | initializerInitialized | initializerDiscard | initializerAssign | initializerBitNot => trivial

theorem Tree.control_shape {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative
      context scope (.statements mode statements) expected type code)
    (unique : NodeOccurrencesUnique source)
    {program : Program} {actualContext finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {outcome : Dynamic.ControlOutcome}
    (executed : ScalarStatementViews.ListExecutes mode program actualContext evidence source environment before statements finalContext outcome after) :
    ControlShape outcome := tree.control_shapeAt unique executed

theorem Tree.control_not_fault {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative
      context scope (.statements mode statements) expected type code)
    (unique : NodeOccurrencesUnique source)
    {program : Program} {actualContext finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault}
    (executed : ScalarStatementViews.ListExecutes mode program actualContext evidence source environment before statements finalContext (.fault reason) after) : False := by
  cases tree.control_shape unique executed
end Solcore.SourceSemantics.CoreLowering.TypedImperativeFor
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.TypedImperativeForMeaning
/-! Finite preservation and completed reflection for mixed assignments, while
loops, lexical bindings and scoped control. Concrete expression and statement
trees discharge every child meaning. Native typing is a separate static receipt;
scoped exits restore the source context while retaining effects and live cells. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.TypedImperativeFor
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedAllocationCompletion CoreProof
open TypedScopedStatements (Executes)
open TypedImperative (assignment_preserves assignment_reflects)
open TypedLexicalWhile hiding Syntax Tree Scope ValuesContext absentRequest initializedRequest sequence
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
  {readFuel : Nat} {values : ValuesContext} {source : TypedSource}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry}

variable (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

variable {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)

abbrev PreservesAt (context : SourceSemantics.Context) (scope : Scope) (position : Position)
    (expected : TypeSystem.Ty) (type : Ty) (code : Expr) : Prop :=
  match position with
  | .statements mode statements => Preserves functions program evidence (registry := registry) (source := source)
      (context := context) (scope := scope) (faults := faults) (solved := solved) (frameLayout := frame)
      (globals := globals) (administrative := administrative) mode statements expected type code
  | .initializers items condition post statements => PreservingHeader functions program evidence
      (layouts := layouts) (owner := owner) (active := active) (frameLayout := frame) (globals := globals)
      (onError := onError) (readFuel := readFuel) (source := source) (solved := solved) (reasonAt := reasonAt)
      (administrative := administrative) (registry := registry) (faults := faults)
      context scope items condition post statements expected type code

abbrev ReflectsAt (context : SourceSemantics.Context) (scope : Scope) (position : Position)
    (expected : TypeSystem.Ty) (type : Ty) (code : Expr) : Prop :=
  match position with
  | .statements mode statements => Reflects functions program evidence (registry := registry) (source := source)
      (context := context) (scope := scope) (faults := faults) (solved := solved) (frameLayout := frame)
      (globals := globals) (administrative := administrative) mode statements expected type code
  | .initializers items condition post statements => ReflectingHeader functions program evidence
      (layouts := layouts) (owner := owner) (active := active) (frameLayout := frame) (globals := globals)
      (onError := onError) (readFuel := readFuel) (source := source) (solved := solved) (reasonAt := reasonAt)
      (administrative := administrative) (registry := registry) (faults := faults)
      context scope items condition post statements expected type code

include definitions registered extension uninitialized missing faithful observations in
theorem Tree.preservesAt [FunctionCalls.FaultTokens faults] (unique : NodeOccurrencesUnique source)
    {context : SourceSemantics.Context} {scope : Scope} {position : Position}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError readFuel values source solved reasonAt ambient.definitions administrative
      context scope position expected type code)
    (errors : Tree.Errors registry faults tree) :
    PreservesAt functions program evidence (layouts := layouts) (owner := owner) (active := active)
      (frame := frame) (globals := globals) (onError := onError) (readFuel := readFuel)
      (source := source) (solved := solved) (reasonAt := reasonAt) (administrative := administrative)
      (registry := registry) (faults := faults) context scope position expected type code := by
  induction errors with
  | @body context scope mode statements expected type code syntaxTree body =>
    intro contextValid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext
      environments heaps locals agrees actualTyped reference read unmapped trace
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, related, finalHeaps, maps, worlds, preservation, metadata, lexical⟩ :=
      body.preserves functions definitions registered extension program evidence uninitialized missing contextValid unique environments heaps locals agrees actualTyped reference read unmapped trace
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
        CompatibleExpressionTyped.preserves functions extension program evidence contextValid unique uninitialized missing initial initialFound
          environments heaps locals agrees actualTyped (.fault failed)
      cases represented with
      | fault matched => exact ⟨_, finalStore, finalMap, finalWorld, LanguageResult.bind_failure _ initialEval,
          .fault matched, finalHeaps, maps, worlds, preservation, metadata, _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
    · obtain ⟨value, middleStore, middleMap, middleWorld, initialEval, represented, middleHeaps, maps, worlds, preservation, metadata⟩ :=
        CompatibleExpressionTyped.preserves functions extension program evidence contextValid unique uninitialized missing initial initialFound
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
        CompatibleExpressionTyped.preserves functions extension program evidence contextValid unique uninitialized missing child expressionFound
          environments heaps locals agrees actualTyped (.fault failed)
      cases represented with
      | fault matched =>
        exact ⟨_, finalStore, finalMap, finalWorld, by rw [LoopRenaming.discard]; exact LocalSequence.discard_failure _ evaluated,
          .fault matched, finalHeaps, maps, worlds, frame, metadata,
          _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
    · obtain ⟨value, middleStore, middleMap, middleWorld, first, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata⟩ :=
        CompatibleExpressionTyped.preserves functions extension program evidence contextValid unique uninitialized missing child expressionFound
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
      (conditional_preserves (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame) (globals := globals) (extension := extension) (uninitialized := uninitialized) (missing := missing) (unique := unique) found form conditionFound conditionType conditionTree thenIH elseIH) remainingIH
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
      (while_preserves functions extension program evidence uninitialized missing found form conditionFound conditionTree nativeTyped unique loopIH) restIH
      contextValid environments heaps locals agrees actualTyped reference read unmapped trace

  | @assign context scope mode id node assignment operator rhs rest expected type body found form head remaining remainingErrors headErrors ih =>
    intro contextValid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext
      environments heaps locals agrees actualTyped reference read unmapped trace
    exact assignment_preserves functions extension program evidence uninitialized missing faithful observations
      found form head headErrors unique ih contextValid environments heaps locals agrees actualTyped reference read unmapped trace

  | @bitNot context scope mode id node assignment rest expected type body found form head remaining remainingErrors headErrors ih =>
    intro contextValid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext
      environments heaps locals agrees actualTyped reference read unmapped trace
    exact CompatibleBitNotStatements.assignment_preserves functions program evidence
      found form head headErrors unique ih contextValid environments heaps locals agrees actualTyped reference read unmapped trace

  | @forLoop context scope mode id node initializer condition post statements rest expected type initialCode body found form initial remaining initialErrors remainingErrors initialIH restIH =>
    intro contextValid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext
      environments heaps locals agrees actualTyped reference read unmapped trace
    exact sequence_preserves (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame) (globals := globals) (unique := unique) found (by intro expression; simp [form])
      (header_preserves functions definitions registered extension program evidence uninitialized missing faithful observations unique found form initialIH) restIH
      contextValid environments heaps locals agrees actualTyped reference read unmapped trace
  | @initializersDone context scope condition conditionNode post statements expected type conditionCode bodyCode postCode selfReason conditionFound conditionType conditionTree loopTree postTree nativeTyped loopErrors postErrors loopIH =>
    have completed := loop_preserves functions extension program evidence unique uninitialized missing definitions registered faithful observations
      conditionFound conditionTree nativeTyped postTree postErrors loopIH
    exact ⟨.nil completed, TypedForHeader.Tree.Errors.nil (next := completed)⟩
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

include definitions registered extension uninitialized missing faithful observations in
theorem Tree.reflectsAt [FunctionCalls.FaultTokens faults] (functionTypes : FunctionRuntimeViews functions) (unique : NodeOccurrencesUnique source)
    {context : SourceSemantics.Context} {scope : Scope} {position : Position}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError readFuel values source solved reasonAt ambient.definitions administrative
      context scope position expected type code)
    (errors : Tree.Errors registry faults tree) :
    ReflectsAt functions program evidence (layouts := layouts) (owner := owner) (active := active)
      (frame := frame) (globals := globals) (onError := onError) (readFuel := readFuel)
      (source := source) (solved := solved) (reasonAt := reasonAt) (administrative := administrative)
      (registry := registry) (faults := faults) context scope position expected type code := by
  induction errors with
  | @body context scope mode statements expected type code syntaxTree body =>
    intro contextValid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
      environments heaps locals agrees actualTyped reference read unmapped evaluated
    obtain ⟨finalContext, outcome, after, finalMap, finalWorld, trace, related, finalHeaps, maps, worlds, preservation, metadata, lexical⟩ :=
      body.reflects functions definitions registered extension program evidence uninitialized missing contextValid environments heaps locals agrees actualTyped reference read unmapped evaluated
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
      CompatibleExpressionTyped.reflects functions extension program evidence contextValid uninitialized missing initial initialFound
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
        CompatibleExpressionTyped.reflects functions extension program evidence contextValid uninitialized missing child expressionFound
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
        CompatibleExpressionTyped.reflects functions extension program evidence contextValid uninitialized missing child expressionFound
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
      (conditional_reflects (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame) (globals := globals) (extension := extension) (uninitialized := uninitialized) (missing := missing) found form conditionFound conditionType conditionTree thenIH elseIH) remainingIH
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
      (while_reflects functions extension program evidence uninitialized missing found form conditionFound conditionTree nativeTyped loopIH
        (fun executed => loopTree.control_not_fault unique executed)) restIH
      contextValid environments heaps locals agrees actualTyped reference read unmapped evaluated

  | @assign context scope mode id node assignment operator rhs rest expected type body found form head remaining remainingErrors headErrors ih =>
    intro contextValid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
      environments heaps locals agrees actualTyped reference read unmapped evaluated
    exact assignment_reflects functions extension program evidence uninitialized missing faithful observations functionTypes
      found form head headErrors unique ih contextValid environments heaps locals agrees actualTyped reference read unmapped evaluated

  | @bitNot context scope mode id node assignment rest expected type body found form head remaining remainingErrors headErrors ih =>
    intro contextValid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
      environments heaps locals agrees actualTyped reference read unmapped evaluated
    exact CompatibleBitNotStatements.assignment_reflects functions program evidence
      found form head headErrors unique ih contextValid environments heaps locals agrees actualTyped reference read unmapped evaluated

  | @forLoop context scope mode id node initializer condition post statements rest expected type initialCode body found form initial remaining initialErrors remainingErrors initialIH restIH =>
    intro contextValid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
      environments heaps locals agrees actualTyped reference read unmapped evaluated
    exact sequence_reflects (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame) (globals := globals) found (by intro expression; simp [form])
      (header_reflects functions definitions registered extension program evidence uninitialized missing faithful observations functionTypes unique found form initialIH) restIH
      contextValid environments heaps locals agrees actualTyped reference read unmapped evaluated
  | @initializersDone context scope condition conditionNode post statements expected type conditionCode bodyCode postCode selfReason conditionFound conditionType conditionTree loopTree postTree nativeTyped loopErrors postErrors loopIH =>
    have completed := loop_reflects functions extension program evidence unique uninitialized missing definitions registered faithful observations functionTypes
      conditionFound conditionTree nativeTyped postTree postErrors loopIH (fun executed => loopTree.control_not_fault unique executed)
    exact ⟨.nil completed, TypedForHeader.Tree.Errors.nil (next := completed)⟩
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

include definitions registered extension uninitialized missing faithful observations in
theorem Tree.preserves [FunctionCalls.FaultTokens faults] {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError readFuel values source solved reasonAt ambient.definitions administrative
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
  exact tree.preservesAt functions definitions registered extension program evidence uninitialized missing faithful observations unique errors
    contextValid environments heaps locals agrees actualTyped reference read unmapped trace

include definitions registered extension uninitialized missing faithful observations in
theorem Tree.reflects [FunctionCalls.FaultTokens faults] (functionTypes : FunctionRuntimeViews functions) {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError readFuel values source solved reasonAt ambient.definitions administrative
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
  exact tree.reflectsAt functions definitions registered extension program evidence uninitialized missing faithful observations functionTypes unique errors
    contextValid environments heaps locals agrees actualTyped reference read unmapped evaluated

end Solcore.SourceSemantics.CoreLowering.TypedImperativeFor
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.TypedImperativeForUnaryCertificates
/-! Extraction follows actual loop-policy success and one enclosing native
HasType receipt. Source typing, expression certificates and policy authenticity
are static inputs; loop and assignment continuation typing are derived here. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.TypedImperativeFor
open Core Frontend SourceInference

inductive UnarySyntax (source : TypedSource) :
    SourceSemantics.Context → Position → TypeSystem.Ty → Prop where
  | body {context mode statements expected} (syntaxTree : TypedLexicalControl.Syntax source context mode statements expected) :
      UnarySyntax source context (.statements mode statements) expected
  | uninitialized {context nextContext mode id node binder rest expected}
      (found : source.lookupStatement? id = some node) (form : node.form = .letDecl binder none)
      (declaration : SourceCoreDataPlaces.rootBinder source binder.id = .ok binder)
      (monomorphic : binder.scheme.quantified = [])
      (extended : BinderExtends source.owner context binder nextContext)
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (remaining : UnarySyntax source nextContext (.statements mode rest) expected) :
      UnarySyntax source context (.statements mode (id :: rest)) expected

  | initialized {context nextContext mode id node binder initializer initializerNode rest expected}
      (found : source.lookupStatement? id = some node) (form : node.form = .letDecl binder (some initializer))
      (declaration : SourceCoreDataPlaces.rootBinder source binder.id = .ok binder)
      (monomorphic : binder.scheme.quantified = [])
      (extended : BinderExtends source.owner context binder nextContext)
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (initializerFound : source.lookupExpression? initializer = some initializerNode)
      (sourceType : initializerNode.type = binder.scheme.body)
      (initializerTyped : ExpressionHasType source context initializer initializerNode.type)
      (initializerUnarySyntax : CompatibleExpressionTyped.Syntax source initializer)
      (remaining : UnarySyntax source nextContext (.statements mode rest) expected) :
      UnarySyntax source context (.statements mode (id :: rest)) expected
  | discard {context mode id node expression expressionNode semicolon rest expected}
      (found : source.lookupStatement? id = some node) (form : node.form = .expression expression semicolon)
      (notTail : (!semicolon && mode && rest.isEmpty) = false)
      (sourceType : node.type = if semicolon then .unit else expressionNode.type)
      (expressionFound : source.lookupExpression? expression = some expressionNode)
      (typed : ExpressionHasType source context expression expressionNode.type)
      (value : CompatibleExpressionTyped.Syntax source expression)
      (remaining : UnarySyntax source context (.statements mode rest) expected) : UnarySyntax source context (.statements mode (id :: rest)) expected
  | block {context mode id node statements rest expected}
      (found : source.lookupStatement? id = some node) (form : node.form = .block statements)
      (sourceType : node.type = .unit)
      (inner : UnarySyntax source context (.statements false statements) expected)
      (remaining : UnarySyntax source context (.statements mode rest) expected) : UnarySyntax source context (.statements mode (id :: rest)) expected
  | ifThen {context mode id node condition conditionNode thenBody elseBody rest expected}
      (found : source.lookupStatement? id = some node) (form : node.form = .ifThen condition thenBody elseBody)
      (sourceType : node.type = .unit)
      (conditionFound : source.lookupExpression? condition = some conditionNode)
      (conditionType : conditionNode.type = .bool)
      (typed : ExpressionHasType source context condition conditionNode.type)
      (conditionUnarySyntax : CompatibleExpressionTyped.Syntax source condition)
      (thenUnarySyntax : UnarySyntax source context (.statements false thenBody) expected)
      (elseUnarySyntax : UnarySyntax source context (.statements false (elseBody.getD [])) expected)
      (remaining : UnarySyntax source context (.statements mode rest) expected) : UnarySyntax source context (.statements mode (id :: rest)) expected

  | breaking {context mode id node rest expected}
      (found : source.lookupStatement? id = some node) (form : node.form = .breakStmt) :
      UnarySyntax source context (.statements mode (id :: rest)) expected
  | continuing {context mode id node rest expected}
      (found : source.lookupStatement? id = some node) (form : node.form = .continueStmt) :
      UnarySyntax source context (.statements mode (id :: rest)) expected
  | whileLoop {context mode id node condition conditionNode statements rest expected}
      (found : source.lookupStatement? id = some node) (form : node.form = .whileLoop condition statements)
      (conditionFound : source.lookupExpression? condition = some conditionNode)
      (conditionType : conditionNode.type = .bool)
      (typed : ExpressionHasType source context condition conditionNode.type)
      (conditionUnarySyntax : CompatibleExpressionTyped.Syntax source condition)
      (loopBody : UnarySyntax source context (.statements false statements) expected)
      (remaining : UnarySyntax source context (.statements mode rest) expected) : UnarySyntax source context (.statements mode (id :: rest)) expected

  | assign {context mode id node assignment operator rhs rest expected}
      (found : source.lookupStatement? id = some node) (form : node.form = .assignValue assignment operator rhs)
      (sourceTyped : ∀ binder, SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder →
        SourceProjectionsHaveType source context binder.scheme.body assignment.target.projections assignment.target.type)
      (writable : ∀ binder, SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder → WritableLocal context assignment.target.root binder.scheme.body)
      (rightTyped : ExpressionHasType source context rhs assignment.target.type)
      (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
        SourceCoreRawMetadata.runtimeType assignment.target.type = .integer ∧ operator.wordOnly = false)
      (remaining : UnarySyntax source context (.statements mode rest) expected) : UnarySyntax source context (.statements mode (id :: rest)) expected


  | forLoop {context mode id node initializer condition post statements rest expected}
      (found : source.lookupStatement? id = some node) (form : node.form = .forLoop initializer condition post statements)
      (sourceType : node.type = .unit)
      (initial : UnarySyntax source context (.initializers initializer condition post statements) expected)
      (remaining : UnarySyntax source context (.statements mode rest) expected) : UnarySyntax source context (.statements mode (id :: rest)) expected
  | initializersDone {context condition conditionNode post statements expected}
      (conditionFound : source.lookupExpression? condition = some conditionNode)
      (conditionType : conditionNode.type = .bool)
      (typed : ExpressionHasType source context condition conditionNode.type)
      (conditionUnarySyntax : CompatibleExpressionTyped.Syntax source condition)
      (loopBody : UnarySyntax source context (.statements false statements) expected)
      (postUnarySyntax : TypedForHeader.UnarySyntax source context post) :
      UnarySyntax source context (.initializers [] condition post statements) expected
  | initializerUninitialized {context nextContext binder rest condition post statements expected}
      (declaration : SourceCoreDataPlaces.rootBinder source binder.id = .ok binder)
      (monomorphic : binder.scheme.quantified = [])
      (extended : BinderExtends source.owner context binder nextContext)
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (remaining : UnarySyntax source nextContext (.initializers rest condition post statements) expected) : UnarySyntax source context (.initializers (.letDecl binder none :: rest) condition post statements) expected
  | initializerInitialized {context nextContext binder initializer initializerNode rest condition post statements expected}
      (declaration : SourceCoreDataPlaces.rootBinder source binder.id = .ok binder)
      (monomorphic : binder.scheme.quantified = [])
      (extended : BinderExtends source.owner context binder nextContext)
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (initializerFound : source.lookupExpression? initializer = some initializerNode)
      (sourceType : initializerNode.type = binder.scheme.body)
      (initializerTyped : ExpressionHasType source context initializer initializerNode.type)
      (initializerUnarySyntax : CompatibleExpressionTyped.Syntax source initializer)
      (remaining : UnarySyntax source nextContext (.initializers rest condition post statements) expected) : UnarySyntax source context (.initializers (.letDecl binder (some initializer) :: rest) condition post statements) expected
  | initializerDiscard {context expression expressionNode rest condition post statements expected}
      (found : source.lookupExpression? expression = some expressionNode)
      (typed : ExpressionHasType source context expression expressionNode.type)
      (syntaxTree : CompatibleExpressionTyped.Syntax source expression)
      (remaining : UnarySyntax source context (.initializers rest condition post statements) expected) : UnarySyntax source context (.initializers (.expression expression :: rest) condition post statements) expected
  | initializerAssign {context assignment operator rhs rest condition post statements expected}
      (sourceTyped : ∀ binder, SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder →
        SourceProjectionsHaveType source context binder.scheme.body assignment.target.projections assignment.target.type)
      (writable : ∀ binder, SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder →
        WritableLocal context assignment.target.root binder.scheme.body)
      (rightTyped : ExpressionHasType source context rhs assignment.target.type)
      (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
        SourceCoreRawMetadata.runtimeType assignment.target.type = .integer ∧ operator.wordOnly = false)
      (remaining : UnarySyntax source context (.initializers rest condition post statements) expected) : UnarySyntax source context (.initializers (.assignValue assignment operator rhs :: rest) condition post statements) expected
  | bitNot {context mode id node assignment rest expected}
      (found : source.lookupStatement? id = some node) (form : node.form = .assignBitNot assignment)
      (writable : ∀ binder, SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder →
        WritableLocal context assignment.target.root binder.scheme.body)
      (bare : assignment.target.projections = [])
      (profile : SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
        SourceCoreRawMetadata.runtimeType assignment.target.type = .integer)
      (remaining : UnarySyntax source context (.statements mode rest) expected) :
      UnarySyntax source context (.statements mode (id :: rest)) expected
  | initializerBitNot {context assignment rest condition post statements expected}
      (writable : ∀ binder, SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder →
        WritableLocal context assignment.target.root binder.scheme.body)
      (bare : assignment.target.projections = [])
      (profile : SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
        SourceCoreRawMetadata.runtimeType assignment.target.type = .integer)
      (remaining : UnarySyntax source context (.initializers rest condition post statements) expected) :
      UnarySyntax source context (.initializers (.assignBitNot assignment :: rest) condition post statements) expected

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {readFuel : Nat} {values : ValuesContext} {source : TypedSource}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
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
theorem tree_of_typed_position_withBitNot
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      policy.lowerBinder source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked source scope binder)
    (allocationPolicy : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (expressions : ∀ sourceContext, sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = false →
      sourceContext.signatures = values.checked.signatures →
      ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations source scope sourceContext → CompatibleExpressionTyped.Syntax source id →
      source.lookupExpression? id = some node → ExpressionHasType source sourceContext id node.type →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
      CompatibleExpressionTyped.Tree readFuel values source sourceContext solved reasonAt scope id lowered)
    (assignments : CompatibleAssignmentStatements.AssignmentPolicy policy values invalidProjection invalidOperand missingDefault)
    (unaryPolicy : CompatibleBitNotStatements.Policy policy values invalidProjection invalidUnary missingDefault)
    (unique : NodeOccurrencesUnique source)
    (assignmentExpressions : ∀ sourceContext scope fuel id lowered,
      sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = false →
      sourceContext.signatures = values.checked.signatures →
      CompatibleExpressionReads.ScopeDeclarations source scope sourceContext →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered → ∃ node,
        source.lookupExpression? id = some node ∧
        CompatibleExpressionTyped.Tree readFuel values source sourceContext solved reasonAt scope id lowered ∧
        HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
          (LanguageResult.resultType lowered.type) definitions)
    {context : SourceSemantics.Context} {scope : Scope} {position : Position} {expected : TypeSystem.Ty}
    (syntaxTree : UnarySyntax source context position expected)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {fuel : Nat} {type : Ty} {code : Expr} {selfReason : Word} {nativeType : Ty}
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : Accepted policy fuel source scope position type reasonAt selfReason code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType definitions) :
    Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative
      context scope position expected type code := by
  induction syntaxTree generalizing scope fuel code nativeType with
  | body syntaxTree => exact .body syntaxTree (TypedLexicalControl.tree_of_flow readPolicy binderPolicy allocationPolicy expressions syntaxTree closed residual sourceSignatures declarations projection accepted)
  | @uninitialized context nextContext mode id node binder rest expected found form declaration monomorphic extended ordinary remaining ih =>
    simp only [Accepted] at accepted
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
      exact .uninitialized found form monomorphic extended ordinary (binder_projected (binderPolicy scope binder monomorphic ▸ projected))
        allocation annotation same (ih (by cases extended; exact closed) (by cases extended; exact residual) (by cases extended; exact sourceSignatures)
          (scope_bind payload declarations declaration extended) projection generated (TypedLexicalWhile.Native.absent_child allocation annotation same nativeTyped))

  | @initialized context nextContext mode id node binder initializer initializerNode rest expected found form declaration mono extended ordinary initializerFound sourceType typed initializerSyntax remaining ih =>
    simp only [Accepted] at accepted
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
      exact .initialized found form mono extended ordinary initializerFound sourceType
        (expressions context closed residual sourceSignatures declarations initializerSyntax initializerFound typed generated)
        allocation annotation same
        (ih (by cases extended; exact closed) (by cases extended; exact residual) (by cases extended; exact sourceSignatures)
          (scope_bind lowered.type declarations declaration extended) projection generatedBody (TypedLexicalWhile.Native.initialized_child allocation annotation same nativeTyped))

  | @discard context mode id node expression expressionNode semicolon rest expected found form notTail sourceType expressionFound typed syntaxValue remaining ih =>
    simp only [Accepted] at accepted
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
        exact .discard found form notTail expressionFound (expressions context closed residual sourceSignatures declarations syntaxValue expressionFound typed generated)
          (ih closed residual sourceSignatures declarations projection generatedBody tailTyped)

  | @block context mode id node statements rest expected found form sourceType inner remaining innerIH restIH =>
    simp only [Accepted] at accepted
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
      exact .block found form (innerIH closed residual sourceSignatures declarations projection generatedInner headTyped) (restIH closed residual sourceSignatures declarations projection generatedBody tailTyped)
  | @ifThen context mode id node condition conditionNode thenBody elseBody rest expected found form sourceType conditionFound conditionType typed conditionSyntax thenSyntax elseSyntax remaining thenIH elseIH restIH =>
    simp only [Accepted] at accepted
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
        exact .ifThen found form conditionFound conditionType
          (expressions context closed residual sourceSignatures declarations conditionSyntax conditionFound typed generatedCondition)
          (thenIH closed residual sourceSignatures declarations projection generatedThen thenTyped) (elseIH closed residual sourceSignatures declarations projection generatedElse elseTyped) (restIH closed residual sourceSignatures declarations projection generatedBody tailTyped)
      | some statements =>
        obtain ⟨elseCode, generatedElse, accepted⟩ := bind_ok accepted
        obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
        cases accepted
        obtain ⟨⟨_, branchTyped⟩, ⟨_, tailTyped⟩⟩ := TypedLexicalWhile.Native.sequence_children nativeTyped
        obtain ⟨⟨_, thenTyped⟩, ⟨_, elseTyped⟩⟩ := TypedLexicalWhile.Native.conditional_children branchTyped
        exact .ifThen found form conditionFound conditionType
          (expressions context closed residual sourceSignatures declarations conditionSyntax conditionFound typed generatedCondition)
          (thenIH closed residual sourceSignatures declarations projection generatedThen thenTyped) (elseIH closed residual sourceSignatures declarations projection generatedElse elseTyped) (restIH closed residual sourceSignatures declarations projection generatedBody tailTyped)

  | @breaking context mode id node rest expected found form =>
    simp only [Accepted] at accepted
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
      exact .breaking found form
  | @continuing context mode id node rest expected found form =>
    simp only [Accepted] at accepted
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
      exact .continuing found form
  | @whileLoop context mode id node condition conditionNode statements rest expected found form conditionFound conditionType typed conditionSyntax loopSyntax remaining loopIH restIH =>
    simp only [Accepted] at accepted
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
      exact .whileLoop found form conditionFound conditionType
        (expressions context closed residual sourceSignatures declarations conditionSyntax conditionFound typed generatedCondition)
        (loopIH closed residual sourceSignatures declarations projection generatedLoop loopBodyTyped)
        loopTyped
        (restIH closed residual sourceSignatures declarations projection generatedBody tailTyped)

  | @assign context mode id node assignment operator rhs rest expected found form sourceTyped writable rightTyped profile remaining ih =>
    simp only [Accepted] at accepted
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
      obtain ⟨head, rfl⟩ := CompatibleAssignmentStatements.Head.of_lower unique sourceSignatures sourceTyped writable rightTyped profile
        (fun id lowered generated => assignmentExpressions context scope fuel id lowered closed residual sourceSignatures declarations generated) compiled nativeTyped
      exact .assign found form head (ih closed residual sourceSignatures declarations projection compiledBody (TypedImperative.Native.execute_continuation nativeTyped))

  | @forLoop context mode id node initializer condition post statements rest expected found form sourceType initial remaining initialIH restIH =>
    simp only [Accepted] at accepted
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
      apply Tree.forLoop found form
      · apply initialIH closed residual sourceSignatures declarations projection (nativeTyped := initialTyped)
        refine ⟨fuel, .occurrence id.occurrence, _, generatedInitial, ?_⟩
        intro loopScope nextCode generated
        obtain ⟨conditionCode, conditionGenerated, generated⟩ := bind_ok generated
        obtain ⟨checked, conditionChecked, generated⟩ := bind_ok generated
        cases checked
        obtain ⟨loopCode, loopGenerated, generated⟩ := bind_ok generated
        obtain ⟨postCode, postGenerated, generated⟩ := bind_ok generated
        cases generated
        exact ⟨conditionCode, loopCode, postCode, conditionGenerated, (unary_ensure_same conditionChecked).symm, loopGenerated, postGenerated, rfl⟩
      · exact restIH closed residual sourceSignatures declarations projection generatedBody tailTyped
  | @initializersDone context condition conditionNode post statements expected conditionFound conditionType typed conditionSyntax loopBody postSyntax loopIH =>
    obtain ⟨headerFuel, parentSite, next, generated, nextReceipt⟩ := accepted
    have nextAccepted : next scope = .ok code := by cases headerFuel <;> exact generated
    obtain ⟨conditionCode, loopCode, postCode, conditionGenerated, conditionChecked, loopGenerated, postGenerated, rfl⟩ :=
      nextReceipt scope code nextAccepted
    rcases conditionCode with ⟨native, expression⟩
    dsimp only at conditionChecked
    subst native
    obtain ⟨⟨_, bodyTyped⟩, ⟨_, postTyped⟩, loopTyped⟩ := Native.iterate_children nativeTyped
    exact .initializersDone conditionFound conditionType
      (expressions context closed residual sourceSignatures declarations conditionSyntax conditionFound typed conditionGenerated)
      (loopIH closed residual sourceSignatures declarations projection loopGenerated bodyTyped)
      (TypedForHeader.tree_of_lowerForItems_withBitNot binderPolicy allocationPolicy assignments unaryPolicy unique assignmentExpressions
        (fun _ _ _ _ _ _ _ same => by cases same; rfl) postSyntax closed residual sourceSignatures declarations postGenerated postTyped)
      loopTyped
  | @initializerUninitialized context nextContext binder rest condition post statements expected declaration monomorphic extended ordinary remaining ih =>
    obtain ⟨headerFuel, parentSite, next, accepted, nextReceipt⟩ := accepted
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
      exact .initializerUninitialized monomorphic extended ordinary (binder_projected (binderPolicy scope binder monomorphic ▸ projected))
        allocation annotation same (ih (by cases extended; exact closed) (by cases extended; exact residual) (by cases extended; exact sourceSignatures)
          (scope_bind payload declarations declaration extended) projection ⟨headerFuel, parentSite, next, generated, nextReceipt⟩ (TypedLexicalWhile.Native.absent_child allocation annotation same nativeTyped))
  | @initializerInitialized context nextContext binder initializer initializerNode rest condition post statements expected declaration mono extended ordinary initializerFound sourceType typed initializerSyntax remaining ih =>
    obtain ⟨headerFuel, parentSite, next, accepted, nextReceipt⟩ := accepted
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
      obtain ⟨actualNode, actualFound, initial, _⟩ := assignmentExpressions context scope headerFuel initializer lowered closed residual sourceSignatures declarations generated
      exact .initializerInitialized mono extended ordinary initializerFound sourceType initial allocation annotation same
        (ih (by cases extended; exact closed) (by cases extended; exact residual) (by cases extended; exact sourceSignatures)
          (scope_bind lowered.type declarations declaration extended) projection ⟨headerFuel, parentSite, next, generatedBody, nextReceipt⟩ (TypedLexicalWhile.Native.initialized_child allocation annotation same nativeTyped))
  | @initializerDiscard context expression expressionNode rest condition post statements expected found typed syntaxTree remaining ih =>
    obtain ⟨headerFuel, parentSite, next, accepted, nextReceipt⟩ := accepted
    cases headerFuel with
    | zero => cases accepted
    | succ headerFuel =>
      simp only [SourceCoreLoops.lowerForItems] at accepted
      obtain ⟨lowered, generated, accepted⟩ := bind_ok accepted
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨actualNode, actualFound, child, _⟩ := assignmentExpressions context scope headerFuel expression lowered closed residual sourceSignatures declarations generated
      obtain ⟨_, bodyTyped⟩ := TypedLexicalWhile.Native.discard_child nativeTyped
      exact .initializerDiscard found child (ih closed residual sourceSignatures declarations projection ⟨headerFuel, parentSite, next, generatedBody, nextReceipt⟩ bodyTyped)
  | @initializerAssign context assignment operator rhs rest condition post statements expected sourceTyped writable rightTyped profile remaining ih =>
    obtain ⟨headerFuel, parentSite, next, accepted, nextReceipt⟩ := accepted
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
      obtain ⟨head, rfl⟩ := CompatibleAssignmentStatements.Head.of_lower unique sourceSignatures sourceTyped writable rightTyped profile
        (fun id lowered generated => assignmentExpressions context scope headerFuel id lowered closed residual sourceSignatures declarations generated) compiled nativeTyped
      exact .initializerAssign head (ih closed residual sourceSignatures declarations projection ⟨headerFuel, parentSite, next, generatedBody, nextReceipt⟩ (TypedImperative.Native.execute_continuation nativeTyped))

  | @bitNot context mode id node assignment rest expected found form writable bare profile remaining ih =>
    simp only [Accepted] at accepted
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
      exact .bitNot found form head (ih closed residual sourceSignatures declarations projection compiledBody
        (TypedImperative.Native.execute_continuation nativeTyped))
  | @initializerBitNot context assignment rest condition post statements expected writable bare profile remaining ih =>
    obtain ⟨headerFuel, parentSite, next, generated, nextReceipt⟩ := accepted
    cases headerFuel with
    | zero => cases generated
    | succ headerFuel =>
      simp only [SourceCoreLoops.lowerForItems, unaryPolicy] at generated
      obtain ⟨body, generatedBody, generated⟩ := bind_ok generated
      obtain ⟨head, rfl⟩ := CompatibleBitNotStatements.Head.of_lower writable bare profile generated
      exact .initializerBitNot head (ih closed residual sourceSignatures declarations projection
        ⟨headerFuel, parentSite, next, generatedBody, nextReceipt⟩ (TypedImperative.Native.execute_continuation nativeTyped))


theorem tree_of_typed_flow_withBitNot
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      policy.lowerBinder source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked source scope binder)
    (allocationPolicy : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (expressions : ∀ sourceContext, sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = false →
      sourceContext.signatures = values.checked.signatures →
      ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations source scope sourceContext → CompatibleExpressionTyped.Syntax source id →
      source.lookupExpression? id = some node → ExpressionHasType source sourceContext id node.type →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
      CompatibleExpressionTyped.Tree readFuel values source sourceContext solved reasonAt scope id lowered)
    (assignments : CompatibleAssignmentStatements.AssignmentPolicy policy values invalidProjection invalidOperand missingDefault)
    (unaryPolicy : CompatibleBitNotStatements.Policy policy values invalidProjection invalidUnary missingDefault)
    (unique : NodeOccurrencesUnique source)
    (assignmentExpressions : ∀ sourceContext scope fuel id lowered,
      sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = false →
      sourceContext.signatures = values.checked.signatures →
      CompatibleExpressionReads.ScopeDeclarations source scope sourceContext →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered → ∃ node,
        source.lookupExpression? id = some node ∧
        CompatibleExpressionTyped.Tree readFuel values source sourceContext solved reasonAt scope id lowered ∧
        HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
          (LanguageResult.resultType lowered.type) definitions)
    {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {statements : List StatementId} {expected : TypeSystem.Ty}
    (syntaxTree : UnarySyntax source context (.statements mode statements) expected)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {fuel : Nat} {type : Ty} {code : Expr} {selfReason : Word} {nativeType : Ty}
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope statements type reasonAt mode selfReason = .ok code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType definitions) :
    Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative
      context scope (.statements mode statements) expected type code := by
  exact tree_of_typed_position_withBitNot readPolicy binderPolicy allocationPolicy expressions assignments unaryPolicy unique assignmentExpressions syntaxTree closed residual sourceSignatures declarations projection accepted nativeTyped

/-- The public statement wrapper's real typing exposes its enclosed flow.
This retains the exact emitted finish/toControl equation for body consumers. -/
theorem tree_of_typed_body_withBitNot
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      policy.lowerBinder source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked source scope binder)
    (allocationPolicy : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (expressions : ∀ sourceContext, sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = false →
      sourceContext.signatures = values.checked.signatures →
      ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations source scope sourceContext → CompatibleExpressionTyped.Syntax source id →
      source.lookupExpression? id = some node → ExpressionHasType source sourceContext id node.type →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
      CompatibleExpressionTyped.Tree readFuel values source sourceContext solved reasonAt scope id lowered)
    (assignments : CompatibleAssignmentStatements.AssignmentPolicy policy values invalidProjection invalidOperand missingDefault)
    (unaryPolicy : CompatibleBitNotStatements.Policy policy values invalidProjection invalidUnary missingDefault)
    (unique : NodeOccurrencesUnique source)
    (assignmentExpressions : ∀ sourceContext scope fuel id lowered,
      sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = false →
      sourceContext.signatures = values.checked.signatures →
      CompatibleExpressionReads.ScopeDeclarations source scope sourceContext →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered → ∃ node,
        source.lookupExpression? id = some node ∧
        CompatibleExpressionTyped.Tree readFuel values source sourceContext solved reasonAt scope id lowered ∧
        HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
          (LanguageResult.resultType lowered.type) definitions)
    {context : SourceSemantics.Context} {scope : Scope} {statements : List StatementId} {expected : TypeSystem.Ty}
    (syntaxTree : UnarySyntax source context (.statements true statements) expected)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {fuel : Nat} {type nativeType : Ty} {code : Expr} {fellThrough escaped : Word}
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope statements type reasonAt fellThrough escaped = .ok code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType definitions) :
    ∃ flow,
      SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope statements type reasonAt true escaped = .ok flow ∧
      Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative
        context scope (.statements true statements) expected type flow ∧
      code = LocalControl.finish type (LocalLoop.toControl type flow escaped)
        (if type = .unit then LanguageResult.success .unit else LanguageResult.failure type (.word fellThrough)) := by
  unfold SourceCoreLoops.lowerStatementsWithPolicy at accepted
  obtain ⟨flow, generated, same⟩ := bind_ok accepted
  cases same
  obtain ⟨_, flowTyped⟩ := TypedLexicalWhile.Native.finished_flow nativeTyped
  exact ⟨flow, generated, tree_of_typed_flow_withBitNot readPolicy binderPolicy allocationPolicy expressions
    assignments unaryPolicy unique assignmentExpressions syntaxTree closed residual sourceSignatures declarations projection generated flowTyped, rfl⟩

end Solcore.SourceSemantics.CoreLowering.TypedImperativeFor
end
