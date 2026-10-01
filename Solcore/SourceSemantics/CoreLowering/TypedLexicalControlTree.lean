import Solcore.SourceSemantics.CoreLowering.TypedStatementMixedMeaning
import Solcore.SourceSemantics.CoreLowering.TypedScopedControlMeaning

/-! Ordinary monomorphic lexical bindings and typed scoped control at every
list position. Scoped bodies return to their enclosing lexical context while
their allocated cells and expression effects remain in the heap. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.TypedLexicalControl
open Core Frontend SourceInference
abbrev Scope := SourceCoreLocalCell.Scope
abbrev ValuesContext := SourceCoreCompatibleValues.Context

abbrev absentRequest (source : TypedSource) (scope : Scope) (binder : TypedBinder) (payload : Ty) :
    SourceCoreSourceCells.Request := ⟨source, scope, Renaming.id, binder, payload, none⟩

abbrev initializedRequest := CompatibleStatementInitialized.request
abbrev sequence := CompatibleStatementInitialized.sequence

inductive Syntax (source : TypedSource) :
    SourceSemantics.Context → Bool → List StatementId → TypeSystem.Ty → Prop where
  | body {context mode statements expected} (syntaxTree : TypedScopedStatements.Syntax source context mode statements expected) :
      Syntax source context mode statements expected
  | uninitialized {context nextContext mode id node binder rest expected}
      (found : source.lookupStatement? id = some node) (form : node.form = .letDecl binder none)
      (declaration : SourceCoreDataPlaces.rootBinder source binder.id = .ok binder)
      (monomorphic : binder.scheme.quantified = [])
      (extended : BinderExtends source.owner context binder nextContext)
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (remaining : Syntax source nextContext mode rest expected) :
      Syntax source context mode (id :: rest) expected

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
      (remaining : Syntax source nextContext mode rest expected) :
      Syntax source context mode (id :: rest) expected
  | discard {context mode id node expression expressionNode semicolon rest expected}
      (found : source.lookupStatement? id = some node) (form : node.form = .expression expression semicolon)
      (notTail : (!semicolon && mode && rest.isEmpty) = false)
      (sourceType : node.type = if semicolon then .unit else expressionNode.type)
      (expressionFound : source.lookupExpression? expression = some expressionNode)
      (typed : ExpressionHasType source context expression expressionNode.type)
      (value : CompatibleExpressionTyped.Syntax source expression)
      (remaining : Syntax source context mode rest expected) : Syntax source context mode (id :: rest) expected
  | block {context mode id node statements rest expected}
      (found : source.lookupStatement? id = some node) (form : node.form = .block statements)
      (sourceType : node.type = .unit)
      (inner : Syntax source context false statements expected)
      (remaining : Syntax source context mode rest expected) : Syntax source context mode (id :: rest) expected
  | ifThen {context mode id node condition conditionNode thenBody elseBody rest expected}
      (found : source.lookupStatement? id = some node) (form : node.form = .ifThen condition thenBody elseBody)
      (sourceType : node.type = .unit)
      (conditionFound : source.lookupExpression? condition = some conditionNode)
      (conditionType : conditionNode.type = .bool)
      (typed : ExpressionHasType source context condition conditionNode.type)
      (conditionSyntax : CompatibleExpressionTyped.Syntax source condition)
      (thenSyntax : Syntax source context false thenBody expected)
      (elseSyntax : Syntax source context false (elseBody.getD []) expected)
      (remaining : Syntax source context mode rest expected) : Syntax source context mode (id :: rest) expected

inductive Tree (layouts : SourceCoreAllocationLayouts.Prepared)
    (owner : SourceSpecialization.SpecializationKey) (active : TypeSystem.Substitution)
    (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (readFuel : Nat) (values : ValuesContext) (source : TypedSource)
    (solved : List SolvedRequirement)
    (reasonAt : ExpressionId → Word) :
    SourceSemantics.Context → Scope → Bool → List StatementId → TypeSystem.Ty → Ty → Expr → Prop where
  | body {context scope mode statements expected type code}
      (body : TypedScopedStatements.Tree readFuel values source context solved reasonAt scope mode statements expected type code) :
      Tree layouts owner active frame globals onError readFuel values source solved reasonAt
        context scope mode statements expected type code
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
      (remaining : Tree layouts owner active frame globals onError readFuel values source solved reasonAt
        nextContext ((binder.id, payload) :: scope) mode rest expected type body) :
      Tree layouts owner active frame globals onError readFuel values source solved reasonAt
        context scope mode (id :: rest) expected type (.letE annotation.expression body)
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
        solved reasonAt nextContext ((binder.id, lowered.type) :: scope) mode rest expected type body) :
      Tree layouts owner active frame globals onError readFuel values source solved reasonAt
        context scope mode (id :: rest) expected type (sequence type lowered.expression annotation.expression body)

  | discard {context scope mode id node expression expressionNode semicolon rest expected lowered type body}
      (found : source.lookupStatement? id = some node) (form : node.form = .expression expression semicolon)
      (notTail : (!semicolon && mode && rest.isEmpty) = false)
      (expressionFound : source.lookupExpression? expression = some expressionNode)
      (value : CompatibleExpressionTyped.Tree readFuel values source context solved reasonAt scope expression lowered)
      (remaining : Tree layouts owner active frame globals onError readFuel values source solved reasonAt context scope mode rest expected type body) :
      Tree layouts owner active frame globals onError readFuel values source solved reasonAt context scope mode (id :: rest) expected type
        (LocalSequence.discard (LocalLoop.controlType type) lowered.expression body)
  | block {context scope mode id node statements rest expected type innerCode body}
      (found : source.lookupStatement? id = some node) (form : node.form = .block statements)
      (inner : Tree layouts owner active frame globals onError readFuel values source solved reasonAt context scope false statements expected type innerCode)
      (remaining : Tree layouts owner active frame globals onError readFuel values source solved reasonAt context scope mode rest expected type body) :
      Tree layouts owner active frame globals onError readFuel values source solved reasonAt context scope mode (id :: rest) expected type
        (LocalLoop.sequence type innerCode body)
  | ifThen {context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body}
      (found : source.lookupStatement? id = some node) (form : node.form = .ifThen condition thenBody elseBody)
      (conditionFound : source.lookupExpression? condition = some conditionNode)
      (conditionType : conditionNode.type = .bool)
      (conditionTree : CompatibleExpressionTyped.Tree readFuel values source context solved reasonAt scope condition ⟨.bool, conditionCode⟩)
      (thenTree : Tree layouts owner active frame globals onError readFuel values source solved reasonAt context scope false thenBody expected type thenCode)
      (elseTree : Tree layouts owner active frame globals onError readFuel values source solved reasonAt context scope false (elseBody.getD []) expected type elseCode)
      (remaining : Tree layouts owner active frame globals onError readFuel values source solved reasonAt context scope mode rest expected type body) :
      Tree layouts owner active frame globals onError readFuel values source solved reasonAt context scope mode (id :: rest) expected type
        (LocalLoop.sequence type (LocalLoop.conditional type conditionCode thenCode elseCode) body)

/-- Reuse the existing result-dependent lexical stopping relation. -/
abbrev Reached := CompatibleStatementMixed.Reached

end Solcore.SourceSemantics.CoreLowering.TypedLexicalControl
