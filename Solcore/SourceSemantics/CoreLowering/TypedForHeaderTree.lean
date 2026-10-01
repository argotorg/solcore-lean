import Solcore.SourceSemantics.CoreLowering.CompatibleBitNotStatementComposition
import Solcore.SourceSemantics.CoreLowering.TypedImperativeMeaning
import Solcore.SourceSemantics.CoreLowering.TypedImperativeCertificates

/-! Static ordinary for headers thread their lexical scope to a syntactic
continuation. Initializers and post vectors use the same marked allocation
and compatible assignment receipts; no execution belongs to a tree. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.TypedForHeader
open Core Frontend SourceInference
abbrev Scope := SourceCoreLocalCell.Scope
abbrev ValuesContext := SourceCoreCompatibleValues.Context
open TypedLexicalWhile (absentRequest initializedRequest sequence)

inductive Syntax (source : TypedSource) : SourceSemantics.Context → List ForItemForm → Prop where
  | nil {context} : Syntax source context []
  | uninitialized {context nextContext binder rest}
      (declaration : SourceCoreDataPlaces.rootBinder source binder.id = .ok binder)
      (monomorphic : binder.scheme.quantified = [])
      (extended : BinderExtends source.owner context binder nextContext)
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (remaining : Syntax source nextContext rest) : Syntax source context (.letDecl binder none :: rest)
  | initialized {context nextContext binder initializer initializerNode rest}
      (declaration : SourceCoreDataPlaces.rootBinder source binder.id = .ok binder)
      (monomorphic : binder.scheme.quantified = [])
      (extended : BinderExtends source.owner context binder nextContext)
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (initializerFound : source.lookupExpression? initializer = some initializerNode)
      (sourceType : initializerNode.type = binder.scheme.body)
      (initializerTyped : ExpressionHasType source context initializer initializerNode.type)
      (initializerSyntax : CompatibleExpressionTyped.Syntax source initializer)
      (remaining : Syntax source nextContext rest) : Syntax source context (.letDecl binder (some initializer) :: rest)
  | discard {context expression expressionNode rest}
      (found : source.lookupExpression? expression = some expressionNode)
      (typed : ExpressionHasType source context expression expressionNode.type)
      (syntaxTree : CompatibleExpressionTyped.Syntax source expression)
      (remaining : Syntax source context rest) : Syntax source context (.expression expression :: rest)
  | assign {context assignment operator rhs rest}
      (sourceTyped : ∀ binder, SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder →
        SourceProjectionsHaveType source context binder.scheme.body assignment.target.projections assignment.target.type)
      (writable : ∀ binder, SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder →
        WritableLocal context assignment.target.root binder.scheme.body)
      (rightTyped : ExpressionHasType source context rhs assignment.target.type)
      (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
        SourceCoreRawMetadata.runtimeType assignment.target.type = .integer)
      (remaining : Syntax source context rest) : Syntax source context (.assignValue assignment operator rhs :: rest)

inductive Tree (layouts : SourceCoreAllocationLayouts.Prepared)
    (owner : SourceSpecialization.SpecializationKey) (active : TypeSystem.Substitution)
    (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (readFuel : Nat) (values : ValuesContext) (source : TypedSource)
    (solved : List SolvedRequirement) (reasonAt : ExpressionId → Word)
    (definitions : DataEnvironment) (administrative : Core.Context) (type : Ty)
    (continuation : SourceSemantics.Context → Scope → Expr → Prop) :
    SourceSemantics.Context → Scope → List ForItemForm → Expr → Prop where
  | nil {context scope code} (next : continuation context scope code) :
      Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative type continuation
        context scope [] code
  | uninitialized {context nextContext scope binder rest body payload}
      (monomorphic : binder.scheme.quantified = [])
      (extended : BinderExtends source.owner context binder nextContext)
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (projected : values.checked.catalog.project binder.scheme.body = .ok payload)
      (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (absentRequest source scope binder payload))
      (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
        (layouts.allocatorAt owner active onError) (absentRequest source scope binder payload))
      (same : annotation.original = allocation.expression)
      (remaining : Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative type continuation
        nextContext ((binder.id, payload) :: scope) rest body) :
      Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative type continuation
        context scope (.letDecl binder none :: rest) (.letE annotation.expression body)
  | initialized {context nextContext scope binder initializer initializerNode lowered body rest}
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
      (remaining : Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative type continuation
        nextContext ((binder.id, lowered.type) :: scope) rest body) :
      Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative type continuation
        context scope (.letDecl binder (some initializer) :: rest) (sequence type lowered.expression annotation.expression body)
  | discard {context scope expression expressionNode rest lowered body}
      (found : source.lookupExpression? expression = some expressionNode)
      (value : CompatibleExpressionTyped.Tree readFuel values source context solved reasonAt scope expression lowered)
      (remaining : Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative type continuation
        context scope rest body) :
      Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative type continuation
        context scope (.expression expression :: rest) (LocalSequence.discard (LocalLoop.controlType type) lowered.expression body)
  | assign {context scope assignment operator rhs rest body}
      (head : CompatibleAssignmentStatements.Head readFuel values source context solved reasonAt scope administrative definitions assignment operator rhs)
      (remaining : Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative type continuation
        context scope rest body) :
      Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative type continuation
        context scope (.assignValue assignment operator rhs :: rest) (head.emit body (LocalLoop.controlType type))

  | bitNot {context scope assignment rest body}
      (head : CompatibleBitNotStatements.Head context scope assignment)
      (remaining : Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative type continuation
        context scope rest body) :
      Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative type continuation
        context scope (.assignBitNot assignment :: rest) (head.emit body (LocalLoop.controlType type))

namespace Tree
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {readFuel : Nat} {values : ValuesContext} {source : TypedSource} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {definitions : DataEnvironment} {administrative : Core.Context}
  {type : Ty} {continuation : SourceSemantics.Context → Scope → Expr → Prop}

inductive Errors (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) :
    {context : SourceSemantics.Context} → {scope : Scope} → {items : List ForItemForm} → {code : Expr} →
    Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative type continuation
      context scope items code → Prop where
  | nil {context scope code}
      {next : continuation context scope code}
      : Errors registry faults (.nil next)
  | uninitialized {context nextContext scope binder rest body payload}
      {monomorphic : binder.scheme.quantified = []}
      {extended : BinderExtends source.owner context binder nextContext}
      {ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false}
      {projected : values.checked.catalog.project binder.scheme.body = .ok payload}
      {allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (absentRequest source scope binder payload)}
      {annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
        (layouts.allocatorAt owner active onError) (absentRequest source scope binder payload)}
      {same : annotation.original = allocation.expression}
      {remaining : Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative type continuation
        nextContext ((binder.id, payload) :: scope) rest body}
      (remainingErrors : Errors registry faults remaining)
      : Errors registry faults (.uninitialized monomorphic extended ordinary projected allocation annotation same remaining)
  | initialized {context nextContext scope binder initializer initializerNode lowered body rest}
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
      {remaining : Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative type continuation
        nextContext ((binder.id, lowered.type) :: scope) rest body}
      (remainingErrors : Errors registry faults remaining)
      : Errors registry faults (.initialized monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining)
  | discard {context scope expression expressionNode rest lowered body}
      {found : source.lookupExpression? expression = some expressionNode}
      {value : CompatibleExpressionTyped.Tree readFuel values source context solved reasonAt scope expression lowered}
      {remaining : Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative type continuation
        context scope rest body}
      (remainingErrors : Errors registry faults remaining)
      : Errors registry faults (.discard found value remaining)
  | assign {context scope assignment operator rhs rest body}
      {head : CompatibleAssignmentStatements.Head readFuel values source context solved reasonAt scope administrative definitions assignment operator rhs}
      {remaining : Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative type continuation
        context scope rest body}
      (remainingErrors : Errors registry faults remaining)
      (headErrors : head.Errors registry faults)
      : Errors registry faults (.assign head remaining)
  | bitNot {context scope assignment rest body}
      {head : CompatibleBitNotStatements.Head context scope assignment}
      {remaining : Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative type continuation
        context scope rest body}
      (remainingErrors : Errors registry faults remaining)
      (headErrors : head.Errors faults)
      : Errors registry faults (.bitNot head remaining)
end Tree
end Solcore.SourceSemantics.CoreLowering.TypedForHeader
