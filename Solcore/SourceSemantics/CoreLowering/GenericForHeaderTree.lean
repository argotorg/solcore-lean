import Solcore.SourceSemantics.CoreLowering.AssignmentDiagnosticPolicy
import Solcore.SourceSemantics.CoreLowering.CompatibleBitNotStatementComposition
import Solcore.SourceSemantics.CoreLowering.TypedImperativeMeaning
import Solcore.SourceSemantics.CoreLowering.TypedImperativeCertificates
import Solcore.SourceSemantics.CoreLowering.GenericAssignmentStatementCertificates
import Solcore.SourceSemantics.CoreLowering.GenericAssignmentStatementMeaning

/-! Static ordinary for headers thread their lexical scope to a syntactic
continuation. Initializers and post vectors use the same marked allocation
and compatible assignment receipts; no execution belongs to a tree. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericForHeader
open Core Frontend SourceInference
abbrev Scope := SourceCoreLocalCell.Scope
abbrev ValuesContext := SourceCoreCompatibleValues.Context
open TypedLexicalWhile (absentRequest initializedRequest sequence)

inductive Syntax (source : TypedSource) (expressionSyntax : ExpressionId → Prop) : SourceSemantics.Context → List ForItemForm → Prop where
  | nil {context} : Syntax source expressionSyntax context []
  | uninitialized {context nextContext binder rest}
      (declaration : SourceCoreDataPlaces.rootBinder source binder.id = .ok binder)
      (monomorphic : binder.scheme.quantified = [])
      (extended : BinderExtends source.owner context binder nextContext)
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (remaining : Syntax source expressionSyntax nextContext rest) : Syntax source expressionSyntax context (.letDecl binder none :: rest)
  | initialized {context nextContext binder initializer initializerNode rest}
      (declaration : SourceCoreDataPlaces.rootBinder source binder.id = .ok binder)
      (monomorphic : binder.scheme.quantified = [])
      (extended : BinderExtends source.owner context binder nextContext)
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (initializerFound : source.lookupExpression? initializer = some initializerNode)
      (sourceType : initializerNode.type = binder.scheme.body)
      (initializerTyped : ExpressionHasType source context initializer initializerNode.type)
      (initializerSyntax : expressionSyntax initializer)
      (remaining : Syntax source expressionSyntax nextContext rest) : Syntax source expressionSyntax context (.letDecl binder (some initializer) :: rest)
  | discard {context expression expressionNode rest}
      (found : source.lookupExpression? expression = some expressionNode)
      (typed : ExpressionHasType source context expression expressionNode.type)
      (syntaxTree : expressionSyntax expression)
      (remaining : Syntax source expressionSyntax context rest) : Syntax source expressionSyntax context (.expression expression :: rest)
  | assign {context assignment operator rhs rest}
      (sourceTyped : ∀ binder, SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder →
        SourceProjectionsHaveType source context binder.scheme.body assignment.target.projections assignment.target.type)
      (writable : ∀ binder, SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder →
        WritableLocal context assignment.target.root binder.scheme.body)
      (rightTyped : ExpressionHasType source context rhs assignment.target.type)
      (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
        SourceCoreRawMetadata.runtimeType assignment.target.type = .integer)
      (children : ∀ id, id ∈ rhs :: DataPlaceKeyOrder.sourceKeys assignment.target.projections →
        expressionSyntax id ∧ ∃ node, source.lookupExpression? id = some node ∧ ExpressionHasType source context id node.type)
      (remaining : Syntax source expressionSyntax context rest) : Syntax source expressionSyntax context (.assignValue assignment operator rhs :: rest)
  | bitNot {context assignment rest}
      (writable : ∀ binder, SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder →
        WritableLocal context assignment.target.root binder.scheme.body)
      (bare : assignment.target.projections = [])
      (profile : SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
        SourceCoreRawMetadata.runtimeType assignment.target.type = .integer)
      (remaining : Syntax source expressionSyntax context rest) : Syntax source expressionSyntax context (.assignBitNot assignment :: rest)


inductive Tree (layouts : SourceCoreAllocationLayouts.Prepared)
    (owner : SourceSpecialization.SpecializationKey) (active : TypeSystem.Substitution)
    (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (values : ValuesContext) (source : TypedSource)
    (certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate)
    (definitions : DataEnvironment) (administrative : Core.Context) (type : Ty)
    (continuation : SourceSemantics.Context → Scope → Expr → Prop) :
    SourceSemantics.Context → Scope → List ForItemForm → Expr → Prop where
  | nil {context scope code} (next : continuation context scope code) :
      Tree layouts owner active frame globals onError values source certificates definitions administrative type continuation
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
      (remaining : Tree layouts owner active frame globals onError values source certificates definitions administrative type continuation
        nextContext ((binder.id, payload) :: scope) rest body) :
      Tree layouts owner active frame globals onError values source certificates definitions administrative type continuation
        context scope (.letDecl binder none :: rest) (.letE annotation.expression body)
  | initialized {context nextContext scope binder initializer initializerNode lowered body rest}
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
      (remaining : Tree layouts owner active frame globals onError values source certificates definitions administrative type continuation
        nextContext ((binder.id, lowered.type) :: scope) rest body) :
      Tree layouts owner active frame globals onError values source certificates definitions administrative type continuation
        context scope (.letDecl binder (some initializer) :: rest) (sequence type lowered.expression annotation.expression body)
  | discard {context scope expression expressionNode rest lowered body}
      (found : source.lookupExpression? expression = some expressionNode)
      (value : certificates context scope expression lowered)
      (remaining : Tree layouts owner active frame globals onError values source certificates definitions administrative type continuation
        context scope rest body) :
      Tree layouts owner active frame globals onError values source certificates definitions administrative type continuation
        context scope (.expression expression :: rest) (LocalSequence.discard (LocalLoop.controlType type) lowered.expression body)
  | assign {context scope assignment operator rhs rest body}
      (head : GenericAssignmentStatements.Head values source context (certificates context) scope administrative definitions assignment operator rhs)
      (remaining : Tree layouts owner active frame globals onError values source certificates definitions administrative type continuation
        context scope rest body) :
      Tree layouts owner active frame globals onError values source certificates definitions administrative type continuation
        context scope (.assignValue assignment operator rhs :: rest) (head.emit body (LocalLoop.controlType type))

  | bitNot {context scope assignment rest body}
      (head : CompatibleBitNotStatements.Head context scope assignment)
      (remaining : Tree layouts owner active frame globals onError values source certificates definitions administrative type continuation
        context scope rest body) :
      Tree layouts owner active frame globals onError values source certificates definitions administrative type continuation
        context scope (.assignBitNot assignment :: rest) (head.emit body (LocalLoop.controlType type))

namespace Tree
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate} {definitions : DataEnvironment} {administrative : Core.Context}
  {type : Ty} {continuation : SourceSemantics.Context → Scope → Expr → Prop}

inductive ErrorsFor (policy : AssignmentDiagnosticPolicy) (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) :
    {context : SourceSemantics.Context} → {scope : Scope} → {items : List ForItemForm} → {code : Expr} →
    Tree layouts owner active frame globals onError values source certificates definitions administrative type continuation
      context scope items code → Prop where
  | nil {context scope code}
      {next : continuation context scope code}
      : ErrorsFor policy registry faults (.nil next)
  | uninitialized {context nextContext scope binder rest body payload}
      {monomorphic : binder.scheme.quantified = []}
      {extended : BinderExtends source.owner context binder nextContext}
      {ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false}
      {projected : values.checked.catalog.project binder.scheme.body = .ok payload}
      {allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (absentRequest source scope binder payload)}
      {annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
        (layouts.allocatorAt owner active onError) (absentRequest source scope binder payload)}
      {same : annotation.original = allocation.expression}
      {remaining : Tree layouts owner active frame globals onError values source certificates definitions administrative type continuation
        nextContext ((binder.id, payload) :: scope) rest body}
      (remainingErrors : ErrorsFor policy registry faults remaining)
      : ErrorsFor policy registry faults (.uninitialized monomorphic extended ordinary projected allocation annotation same remaining)
  | initialized {context nextContext scope binder initializer initializerNode lowered body rest}
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
      {remaining : Tree layouts owner active frame globals onError values source certificates definitions administrative type continuation
        nextContext ((binder.id, lowered.type) :: scope) rest body}
      (remainingErrors : ErrorsFor policy registry faults remaining)
      : ErrorsFor policy registry faults (.initialized monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining)
  | discard {context scope expression expressionNode rest lowered body}
      {found : source.lookupExpression? expression = some expressionNode}
      {value : certificates context scope expression lowered}
      {remaining : Tree layouts owner active frame globals onError values source certificates definitions administrative type continuation
        context scope rest body}
      (remainingErrors : ErrorsFor policy registry faults remaining)
      : ErrorsFor policy registry faults (.discard found value remaining)
  | assign {context scope assignment operator rhs rest body}
      {head : GenericAssignmentStatements.Head values source context (certificates context) scope administrative definitions assignment operator rhs}
      {remaining : Tree layouts owner active frame globals onError values source certificates definitions administrative type continuation
        context scope rest body}
      (remainingErrors : ErrorsFor policy registry faults remaining)
      (headErrors : head.ErrorsFor policy registry faults)
      : ErrorsFor policy registry faults (.assign head remaining)
  | bitNot {context scope assignment rest body}
      {head : CompatibleBitNotStatements.Head context scope assignment}
      {remaining : Tree layouts owner active frame globals onError values source certificates definitions administrative type continuation
        context scope rest body}
      (remainingErrors : ErrorsFor policy registry faults remaining)
      (headErrors : head.Errors faults)
      : ErrorsFor policy registry faults (.bitNot head remaining)

/-- Original diagnostic receipt, with its public parameter order unchanged. -/
abbrev Errors (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    {context : SourceSemantics.Context} {scope : Scope} {items : List ForItemForm} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source certificates definitions administrative type continuation
      context scope items code) : Prop := ErrorsFor .unconditional registry faults tree

/-- Only reachable operand failures require a token interpretation. -/
abbrev ReachableErrors (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    {context : SourceSemantics.Context} {scope : Scope} {items : List ForItemForm} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source certificates definitions administrative type continuation
      context scope items code) : Prop := ErrorsFor .reachable registry faults tree

namespace Errors
variable {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

abbrev nil {context scope code}
      {next : continuation context scope code}
      : Errors (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (certificates := certificates) (definitions := definitions) (administrative := administrative) (type := type) (continuation := continuation) registry faults (.nil next) :=
  @ErrorsFor.nil layouts owner active frame globals onError values source certificates definitions administrative type continuation .unconditional registry faults context scope code next

abbrev uninitialized {context nextContext scope binder rest body payload}
      {monomorphic : binder.scheme.quantified = []}
      {extended : BinderExtends source.owner context binder nextContext}
      {ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false}
      {projected : values.checked.catalog.project binder.scheme.body = .ok payload}
      {allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (absentRequest source scope binder payload)}
      {annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
        (layouts.allocatorAt owner active onError) (absentRequest source scope binder payload)}
      {same : annotation.original = allocation.expression}
      {remaining : Tree layouts owner active frame globals onError values source certificates definitions administrative type continuation
        nextContext ((binder.id, payload) :: scope) rest body}
      (remainingErrors : Errors (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (certificates := certificates) (definitions := definitions) (administrative := administrative) (type := type) (continuation := continuation) registry faults remaining)
      : Errors (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (certificates := certificates) (definitions := definitions) (administrative := administrative) (type := type) (continuation := continuation) registry faults (.uninitialized monomorphic extended ordinary projected allocation annotation same remaining) :=
  @ErrorsFor.uninitialized layouts owner active frame globals onError values source certificates definitions administrative type continuation .unconditional registry faults context nextContext scope binder rest body payload monomorphic extended ordinary projected allocation annotation same remaining remainingErrors

abbrev initialized {context nextContext scope binder initializer initializerNode lowered body rest}
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
      {remaining : Tree layouts owner active frame globals onError values source certificates definitions administrative type continuation
        nextContext ((binder.id, lowered.type) :: scope) rest body}
      (remainingErrors : Errors (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (certificates := certificates) (definitions := definitions) (administrative := administrative) (type := type) (continuation := continuation) registry faults remaining)
      : Errors (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (certificates := certificates) (definitions := definitions) (administrative := administrative) (type := type) (continuation := continuation) registry faults (.initialized monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining) :=
  @ErrorsFor.initialized layouts owner active frame globals onError values source certificates definitions administrative type continuation .unconditional registry faults context nextContext scope binder initializer initializerNode lowered body rest monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining remainingErrors

abbrev discard {context scope expression expressionNode rest lowered body}
      {found : source.lookupExpression? expression = some expressionNode}
      {value : certificates context scope expression lowered}
      {remaining : Tree layouts owner active frame globals onError values source certificates definitions administrative type continuation
        context scope rest body}
      (remainingErrors : Errors (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (certificates := certificates) (definitions := definitions) (administrative := administrative) (type := type) (continuation := continuation) registry faults remaining)
      : Errors (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (certificates := certificates) (definitions := definitions) (administrative := administrative) (type := type) (continuation := continuation) registry faults (.discard found value remaining) :=
  @ErrorsFor.discard layouts owner active frame globals onError values source certificates definitions administrative type continuation .unconditional registry faults context scope expression expressionNode rest lowered body found value remaining remainingErrors

abbrev assign {context scope assignment operator rhs rest body}
      {head : GenericAssignmentStatements.Head values source context (certificates context) scope administrative definitions assignment operator rhs}
      {remaining : Tree layouts owner active frame globals onError values source certificates definitions administrative type continuation
        context scope rest body}
      (remainingErrors : Errors (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (certificates := certificates) (definitions := definitions) (administrative := administrative) (type := type) (continuation := continuation) registry faults remaining)
      (headErrors : head.Errors registry faults)
      : Errors (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (certificates := certificates) (definitions := definitions) (administrative := administrative) (type := type) (continuation := continuation) registry faults (.assign head remaining) :=
  @ErrorsFor.assign layouts owner active frame globals onError values source certificates definitions administrative type continuation .unconditional registry faults context scope assignment operator rhs rest body head remaining remainingErrors headErrors

abbrev bitNot {context scope assignment rest body}
      {head : CompatibleBitNotStatements.Head context scope assignment}
      {remaining : Tree layouts owner active frame globals onError values source certificates definitions administrative type continuation
        context scope rest body}
      (remainingErrors : Errors (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (certificates := certificates) (definitions := definitions) (administrative := administrative) (type := type) (continuation := continuation) registry faults remaining)
      (headErrors : head.Errors faults)
      : Errors (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (certificates := certificates) (definitions := definitions) (administrative := administrative) (type := type) (continuation := continuation) registry faults (.bitNot head remaining) :=
  @ErrorsFor.bitNot layouts owner active frame globals onError values source certificates definitions administrative type continuation .unconditional registry faults context scope assignment rest body head remaining remainingErrors headErrors

end Errors

theorem Errors.reachable {context : SourceSemantics.Context} {scope : Scope} {items : List ForItemForm} {code : Expr}
    {tree : Tree layouts owner active frame globals onError values source certificates definitions administrative type continuation
      context scope items code}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (errors : Errors registry faults tree) : ReachableErrors registry faults tree := by
  induction errors with
  | @nil context scope code next =>
    exact @ErrorsFor.nil layouts owner active frame globals onError values source certificates definitions administrative type continuation .reachable registry faults context scope code next
  | @uninitialized context nextContext scope binder rest body payload monomorphic extended ordinary projected allocation annotation same remaining remainingErrors ih =>
    exact @ErrorsFor.uninitialized layouts owner active frame globals onError values source certificates definitions administrative type continuation .reachable registry faults context nextContext scope binder rest body payload monomorphic extended ordinary projected allocation annotation same remaining ih
  | @initialized context nextContext scope binder initializer initializerNode lowered body rest monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining remainingErrors ih =>
    exact @ErrorsFor.initialized layouts owner active frame globals onError values source certificates definitions administrative type continuation .reachable registry faults context nextContext scope binder initializer initializerNode lowered body rest monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining ih
  | @discard context scope expression expressionNode rest lowered body found value remaining remainingErrors ih =>
    exact @ErrorsFor.discard layouts owner active frame globals onError values source certificates definitions administrative type continuation .reachable registry faults context scope expression expressionNode rest lowered body found value remaining ih
  | @assign context scope assignment operator rhs rest body head remaining remainingErrors headErrors ih =>
    exact @ErrorsFor.assign layouts owner active frame globals onError values source certificates definitions administrative type continuation .reachable registry faults context scope assignment operator rhs rest body head remaining ih (GenericAssignmentStatements.Head.ErrorsFor.reachable headErrors)
  | @bitNot context scope assignment rest body head remaining remainingErrors headErrors ih =>
    exact @ErrorsFor.bitNot layouts owner active frame globals onError values source certificates definitions administrative type continuation .reachable registry faults context scope assignment rest body head remaining ih headErrors

end Tree
end Solcore.SourceSemantics.CoreLowering.GenericForHeader
