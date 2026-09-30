import Solcore.SourceSemantics.CoreLowering.LoopStatementTree

/-! Static certificates for the default scalar/product `for` header compiler.
A header threads binder scope and source context into a static continuation.
The continuation predicate contains syntax certificates only; no source/Core
execution or termination witness is part of this tree. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.ForHeaders

open Frontend Frontend.SourceInference TypeSystem LocalCell BasicStatements

/-- A header can allocate ordinary scalar/product locals, assign a bare local
with `=`, or discard a primitive expression. Its continuation is indexed by
the resulting lexical scope and context, so initializer bindings remain in
scope for the loop and post bindings can be discharged after each iteration. -/
inductive Tree (compilation : SourceCorePrimitive.Context) (source : TypedSource)
    (reasonAt : ExpressionId → Core.Word) (resultType : Core.Ty)
    (continuation : SourceCoreLocalCell.Scope → Context → Core.Expr → Prop) :
    SourceCoreLocalCell.Scope → Context → List ForItemForm → Core.Expr → Prop where
  | nil {scope context code}
      (next : continuation scope context code) :
      Tree compilation source reasonAt resultType continuation scope context [] code
  | letUninitialized {scope context middleContext binder rest payloadType body}
      (binding : BinderCertificate source scope binder payloadType)
      (extension : BinderExtends source.owner context binder middleContext)
      (tail : Tree compilation source reasonAt resultType continuation
        ((binder.id, payloadType) :: scope) middleContext rest body) :
      Tree compilation source reasonAt resultType continuation scope context (.letDecl binder none :: rest)
        (Core.LocalSequence.letUninitialized payloadType body)
  | letInitialized {scope context middleContext binder rest payloadType initializer initializerCode body depth}
      (binding : BinderCertificate source scope binder payloadType)
      (extension : BinderExtends source.owner context binder middleContext)
      (value : PrimitiveExpressions.Tree compilation source scope reasonAt initializer payloadType initializerCode depth)
      (tail : Tree compilation source reasonAt resultType continuation
        ((binder.id, payloadType) :: scope) middleContext rest body) :
      Tree compilation source reasonAt resultType continuation scope context (.letDecl binder (some initializer) :: rest)
        (Core.LocalSequence.letInitialized (Core.LocalLoop.controlType resultType) payloadType initializerCode body)
  | assign {scope context assignment index payloadType rhs rhsCode rest body depth}
      (target : AssignmentCertificate source scope assignment .equal index payloadType)
      (value : PrimitiveExpressions.Tree compilation source scope reasonAt rhs payloadType rhsCode depth)
      (tail : Tree compilation source reasonAt resultType continuation scope context rest body) :
      Tree compilation source reasonAt resultType continuation scope context (.assignValue assignment .equal rhs :: rest)
        (Core.LocalSequence.assign (Core.LocalLoop.controlType resultType) (.var index) rhsCode body)
  | discard {scope context expression expressionType expressionCode rest body depth}
      (value : PrimitiveExpressions.Tree compilation source scope reasonAt expression expressionType expressionCode depth)
      (tail : Tree compilation source reasonAt resultType continuation scope context rest body) :
      Tree compilation source reasonAt resultType continuation scope context (.expression expression :: rest)
        (Core.LocalSequence.discard (Core.LocalLoop.controlType resultType) expressionCode body)

/-- The post-vector finishes normally. Its final lexical names are intentionally
absent from the next iteration's source scope. -/
def Fallthrough (type : Core.Ty) (_scope : SourceCoreLocalCell.Scope) (_context : Context) (code : Core.Expr) : Prop :=
  code = Core.LocalLoop.fallthrough type

theorem Tree.hasType
    {compilation : SourceCorePrimitive.Context} {source : TypedSource} {reasonAt : ExpressionId → Core.Word}
    {resultType : Core.Ty} {continuation : SourceCoreLocalCell.Scope → Context → Core.Expr → Prop}
    {scope : SourceCoreLocalCell.Scope} {context : Context} {items : List ForItemForm} {code : Core.Expr}
    (tree : Tree compilation source reasonAt resultType continuation scope context items code)
    (wellFormed : Core.Ty.WellFormed [] resultType)
    (nextTyped : ∀ {scope context code}, continuation scope context code →
      Core.HasType (SourceCoreLocalCell.coreContext scope) code (Core.LocalLoop.resultType resultType)) :
    Core.HasType (SourceCoreLocalCell.coreContext scope) code (Core.LocalLoop.resultType resultType) := by
  induction tree with
  | nil next => exact nextTyped next
  | letUninitialized binding _ _ tail =>
    exact Core.LocalSequence.letUninitialized_hasType (binding.types.wellFormed []) tail
  | letInitialized _ _ value _ tail =>
    exact Core.LocalSequence.letInitialized_hasType (Core.LocalLoop.controlType_wellFormed wellFormed) value.hasType tail
  | assign target value _ tail =>
    exact Core.LocalSequence.assign_hasType (Core.LocalLoop.controlType_wellFormed wellFormed)
      (.var (SourceCoreLocalCell.lookup?_context target.slot)) value.hasType tail
  | discard value _ tail =>
    exact Core.LocalSequence.discard_hasType (Core.LocalLoop.controlType_wellFormed wellFormed) value.hasType tail

theorem Tree.map
    {compilation : SourceCorePrimitive.Context} {source : TypedSource} {reasonAt : ExpressionId → Core.Word}
    {resultType : Core.Ty} {left right : SourceCoreLocalCell.Scope → Context → Core.Expr → Prop}
    {scope : SourceCoreLocalCell.Scope} {context : Context} {items : List ForItemForm} {code : Core.Expr}
    (tree : Tree compilation source reasonAt resultType left scope context items code)
    (next : ∀ {scope context code}, left scope context code → right scope context code) :
    Tree compilation source reasonAt resultType right scope context items code := by
  induction tree with
  | nil certificate => exact .nil (next certificate)
  | letUninitialized binding extension _ tail => exact .letUninitialized binding extension tail
  | letInitialized binding extension value _ tail => exact .letInitialized binding extension value tail
  | assign target value _ tail => exact .assign target value tail
  | discard value _ tail => exact .discard value tail

end Solcore.SourceSemantics.CoreLowering.ForHeaders
