import Solcore.SourceSemantics.CoreLowering.CompatibleStatementBindingMeaning

/-! One ordinary initialized let before an authenticated binding sequence.
The initializer belongs to the old lexical context. The payload slot is an
administrative result binder, and the new source cell exists only on success. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleStatementInitialized
open Core Frontend SourceInference
abbrev Scope := SourceCoreLocalCell.Scope
abbrev ValuesContext := SourceCoreCompatibleValues.Context

def request (source : TypedSource) (scope : Scope) (binder : TypedBinder) (payload : Ty) :
    SourceCoreSourceCells.Request :=
  ⟨source, scope, Renaming.comp (Renaming.insertion 0) Renaming.id, binder, payload, some (.var 0)⟩

def sequence (type : Ty) (initializer allocation body : Expr) : Expr :=
  LanguageResult.bind (LocalLoop.controlType type) initializer (.letE allocation (body.weakenAt 1))

inductive Syntax (source : TypedSource) (context nextContext finalContext : SourceSemantics.Context)
    (id : StatementId) (rest : List StatementId) (expected : TypeSystem.Ty) : Prop where
  | initialized {node binder initializer initializerNode}
      (found : source.lookupStatement? id = some node) (form : node.form = .letDecl binder (some initializer))
      (declaration : SourceCoreDataPlaces.rootBinder source binder.id = .ok binder)
      (monomorphic : binder.scheme.quantified = [])
      (extended : BinderExtends source.owner context binder nextContext)
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (initializerFound : source.lookupExpression? initializer = some initializerNode)
      (sourceType : initializerNode.type = binder.scheme.body)
      (initializerTyped : ExpressionHasType source context initializer initializerNode.type)
      (initializerSyntax : CompatibleExpressionConstructors.Syntax source initializer)
      (remaining : CompatibleStatementBindings.Syntax source finalContext nextContext rest expected) :
      Syntax source context nextContext finalContext id rest expected

inductive Tree (layouts : SourceCoreAllocationLayouts.Prepared)
    (owner : SourceSpecialization.SpecializationKey) (active : TypeSystem.Substitution)
    (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (readFuel : Nat) (values : ValuesContext) (source : TypedSource)
    (context nextContext finalContext : SourceSemantics.Context) (solved : List SolvedRequirement)
    (reasonAt : ExpressionId → Word) (scope : Scope) (id : StatementId) (rest : List StatementId)
    (expected : TypeSystem.Ty) (type : Ty) : Expr → Prop where
  | initialized {node binder initializer initializerNode lowered body}
      (found : source.lookupStatement? id = some node) (form : node.form = .letDecl binder (some initializer))
      (monomorphic : binder.scheme.quantified = [])
      (extended : BinderExtends source.owner context binder nextContext)
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (initializerFound : source.lookupExpression? initializer = some initializerNode)
      (sourceType : initializerNode.type = binder.scheme.body)
      (initial : CompatibleExpressionConstructors.Tree readFuel values source context solved reasonAt scope initializer lowered)
      (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (request source scope binder lowered.type))
      (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
        (layouts.allocatorAt owner active onError) (request source scope binder lowered.type))
      (same : annotation.original = allocation.expression)
      (remaining : CompatibleStatementBindings.Tree layouts owner active frame globals onError readFuel values source
        finalContext solved reasonAt nextContext ((binder.id, lowered.type) :: scope) rest expected type body) :
      Tree layouts owner active frame globals onError readFuel values source context nextContext finalContext solved reasonAt
        scope id rest expected type (sequence type lowered.expression annotation.expression body)
end Solcore.SourceSemantics.CoreLowering.CompatibleStatementInitialized
