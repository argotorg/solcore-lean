import Solcore.SourceSemantics.CoreLowering.CompatibleStatementInitializedMeaning

/-! Arbitrarily mixed ordinary lexical bindings. Initializers belong to the
context before their binding; a failed initializer ends at that context. The
terminal fixed-scope statement tree closes every child semantic obligation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleStatementMixed
open Core Frontend SourceInference
abbrev Scope := SourceCoreLocalCell.Scope
abbrev ValuesContext := SourceCoreCompatibleValues.Context

abbrev absentRequest (source : TypedSource) (scope : Scope) (binder : TypedBinder) (payload : Ty) :
    SourceCoreSourceCells.Request := ⟨source, scope, Renaming.id, binder, payload, none⟩

abbrev initializedRequest := CompatibleStatementInitialized.request
abbrev sequence := CompatibleStatementInitialized.sequence

inductive Syntax (source : TypedSource) :
    SourceSemantics.Context → List StatementId → TypeSystem.Ty → Prop where
  | body {context statements expected} (syntaxTree : CompatibleStatements.Syntax source context statements expected) :
      Syntax source context statements expected
  | uninitialized {context nextContext id node binder rest expected}
      (found : source.lookupStatement? id = some node) (form : node.form = .letDecl binder none)
      (declaration : SourceCoreDataPlaces.rootBinder source binder.id = .ok binder)
      (monomorphic : binder.scheme.quantified = [])
      (extended : BinderExtends source.owner context binder nextContext)
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (remaining : Syntax source nextContext rest expected) :
      Syntax source context (id :: rest) expected

  | initialized {context nextContext id node binder initializer initializerNode rest expected}
      (found : source.lookupStatement? id = some node) (form : node.form = .letDecl binder (some initializer))
      (declaration : SourceCoreDataPlaces.rootBinder source binder.id = .ok binder)
      (monomorphic : binder.scheme.quantified = [])
      (extended : BinderExtends source.owner context binder nextContext)
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (initializerFound : source.lookupExpression? initializer = some initializerNode)
      (sourceType : initializerNode.type = binder.scheme.body)
      (initializerTyped : ExpressionHasType source context initializer initializerNode.type)
      (initializerSyntax : CompatibleExpressionConstructors.Syntax source initializer)
      (remaining : Syntax source nextContext rest expected) :
      Syntax source context (id :: rest) expected

inductive Tree (layouts : SourceCoreAllocationLayouts.Prepared)
    (owner : SourceSpecialization.SpecializationKey) (active : TypeSystem.Substitution)
    (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (readFuel : Nat) (values : ValuesContext) (source : TypedSource)
    (solved : List SolvedRequirement)
    (reasonAt : ExpressionId → Word) :
    SourceSemantics.Context → Scope → List StatementId → TypeSystem.Ty → Ty → Expr → Prop where
  | body {context scope statements expected type code}
      (body : CompatibleStatements.Tree readFuel values source context solved reasonAt scope statements expected type code) :
      Tree layouts owner active frame globals onError readFuel values source solved reasonAt
        context scope statements expected type code
  | uninitialized {context nextContext scope id node binder rest expected type body payload}
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
        nextContext ((binder.id, payload) :: scope) rest expected type body) :
      Tree layouts owner active frame globals onError readFuel values source solved reasonAt
        context scope (id :: rest) expected type (.letE annotation.expression body)
  | initialized {context nextContext scope id node binder initializer initializerNode lowered body rest expected type}
      (found : source.lookupStatement? id = some node) (form : node.form = .letDecl binder (some initializer))
      (monomorphic : binder.scheme.quantified = [])
      (extended : BinderExtends source.owner context binder nextContext)
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (initializerFound : source.lookupExpression? initializer = some initializerNode)
      (sourceType : initializerNode.type = binder.scheme.body)
      (initial : CompatibleExpressionConstructors.Tree readFuel values source context solved reasonAt scope initializer lowered)
      (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (initializedRequest source scope binder lowered.type))
      (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
        (layouts.allocatorAt owner active onError) (initializedRequest source scope binder lowered.type))
      (same : annotation.original = allocation.expression)
      (remaining : Tree layouts owner active frame globals onError readFuel values source
        solved reasonAt nextContext ((binder.id, lowered.type) :: scope) rest expected type body) :
      Tree layouts owner active frame globals onError readFuel values source solved reasonAt
        context scope (id :: rest) expected type (sequence type lowered.expression annotation.expression body)

/-- The lexical environment at the actual stopping point, recording only the
bindings whose initializers completed and whose source cells were allocated. -/
inductive Reached (owner : Resolved.DeclarationId) :
    SourceSemantics.Context → Scope → Dynamic.Environment →
    SourceSemantics.Context → Scope → Dynamic.Environment → Prop where
  | here {context scope environment} : Reached owner context scope environment context scope environment
  | bind {context nextContext finalContext scope finalScope environment finalEnvironment binder payload location}
      (extended : BinderExtends owner context binder nextContext)
      (remaining : Reached owner nextContext ((binder.id, payload) :: scope) ((binder.id, location) :: environment)
        finalContext finalScope finalEnvironment) :
      Reached owner context scope environment finalContext finalScope finalEnvironment

end Solcore.SourceSemantics.CoreLowering.CompatibleStatementMixed
