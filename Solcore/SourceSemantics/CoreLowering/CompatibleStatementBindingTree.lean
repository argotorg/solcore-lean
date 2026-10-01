import Solcore.SourceSemantics.CoreLowering.CompatibleStatementMeaning
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOrdinaryAllocation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedAllocationRenaming
import Solcore.SourceSemantics.CoreLowering.CoreContinuationAgreement

/-! Ordinary uninitialized lexical bindings before a fixed-scope compatible
body. Each binding retains the actual indexed allocator receipts. Generalized
bindings and initializer evaluation are separate extensions. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleStatementBindings
open Core Frontend SourceInference
abbrev Scope := SourceCoreLocalCell.Scope
abbrev ValuesContext := SourceCoreCompatibleValues.Context

def request (source : TypedSource) (scope : Scope) (binder : TypedBinder) (payload : Ty) :
    SourceCoreSourceCells.Request := ⟨source, scope, Renaming.id, binder, payload, none⟩

inductive Syntax (source : TypedSource) (finalContext : SourceSemantics.Context) :
    SourceSemantics.Context → List StatementId → TypeSystem.Ty → Prop where
  | body {statements expected} (syntaxTree : CompatibleStatements.Syntax source finalContext statements expected) :
      Syntax source finalContext finalContext statements expected
  | uninitialized {context nextContext id node binder rest expected}
      (found : source.lookupStatement? id = some node) (form : node.form = .letDecl binder none)
      (declaration : SourceCoreDataPlaces.rootBinder source binder.id = .ok binder)
      (monomorphic : binder.scheme.quantified = [])
      (extended : BinderExtends source.owner context binder nextContext)
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (remaining : Syntax source finalContext nextContext rest expected) :
      Syntax source finalContext context (id :: rest) expected

inductive Tree (layouts : SourceCoreAllocationLayouts.Prepared)
    (owner : SourceSpecialization.SpecializationKey) (active : TypeSystem.Substitution)
    (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (readFuel : Nat) (values : ValuesContext) (source : TypedSource)
    (finalContext : SourceSemantics.Context) (solved : List SolvedRequirement)
    (reasonAt : ExpressionId → Word) :
    SourceSemantics.Context → Scope → List StatementId → TypeSystem.Ty → Ty → Expr → Prop where
  | body {scope statements expected type code}
      (body : CompatibleStatements.Tree readFuel values source finalContext solved reasonAt scope statements expected type code) :
      Tree layouts owner active frame globals onError readFuel values source finalContext solved reasonAt
        finalContext scope statements expected type code
  | uninitialized {context nextContext scope id node binder rest expected type body payload}
      (found : source.lookupStatement? id = some node) (form : node.form = .letDecl binder none)
      (monomorphic : binder.scheme.quantified = [])
      (extended : BinderExtends source.owner context binder nextContext)
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (projected : values.checked.catalog.project binder.scheme.body = .ok payload)
      (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (request source scope binder payload))
      (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
        (layouts.allocatorAt owner active onError) (request source scope binder payload))
      (same : annotation.original = allocation.expression)
      (remaining : Tree layouts owner active frame globals onError readFuel values source finalContext solved reasonAt
        nextContext ((binder.id, payload) :: scope) rest expected type body) :
      Tree layouts owner active frame globals onError readFuel values source finalContext solved reasonAt
        context scope (id :: rest) expected type (.letE annotation.expression body)
end Solcore.SourceSemantics.CoreLowering.CompatibleStatementBindings
