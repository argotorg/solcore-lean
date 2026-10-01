import Solcore.Frontend.SourceCoreCallableViews
import Solcore.Frontend.SourceCoreCallableViewWrappers

/-! Select a cached local-read view and wrap its actual native expression.
No evidence is selected and no source body is traversed at runtime. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCallableViewLowering
open SourceInference
abbrev Key := SourceSpecialization.SpecializationKey
abbrev Plan := SourceSpecializationWorklist.Plan

inductive Error where
  | missingView (owner : Key) (read : ExpressionId) (active : TypeSystem.Substitution)
  | sourceOwnerMismatch
  | occurrenceMismatch (read : ExpressionId)
  | unsupportedCarrier (type : Core.Ty)
  deriving Repr

structure Viewed {program : CheckedProgram} {plan : Plan}
    (table : SourceCoreCallableViews.Table program plan) (owner : Key) (active : TypeSystem.Substitution)
    (read : ExpressionId) (original : SourceCoreBasic.LoweredExpr) where private mk ::
  entry : SourceCoreCallableViews.Entry program plan
  found : table.viewAt? owner read active = some entry
  lowered : SourceCoreBasic.LoweredExpr
  typeExact : lowered.type = original.type

def lowerWithReceipt {program : CheckedProgram} {plan : Plan}
    (table : SourceCoreCallableViews.Table program plan) (owner : Key) (active : TypeSystem.Substitution)
    (source : TypedSource) (read : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr) :
    Except Error (Viewed table owner active read lowered) := do
  let entry ← match found : table.viewAt? owner read active with
    | none => throw (.missingView owner read active)
    | some entry => pure (⟨entry, found⟩ : {entry // table.viewAt? owner read active = some entry})
  unless source.owner = owner.declaration do throw .sourceOwnerMismatch
  let current ← match source.lookupExpression? read with
    | none => throw (.occurrenceMismatch read)
    | some current => pure current
  let reference := entry.val.view.reference
  unless current = reference.original || current = reference.normalized || current = entry.val.view.rawRead do
    throw (.occurrenceMismatch read)
  if !entry.val.view.wrapsPrincipal then pure ⟨entry.val, entry.property, lowered, rfl⟩ else
    match lowered.type with
    | .product (.product (.sum .unit .word) (.function parameter (.sum .word result))) .word =>
        pure ⟨entry.val, entry.property, {
          lowered with expression := SourceCoreCallableViewWrappers.lower parameter result entry.val.id lowered.expression }, rfl⟩
    | type => throw (.unsupportedCarrier type)

def lower {program : CheckedProgram} {plan : Plan}
    (table : SourceCoreCallableViews.Table program plan) (owner : Key) (active : TypeSystem.Substitution)
    (source : TypedSource) (read : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr) :
    Except Error SourceCoreBasic.LoweredExpr :=
  (lowerWithReceipt table owner active source read lowered).map (·.lowered)

end Solcore.Frontend.SourceCoreCallableViewLowering
