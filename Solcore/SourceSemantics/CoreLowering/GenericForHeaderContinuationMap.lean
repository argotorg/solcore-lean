import Solcore.SourceSemantics.CoreLowering.GenericForHeaderTree

/-! A static for-header tree changes its terminal continuation by implication.
All allocation, assignment, typing, emitted-code, and error receipts are kept. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericForHeader
open Core Frontend SourceInference
namespace Tree
variable {layouts : SourceCoreAllocationLayouts.Prepared}
  {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {definitions : DataEnvironment} {administrative : Core.Context} {type : Ty}
  {continuation target : SourceSemantics.Context → Scope → Expr → Prop}
  {context : SourceSemantics.Context} {scope : Scope} {items : List ForItemForm} {code : Expr}

/-- Map only the terminal static continuation of an ordinary for header. -/
theorem mapContinuation
    (tree : Tree layouts owner active frame globals onError values source certificates
      definitions administrative type continuation context scope items code)
    (map : ∀ {context scope code}, continuation context scope code → target context scope code) :
    Tree layouts owner active frame globals onError values source certificates
      definitions administrative type target context scope items code := by
  induction tree with
  | nil next => exact .nil (map next)
  | uninitialized monomorphic extended ordinary projected allocation annotation same remaining ih =>
    exact .uninitialized monomorphic extended ordinary projected allocation annotation same ih
  | initialized monomorphic extended ordinary found sourceType initial allocation annotation same remaining ih =>
    exact .initialized monomorphic extended ordinary found sourceType initial allocation annotation same ih
  | discard found value remaining ih => exact .discard found value ih
  | assign head remaining ih => exact .assign head ih
  | bitNot head remaining ih => exact .bitNot head ih

/-- Error interpretation does not depend on the terminal continuation proof. -/
theorem ErrorsFor.mapContinuation
    {policy : AssignmentDiagnosticPolicy} {registry : SourceCoreRawMetadata.Registry}
    {faults : FunctionCalls.FaultRep}
    {tree : Tree layouts owner active frame globals onError values source certificates
      definitions administrative type continuation context scope items code}
    (errors : ErrorsFor policy registry faults tree)
    (map : ∀ {context scope code}, continuation context scope code → target context scope code) :
    ErrorsFor policy registry faults (tree.mapContinuation map) := by
  induction errors with
  | @nil context scope code next => exact .nil (next := map next)
  | @uninitialized context nextContext scope binder rest body payload
      monomorphic extended ordinary projected allocation annotation same remaining remainingErrors ih =>
    exact .uninitialized (monomorphic := monomorphic) (extended := extended)
      (ordinary := ordinary) (projected := projected) (allocation := allocation)
      (annotation := annotation) (same := same) ih
  | @initialized context nextContext scope binder initializer initializerNode lowered body rest
      monomorphic extended ordinary found sourceType initial allocation annotation same remaining remainingErrors ih =>
    exact .initialized (monomorphic := monomorphic) (extended := extended)
      (ordinary := ordinary) (initializerFound := found) (sourceType := sourceType)
      (initial := initial) (allocation := allocation) (annotation := annotation) (same := same) ih
  | @discard context scope expression expressionNode rest lowered body found value remaining remainingErrors ih =>
    exact .discard (found := found) (value := value) ih
  | @assign context scope assignment operator rhs rest body head remaining remainingErrors headErrors ih =>
    exact .assign (head := head) ih headErrors
  | @bitNot context scope assignment rest body head remaining remainingErrors headErrors ih =>
    exact .bitNot (head := head) ih headErrors

end Tree
end Solcore.SourceSemantics.CoreLowering.GenericForHeader
