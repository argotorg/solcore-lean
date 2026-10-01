import Solcore.SourceSemantics.CoreLowering.CallableIndexedOrdinaryAllocation

/-! Exact transport for the emitted allocation prefix only. This fragment may
copy arbitrary existing closures as values, but never constructs or calls one.
It therefore retains exactly the same allocated values under lexical insertion.
No corresponding equality is asserted for an arbitrary function body. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedAllocationRenaming
open Core Frontend ReadOnly CallableIndexedAllocationCompletion

private inductive Fragment : Expr → Prop where
  | unit : Fragment .unit
  | var {index} : Fragment (.var index)
  | pair {left right} : Fragment left → Fragment right → Fragment (.pair left right)
  | construct {constructor payload} : Fragment payload → Fragment (.construct constructor payload)
  | inLeft {type payload} : Fragment payload → Fragment (.inLeft type payload)
  | inRight {type payload} : Fragment payload → Fragment (.inRight type payload)
  | newCell {type payload} : Fragment payload → Fragment (.newCell type payload)
  | loadCell {reference} : Fragment reference → Fragment (.loadCell reference)
  | letE {value body} : Fragment value → Fragment body → Fragment (.letE value body)

private theorem Fragment.rename {expression : Expr} (fragment : Fragment expression) (ξ : Renaming) :
    Fragment (expression.rename ξ) := by
  induction fragment generalizing ξ with
  | unit => exact .unit
  | var => exact .var
  | pair _ _ left right => exact .pair (left ξ) (right ξ)
  | construct _ ih => exact .construct (ih ξ)
  | inLeft _ ih => exact .inLeft (ih ξ)
  | inRight _ ih => exact .inRight (ih ξ)
  | newCell _ ih => exact .newCell (ih ξ)
  | loadCell _ ih => exact .loadCell (ih ξ)
  | letE _ _ value body => exact .letE (value ξ) (body ξ.lift)

private theorem Fragment.transport {expression : Expr} (fragment : Fragment expression)
    {environment target : Environment} {before after : Store} {result : Value} {ξ : Renaming}
    (evaluated : Evaluates environment before expression result after)
    (agrees : EnvironmentsAgree ξ environment target) :
    Evaluates target before (expression.rename ξ) result after := by
  induction fragment generalizing environment target before after result ξ with
  | unit => cases evaluated; exact .unit
  | var => cases evaluated with | var found => exact .var (agrees found)
  | pair _ _ left right =>
    cases evaluated with | pair first second => exact .pair (left first agrees) (right second agrees)
  | construct _ ih => cases evaluated with | construct payload => exact .construct (ih payload agrees)
  | inLeft _ ih => cases evaluated with | inLeft payload => exact .inLeft (ih payload agrees)
  | inRight _ ih => cases evaluated with | inRight payload => exact .inRight (ih payload agrees)
  | newCell _ ih => cases evaluated with | newCell payload => exact .newCell (ih payload agrees)
  | loadCell _ ih => cases evaluated with | loadCell reference read => exact .loadCell (ih reference agrees) read
  | letE _ _ value body =>
    cases evaluated with | letE initial tail => exact .letE (value initial agrees) (body tail (agrees.lift _))

private theorem captures_fragment (references : Renaming) (scope : SourceCoreSourceCells.Scope) :
    Fragment (SourceCoreSourceCells.captures references scope) := by
  induction scope generalizing references with
  | nil => exact .unit
  | cons head tail ih =>
    cases tail with
    | nil => exact .var
    | cons next rest => exact .pair .var (ih _)

/-- Actual allocation receipts, plus the initialized-slot shape emitted by
`SourceCells.letInitialized`, make every temporary insertion exact. -/
theorem transport {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {request : SourceCoreSourceCells.Request} {layout : SourceCoreCallableIndexedFrames.Layout}
    {globals : Nat} {allocate : SourceCoreSourceCells.Allocator}
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active request)
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated layout globals allocate request)
    (same : annotation.original = allocation.expression)
    (payloadShape : request.payload = none ∨ request.payload = some (.var 0))
    {environment target : Environment} {before after : Store} {result : Value} {ξ : Renaming}
    (evaluated : Evaluates environment before annotation.expression result after)
    (agrees : EnvironmentsAgree ξ environment target) :
    Evaluates target before (annotation.expression.rename ξ) result after := by
  have fragment : Fragment annotation.expression := by
    rw [annotation.exact, same, allocation.expressionExact]
    apply Fragment.letE (.newCell (.loadCell .var))
    rw [← Expr.rename_insertion]
    apply Fragment.rename
    rcases payloadShape with absent | initialized
    · simp only [SourceCoreAllocationLayouts.allocation, absent]
      exact .letE (.newCell (.construct (captures_fragment _ _))) (.newCell (.inLeft .unit))
    · simp only [SourceCoreAllocationLayouts.allocation, initialized]
      exact .letE .var (.letE (.newCell (.construct (by
        rw [← Expr.rename_insertion]
        exact (captures_fragment _ _).rename _))) (.newCell (.inRight .var)))
  exact fragment.transport evaluated agrees

end Solcore.SourceSemantics.CoreLowering.CallableIndexedAllocationRenaming
