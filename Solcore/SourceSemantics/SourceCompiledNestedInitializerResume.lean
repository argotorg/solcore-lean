import Solcore.SourceSemantics.SourceCompiledInitializerLambdaResume

/-! A genuine enclosing initializer receipt supplies the lambda call and its
retention. The inner declaration is selected from that lambda's real body. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness ProtectedVariables
open SourceCompiledGeneralizedSoundness

structure NestedInitializerResume
    {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction}
    {fuel : Nat} {selected : Selected compiled row fuel}
    {outerSource : Syntax.Statement} (outer : InitializerOccurrence selected outerSource)
    (innerSource : Syntax.Statement) where
  inner : InitializerOccurrence selected innerSource
  context : inner.inferenceContext = {outer.inferenceContext with loopDepth := 0}
  transport : SafeTransport inner.receipt.binding.1.scheme.quantified inner.receipt.ready outer.receipt.ready
  valueSafe : Safe inner.receipt.binding.1.scheme.quantified outer.receipt.ready outer.receipt.value.type
  live : LiveBindersSafe inner.receipt.binding.1.scheme.quantified outer.receipt.ready
  bound : ∀ q ∈ inner.receipt.binding.1.scheme.quantified, q.index < outer.receipt.ready.inference.next
  olderSafe : ∀ type, type.VariablesBelow outer.entry.inference.next →
    Safe inner.receipt.binding.1.scheme.quantified outer.receipt.ready type
  newRows : ∀ requirement ∈ outer.receipt.ready.requirements,
    requirement ∉ inner.receipt.ready.requirements →
    PredicateSafe inner.receipt.binding.1.scheme.quantified outer.receipt.ready requirement.predicate

theorem InitializerOccurrence.lambdaResume
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    {selected : Selected compiled row fuel} {outerSource innerSource : Syntax.Statement}
    (outer : InitializerOccurrence selected outerSource)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (scope : CheckingScope selected outer.inferenceContext)
    (ready : outer.entry.InferenceReady) (nodesBelow : outer.entry.NodesBelowNextOccurrence)
    (operational : GeneralizedActualStateInvariant outer.entry (evidenceSource selected))
    (owner : outer.entry.owner = (evidenceSource selected).owner)
    (retained : outer.result.state.nodes <+: selected.body.returned.nodes)
    {keyword : Syntax.SourceSpan} {parameters : Syntax.DelimitedList Syntax.LambdaParameter}
    {annotation : Option Syntax.TypeExpr} {body : Syntax.Block}
    (form : outer.receipt.initializer.value = .lambda keyword parameters annotation body)
    {index : Nat} (position : body.value[index]? = some innerSource)
    {name : Syntax.Identifier} {localAnnotation : Option Syntax.TypeExpr} {initializer : Syntax.Expr}
    (innerForm : innerSource.value = .letDecl name localAnnotation (some initializer)) :
    Nonempty (NestedInitializerResume outer innerSource) := by
  have child := outer.receipt.child
  cases fuelEq : outer.childFuel with
  | zero =>
    conv at child => lhs; arg 1; rw [fuelEq]
    simp [Detail.inferExprFuel] at child
  | succ childFuel =>
    conv at child => lhs; arg 1; rw [fuelEq]
    have readyRetained : outer.receipt.ready.nodes <+: selected.body.returned.nodes := by
      apply List.IsPrefix.trans (l₂ := outer.result.state.nodes) _ retained
      rw [congrArg (fun result : Detail.StatementResult => result.state.nodes) outer.receipt.completed]
      exact List.prefix_append _ _
    obtain ⟨inner,context,transport,valueSafe,live,bound,olderSafe,newRows⟩ :=
      lambda_initializer_resume checked scope ready.allocateStatementId
        (State.allocateStatementId_preserves_nodesBelowNextOccurrence _ nodesBelow)
        operational.allocateStatementId owner
        (outer.receipt.annotationAccepted.variablesBelow _)
        (fun _ _ type member => safe_closed _ _
          (outer.receipt.annotationAccepted.variablesBelow 0 type member))
        readyRetained outer.extension form child position innerForm
    exact ⟨⟨inner,context,transport,valueSafe,live,bound,olderSafe,newRows⟩⟩

end Solcore.SourceSemantics.SourceCompiledLocalFinalization
