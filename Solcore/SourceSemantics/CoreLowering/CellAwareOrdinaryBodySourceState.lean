import Solcore.SourceSemantics.CoreLowering.CellAwareLexicalBodyExpressions
import Solcore.SourceSemantics.CoreLowering.CellAwareSourceReadProductLifting
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageLexicalInversion
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageScopedTerminalInversion

/-! Ordinary Source lifting uses actual lexical and heap typing. These facts
come from the genuine closure and its parameter allocation; native evaluation
is not an input to this Source step. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareOrdinaryBodySourceState
open Core Frontend SourceInference
open Staging.Recursive
open SelectedCompilationStageScopedLiftBounds (PlainStatements)

variable {program : Program} {registry : Registry} {invocation : Scope}

structure State (context : SourceSemantics.Context) (environment : Dynamic.Environment) (heap : Dynamic.Heap) : Prop where
  runtime : Dynamic.SourceRuntimeValid program context invocation.source
  covers : invocation.evidence.Covers context
  locals : Dynamic.EnvironmentAgrees heap context.locals environment
  heapTyped : Dynamic.HeapWellTyped context heap

def embed : Dynamic.ControlOutcome → BodyOutcome
  | .returned value => .returned value
  | .fallthrough environment => .fallthrough environment
  | .breaking environment => .breaking environment
  | .continuing environment => .continuing environment
  | .fault reason => .fault (.semantic reason)

def Post (context : SourceSemantics.Context) (before after : Dynamic.Heap) : Dynamic.ControlOutcome → Prop
  | .fault _ => True
  | _ => Dynamic.HeapWellTyped context after ∧ Dynamic.HeapTypesExtend before after

def Lifts (context : SourceSemantics.Context) (mode : Bool) (statements : List StatementId) : Prop :=
  ∀ {environment before}, State (program := program) (invocation := invocation) context environment before →
    ∀ {size finalContext outcome after}, PlainStatements program mode size invocation context environment before
      statements finalContext outcome after →
    StatementsIn program registry mode invocation context environment before statements finalContext (embed outcome) after ∧
      Post context before after outcome

theorem expression {checked : SourceCoreCompatibleCatalog.Checked} {reasonAt context scope id lowered}
    (certificate : CellAwareLexicalBodyExpressions.StaticCertificate checked invocation.source reasonAt context scope id lowered)
    (unique : NodeOccurrencesUnique invocation.source)
    {size environment before outcome after}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome program size context invocation.evidence invocation.source
      environment before id outcome after) :
    Staging.Recursive.Expression program registry invocation context environment before id (Lifting.embed outcome) after := by
  obtain ⟨_,_,_,_,_,tree⟩ := certificate
  exact CellAwareSourceReadProductLifting.exact_trace tree unique trace.sound

theorem expression_typed (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies program registry)
    {checked : SourceCoreCompatibleCatalog.Checked} {reasonAt context scope id lowered node}
    (certificate : CellAwareLexicalBodyExpressions.StaticCertificate checked invocation.source reasonAt context scope id lowered)
    (found : invocation.source.lookupExpression? id = some node)
    {size environment before value after}
    (state : State (program := program) (invocation := invocation) context environment before)
    (trace : RecursiveNamedCallBounds.ExpressionOutcome program size context invocation.evidence invocation.source
      environment before id (.value value) after) :
    Dynamic.ValueHasType context after value node.type ∧
      State (program := program) (invocation := invocation) context environment after ∧
      Dynamic.HeapTypesExtend before after := by
  have lifted := expression (registry := registry) certificate state.runtime.graph.nodeOccurrencesUnique trace
  obtain ⟨_, graded⟩ := Staging.Recursive.Size.Expression.of_trace lifted
  obtain ⟨_,_,actual,actualFound,typed,_⟩ := certificate
  cases Option.some.inj (actualFound.symm.trans found)
  have preserved := Staging.Recursive.SelectedPreservation.expression selectedBodies
    state.runtime state.covers state.locals state.heapTyped typed graded
  exact ⟨preserved.value_typed value rfl,
    ⟨state.runtime,state.covers,state.locals.mono preserved.heap_extends,preserved.heap_typed⟩,
    preserved.heap_extends⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareOrdinaryBodySourceState
