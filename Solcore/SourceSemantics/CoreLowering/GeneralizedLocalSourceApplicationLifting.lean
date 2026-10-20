import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBodyExpressionAdmission
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalMaterializedProvenance
import Solcore.SourceSemantics.CoreLowering.CellAwareSourceReadProductLifting
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosureSourceTrace
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageNamedInvocationLifting
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageTerminalInversion
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageBodyLiftBounds
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalProgramSupport

/-! An ordinary Source call of an actually materialized local function lifts
through its retained compiler profile and original parameter allocation.
The terminal expression tree uses its real Source descriptor and requirement outcome. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalSourceApplicationLifting
open Core Frontend SourceInference GeneralHeap
open GeneralizedLocalMaterializedAssociation
open Staging.Recursive
open SelectedCompilationStageBodyLiftBounds (BodyLift)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {mapping : LocationMap} {world : StoreTyping}
  {function : Dynamic.Closure} (material : Materialization compiled mapping world function)
  (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) material.code)

include inputs in
theorem application {registry : Registry} {child caller : Scope}
    (selected : registry.Closure function child)
    {callContext : SourceSemantics.Context} {callerEvidence invocationEvidence : Dynamic.EvidenceEnvironment}
    {arguments : List Dynamic.Value} {before after : Dynamic.Heap}
    {size : Nat} {outcome : Dynamic.ExpressionOutcome}
    (arity : function.parameters.length = arguments.length)
    (trace : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) size
      callContext callerEvidence invocationEvidence before (.closure function) arguments outcome after) :
    Lifting.ApplicationLift (Program.ofChecked compiled.sourceProgram) registry caller callContext before
      (.closure function) arguments outcome after := by
  obtain ⟨childSize, environment, bound, valid, allocated, sourceTrace, _smaller⟩ :=
    SelectedCompilationStageClosureSourceTrace.source_prefix inputs.extended arity trace
  obtain ⟨finalContext, bodyOutcome, bodyTrace, converted⟩ :=
    SelectedCompilationStageNamedInvocationLifting.body_control sourceTrace
  have source := registry.source selected
  have evidence := registry.evidence selected
  have compilerSource := GeneralizedLocalBodyProfileReceipts.view_source material
  have terminal := GeneralizedLocalBodyProfileReceipts.terminal material
  rw [compilerSource] at terminal
  obtain ⟨expressionSize, plain, _strict, sameContext, sameOutcome, evaluated⟩ :=
    SelectedCompilationStageTerminalInversion.child_of_body material.unique terminal bodyTrace
  subst finalContext
  subst bodyOutcome
  have unique : NodeOccurrencesUnique child.source := source ▸ material.unique
  have plainTrace : Dynamic.ExpressionEvaluatesOutcome (Program.ofChecked compiled.sourceProgram)
      inputs.context child.evidence child.source environment bound material.bodyProfile.expression plain after := by
    simpa only [source, evidence] using evaluated.sound
  obtain ⟨receipt⟩ := GeneralizedLocalBodyProfileReceipts.receipt material
  obtain ⟨tree, _resultType, _typed⟩ := GeneralizedLocalBodyExpressionAdmission.actual_tree material inputs valid source receipt
  simp only [compilerSource, ← source] at tree
  have lifted := CellAwareSourceReadProductLifting.exact_trace (registry := registry) tree unique plainTrace
  have head := receipt.head child (source.trans compilerSource.symm)
  have bodyLift := SelectedCompilationStageBodyLiftBounds.terminal_expression head (Lifting.ExpressionLift.completed lifted)
  exact BodyLift.closure selected valid inputs.extended allocated bodyLift converted

include inputs in
/-- A materialized terminal expression tree introduces no stage rejection: its complete
ordinary outcome and reached Source heap embed exactly. -/
theorem application_exact {registry : Registry} {child caller : Scope}
    (selected : registry.Closure function child)
    {callContext : SourceSemantics.Context} {callerEvidence invocationEvidence : Dynamic.EvidenceEnvironment}
    {arguments : List Dynamic.Value} {before after : Dynamic.Heap}
    {size : Nat} {outcome : Dynamic.ExpressionOutcome}
    (arity : function.parameters.length = arguments.length)
    (trace : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) size
      callContext callerEvidence invocationEvidence before (.closure function) arguments outcome after) :
    Applies (Program.ofChecked compiled.sourceProgram) registry caller callContext before
      (.closure function) arguments (Lifting.embed outcome) after := by
  obtain ⟨childSize, environment, bound, valid, allocated, sourceTrace, _smaller⟩ :=
    SelectedCompilationStageClosureSourceTrace.source_prefix inputs.extended arity trace
  obtain ⟨finalContext, bodyOutcome, bodyTrace, converted⟩ :=
    SelectedCompilationStageNamedInvocationLifting.body_control sourceTrace
  have source := registry.source selected
  have evidence := registry.evidence selected
  have compilerSource := GeneralizedLocalBodyProfileReceipts.view_source material
  have terminal := GeneralizedLocalBodyProfileReceipts.terminal material
  rw [compilerSource] at terminal
  obtain ⟨expressionSize, plain, _strict, sameContext, sameOutcome, evaluated⟩ :=
    SelectedCompilationStageTerminalInversion.child_of_body material.unique terminal bodyTrace
  subst finalContext
  subst bodyOutcome
  have unique : NodeOccurrencesUnique child.source := source ▸ material.unique
  have plainTrace : Dynamic.ExpressionEvaluatesOutcome (Program.ofChecked compiled.sourceProgram)
      inputs.context child.evidence child.source environment bound material.bodyProfile.expression plain after := by
    simpa only [source, evidence] using evaluated.sound
  obtain ⟨receipt⟩ := GeneralizedLocalBodyProfileReceipts.receipt material
  obtain ⟨tree, _resultType, _typed⟩ := GeneralizedLocalBodyExpressionAdmission.actual_tree material inputs valid source receipt
  simp only [compilerSource, ← source] at tree
  have lifted := CellAwareSourceReadProductLifting.exact_trace (registry := registry) tree unique plainTrace
  have head := receipt.head child (source.trans compilerSource.symm)
  obtain ⟨_size, measured⟩ := Size.Expression.of_trace lifted
  cases plain with
  | value value =>
    cases converted
    exact .closure selected valid inputs.extended allocated (head.trace measured).sound .returned
  | fault reason =>
    cases converted
    exact .closure selected valid inputs.extended allocated (head.trace measured).sound .fault

include inputs in
theorem selected_application_exact {caller : Scope}
    {callContext : SourceSemantics.Context} {callerEvidence invocationEvidence : Dynamic.EvidenceEnvironment}
    {arguments : List Dynamic.Value} {before after : Dynamic.Heap}
    {size : Nat} {outcome : Dynamic.ExpressionOutcome}
    (arity : function.parameters.length = arguments.length)
    (trace : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) size
      callContext callerEvidence invocationEvidence before (.closure function) arguments outcome after) :
    Applies (Program.ofChecked compiled.sourceProgram) (SelectedCompilationPhysicalProgramSupport.stages compiled)
      caller callContext before (.closure function) arguments (Lifting.embed outcome) after := by
  obtain ⟨_sidecar, _accepted, selected⟩ := material.scope_at
  exact application_exact (registry := SelectedCompilationPhysicalProgramSupport.stages compiled)
    material inputs (.anonymous selected) arity trace

include inputs in
/-- The selected child comes from the actual compiler packet retained by the
generalized read, using the public program's complete recursive registry. -/
theorem selected_application {caller : Scope}
    {callContext : SourceSemantics.Context} {callerEvidence invocationEvidence : Dynamic.EvidenceEnvironment}
    {arguments : List Dynamic.Value} {before after : Dynamic.Heap}
    {size : Nat} {outcome : Dynamic.ExpressionOutcome}
    (arity : function.parameters.length = arguments.length)
    (trace : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) size
      callContext callerEvidence invocationEvidence before (.closure function) arguments outcome after) :
    Lifting.ApplicationLift (Program.ofChecked compiled.sourceProgram)
      (SelectedCompilationPhysicalProgramSupport.stages compiled) caller callContext before
      (.closure function) arguments outcome after := by
  obtain ⟨_sidecar, _accepted, selected⟩ := material.scope_at
  exact application (registry := SelectedCompilationPhysicalProgramSupport.stages compiled) material inputs (.anonymous selected) arity trace

/-- Public representations expose the retained materialization directly; the
actual Source closure frame determines its original parameter context. -/
theorem selected_association_exact
    {native : Value} {bindings : List CallableIndexedParameterCertificates.Binding}
    {parameter result : Core.Ty}
    (association : Association compiled mapping world function native bindings parameter result)
    (frame : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function)
    {caller : Scope} {callContext : SourceSemantics.Context}
    {callerEvidence invocationEvidence : Dynamic.EvidenceEnvironment}
    {arguments : List Dynamic.Value} {before after : Dynamic.Heap}
    {size : Nat} {outcome : Dynamic.ExpressionOutcome}
    (arity : function.parameters.length = arguments.length)
    (trace : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) size
      callContext callerEvidence invocationEvidence before (.closure function) arguments outcome after) :
    Applies (Program.ofChecked compiled.sourceProgram) (SelectedCompilationPhysicalProgramSupport.stages compiled)
      caller callContext before (.closure function) arguments (Lifting.embed outcome) after := by
  cases association with
  | viewed material _view _typed =>
    obtain ⟨inputs⟩ := GeneralizedLocalBodyCompiler.entry_context material frame material.ownership
    exact selected_application_exact material inputs arity trace

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalSourceApplicationLifting
