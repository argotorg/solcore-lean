import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalOrdinaryBodyAdmission
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalMaterializedProvenance
import Solcore.SourceSemantics.CoreLowering.CellAwareOrdinaryBodySourceLifting
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredClosureSourceArguments
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosureSourceTrace
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageNamedInvocationLifting
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalProgramSupport

/-! Independent Source calls enter the actual parameter allocation and lift
through the complete finite lexical body extracted from contextual compilation.
Source argument and capture typing refer to the actual incoming heap. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalSourceApplicationLifting
open Core Frontend SourceInference GeneralHeap
open GeneralizedLocalMaterializedAssociation
open Staging.Recursive

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {mapping : LocationMap} {world : StoreTyping}
  {function : Dynamic.Closure} (material : Materialization compiled mapping world function)
  (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) material.code)

include inputs in
/-- Parameter allocation supplies the complete Source state at the body boundary. -/
theorem parameter_state {registry : Registry} {child : Scope}
    (selected : registry.Closure function child)
    (frame : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function)
    {arguments : List Dynamic.Value} {before bound : Dynamic.Heap} {environment : Dynamic.Environment}
    (raw : CallableIndexedOwnedStoredClosureSourceArguments.SourceArguments function before arguments)
    (allocated : Dynamic.BindersAllocate function.captured before function.parameters arguments environment bound) :
    CellAwareOrdinaryBodySourceState.State (program := Program.ofChecked compiled.sourceProgram)
      (invocation := child) inputs.context environment bound := by
  have runtime := CallableIndexedOwnedLambdaSourceAdmission.runtime_at_parameters frame inputs.extended
  have mono := FunctionCallBody.mono_binders inputs.extended
  have reached := Dynamic.BindersAllocate.preservesHeapTyping raw.heaps raw.arguments allocated
  have fields := Dynamic.MonoBindersExtend.runtimeContextFields inputs.extended
  refine ⟨?_,?_,allocated.preservesEnvironmentAgreement mono.1 mono.2 raw.captures,?_⟩
  · simpa only [registry.source selected] using runtime.1
  · simpa only [registry.evidence selected] using runtime.2
  · exact reached.transportClosed fields.signatures frame.code.closed (fields.targetClosed frame.code.closed)
      frame.code.variables_closed (fields.targetResidualVariablesOpen frame.code.residual_variables_open)

include inputs in
/-- The original outcome and reached Source heap embed exactly. -/
theorem application_exact {registry : Registry} {child caller : Scope}
    (selected : registry.Closure function child)
    {callContext : SourceSemantics.Context} {callerEvidence invocationEvidence : Dynamic.EvidenceEnvironment}
    {arguments : List Dynamic.Value} {before after : Dynamic.Heap}
    {size : Nat} {outcome : Dynamic.ExpressionOutcome}
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (raw : CallableIndexedOwnedStoredClosureSourceArguments.SourceArguments function before arguments)
    (arity : function.parameters.length = arguments.length)
    (trace : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) size
      callContext callerEvidence invocationEvidence before (.closure function) arguments outcome after) :
    Applies (Program.ofChecked compiled.sourceProgram) registry caller callContext before
      (.closure function) arguments (Lifting.embed outcome) after := by
  obtain ⟨childSize, environment, bound, valid, allocated, sourceTrace, _smaller⟩ :=
    SelectedCompilationStageClosureSourceTrace.source_prefix inputs.extended arity trace
  obtain ⟨finalContext, bodyOutcome, bodyTrace, converted⟩ :=
    SelectedCompilationStageNamedInvocationLifting.body_control sourceTrace
  obtain ⟨flow,_emitted,tree⟩ := GeneralizedLocalOrdinaryBodyAdmission.tree material inputs valid
  have source := registry.source selected
  rw [← source] at tree
  have plain : SelectedCompilationStageScopedLiftBounds.PlainStatements
      (Program.ofChecked compiled.sourceProgram) true childSize child inputs.context environment bound
      function.body finalContext bodyOutcome after := by
    simpa only [SelectedCompilationStageScopedLiftBounds.PlainStatements, Bool.true_eq, ↓reduceIte, source,registry.evidence selected] using bodyTrace
  obtain ⟨lifted,_post⟩ := CellAwareOrdinaryBodySourceLifting.lifts wellFormed tree
    (parameter_state material inputs selected valid raw allocated) plain
  have matched : BodyResult function.resultType (CellAwareOrdinaryBodySourceState.embed bodyOutcome)
      (Lifting.embed outcome) := by
    cases converted with
    | returned => exact .returned
    | unit _ same => rw [same]; exact .unit
    | fault => exact .fault
    | breaking => exact .breaking
    | continuing => exact .continuing
  exact .closure selected valid inputs.extended allocated lifted matched

include inputs in
theorem application {registry : Registry} {child caller : Scope}
    (selected : registry.Closure function child)
    {callContext : SourceSemantics.Context} {callerEvidence invocationEvidence : Dynamic.EvidenceEnvironment}
    {arguments : List Dynamic.Value} {before after : Dynamic.Heap}
    {size : Nat} {outcome : Dynamic.ExpressionOutcome}
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (raw : CallableIndexedOwnedStoredClosureSourceArguments.SourceArguments function before arguments)
    (arity : function.parameters.length = arguments.length)
    (trace : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) size
      callContext callerEvidence invocationEvidence before (.closure function) arguments outcome after) :
    Lifting.ApplicationLift (Program.ofChecked compiled.sourceProgram) registry caller callContext before
      (.closure function) arguments outcome after :=
  ⟨_, _, application_exact material inputs selected wellFormed raw arity trace, .completed⟩

include inputs in
theorem selected_application_exact {caller : Scope}
    {callContext : SourceSemantics.Context} {callerEvidence invocationEvidence : Dynamic.EvidenceEnvironment}
    {arguments : List Dynamic.Value} {before after : Dynamic.Heap}
    {size : Nat} {outcome : Dynamic.ExpressionOutcome}
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (raw : CallableIndexedOwnedStoredClosureSourceArguments.SourceArguments function before arguments)
    (arity : function.parameters.length = arguments.length)
    (trace : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) size
      callContext callerEvidence invocationEvidence before (.closure function) arguments outcome after) :
    Applies (Program.ofChecked compiled.sourceProgram) (SelectedCompilationPhysicalProgramSupport.stages compiled)
      caller callContext before (.closure function) arguments (Lifting.embed outcome) after := by
  obtain ⟨_sidecar, _accepted, selected⟩ := material.scope_at
  exact application_exact (registry := SelectedCompilationPhysicalProgramSupport.stages compiled)
    material inputs (.anonymous selected) wellFormed raw arity trace

include inputs in
/-- The selected child comes from the actual compiler packet retained by the
generalized read, using the public program's complete recursive registry. -/
theorem selected_application {caller : Scope}
    {callContext : SourceSemantics.Context} {callerEvidence invocationEvidence : Dynamic.EvidenceEnvironment}
    {arguments : List Dynamic.Value} {before after : Dynamic.Heap}
    {size : Nat} {outcome : Dynamic.ExpressionOutcome}
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (raw : CallableIndexedOwnedStoredClosureSourceArguments.SourceArguments function before arguments)
    (arity : function.parameters.length = arguments.length)
    (trace : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) size
      callContext callerEvidence invocationEvidence before (.closure function) arguments outcome after) :
    Lifting.ApplicationLift (Program.ofChecked compiled.sourceProgram)
      (SelectedCompilationPhysicalProgramSupport.stages compiled) caller callContext before
      (.closure function) arguments outcome after := by
  obtain ⟨_sidecar, _accepted, selected⟩ := material.scope_at
  exact application (registry := SelectedCompilationPhysicalProgramSupport.stages compiled) material inputs (.anonymous selected) wellFormed raw arity trace

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
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (raw : CallableIndexedOwnedStoredClosureSourceArguments.SourceArguments function before arguments)
    (arity : function.parameters.length = arguments.length)
    (trace : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) size
      callContext callerEvidence invocationEvidence before (.closure function) arguments outcome after) :
    Applies (Program.ofChecked compiled.sourceProgram) (SelectedCompilationPhysicalProgramSupport.stages compiled)
      caller callContext before (.closure function) arguments (Lifting.embed outcome) after := by
  cases association with
  | viewed material _view _typed =>
    obtain ⟨inputs⟩ := GeneralizedLocalBodyCompiler.entry_context material frame material.ownership
    exact selected_application_exact material inputs wellFormed raw arity trace

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalSourceApplicationLifting
