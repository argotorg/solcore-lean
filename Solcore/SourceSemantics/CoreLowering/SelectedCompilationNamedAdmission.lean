import Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedSourceTyping
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedParameterReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalNamedInvocationPreservation

/-! Selected named body certificates supply the actual parameter admission and
caller context transport. Body selection requires original owner uniqueness. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedAdmission
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionValues (Header NamedSourceAt)
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedAdmittedBodyEntries (SourceReceipt)
open SelectedCompilationNamedSourceTyping (Certified)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {header : Header compiled program}

/-- The receipt describes the heap created by this actual parameter allocation. -/
theorem parameter_source (certified : Certified header)
    {before reached : Dynamic.Heap} {arguments : List Dynamic.Value} {environment : Dynamic.Environment}
    (allocated : Dynamic.BindersAllocate [] before header.function.parameters arguments environment reached)
    (beforeTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types) :
    SourceReceipt program header.function header.context environment reached := by
  obtain ⟨facts, certificate⟩ := certified
  have frame : CallableCoercionMethodFrame.Frame header.sourceBody header.function :=
    ⟨header.frame.source, header.frame.context, header.frame.parameters, header.frame.result,
      header.frame.captured, header.frame.roots, header.frame.covers⟩
  obtain ⟨runtime, covers, heapTyped, locals, finalContext, typed, completes⟩ :=
    CallableIndexedOwnedBodySourceAdmission.admission_at_frame_parameters
      certificate.toBodyInstanceTypingCertificate frame header.extended allocated beforeTyped argumentsTyped
  exact ⟨runtime, covers, heapTyped, locals, finalContext, facts, typed, completes⟩

theorem caller_supports (certified : Certified header)
    {context : SourceSemantics.Context} {source : TypedSource}
    (runtime : Dynamic.SourceRuntimeValid program context source) :
    Dynamic.TypeContextSupports header.context context := by
  obtain ⟨facts, certificate⟩ := certified
  have inherited := Dynamic.MonoBindersExtend.runtimeContextFields header.extended
  have signatures : header.context.signatures = program.signatures :=
    inherited.signatures.trans
      ((congrArg (fun current : SourceSemantics.Context => current.signatures) header.frame.context).trans certificate.signatures_eq)
  have closed : header.context.typeParameters = [] :=
    inherited.typeParameters.trans
      ((congrArg (fun current : SourceSemantics.Context => current.typeParameters) header.frame.context).trans certificate.type_parameters_empty)
  have variables : header.context.typeVariables = [] :=
    inherited.typeVariables.trans
      ((congrArg (fun current : SourceSemantics.Context => current.typeVariables) header.frame.context).trans certificate.type_variables_empty)
  exact Dynamic.TypeContextSupports.ofClosed (runtime.signatures.trans signatures.symm)
    closed runtime.closed variables runtime.residual_variables_open

/-- Successful child receipts already carry the complete raw parameter row. -/
theorem arguments (certified : Certified header)
    {context : SourceSemantics.Context} {source : TypedSource} {heap : Dynamic.Heap}
    {values : List Dynamic.Value}
    (runtime : Dynamic.SourceRuntimeValid program context source)
    (heapTyped : Dynamic.HeapWellTyped context heap)
    (argumentsTyped : Dynamic.ValuesHaveTypes context heap values
      (header.bindings.map (fun binding => binding.1.scheme.body))) :
    Dynamic.HeapWellTyped header.function.context heap ∧
      Dynamic.ValuesHaveTypes header.function.context heap values header.types ∧
      Dynamic.TypeContextSupports header.context context := by
  obtain ⟨facts, certificate⟩ := certified
  have signatures := certificate.signatures_eq.trans runtime.signatures.symm
  have bodyHeap := heapTyped.transportClosed signatures runtime.closed certificate.type_parameters_empty
    runtime.variables_closed certificate.residual_type_variables_open
  have bodyArguments := argumentsTyped.transportClosed signatures runtime.closed certificate.type_parameters_empty
    runtime.variables_closed certificate.residual_type_variables_open
  have bodyTypes := Dynamic.MonoBindersExtend.bodyTypes_eq header.extended
  rw [header.parameters] at bodyTypes
  have types : header.types = header.bindings.map (fun binding => binding.1.scheme.body) := by
    simpa only [List.map_map, Function.comp_def] using bodyTypes.symm
  rw [← types] at bodyArguments
  exact ⟨header.frame.context.symm ▸ bodyHeap, header.frame.context.symm ▸ bodyArguments,
    caller_supports ⟨facts, certificate⟩ runtime⟩

variable {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {function : Dynamic.GlobalFunction}

private theorem roots_functional {nodes : List NodeId} {left right : List StatementId}
    (first : Dynamic.StatementRoots nodes left) (second : Dynamic.StatementRoots nodes right) : left = right := by
  induction first generalizing right with
  | nil => cases second; rfl
  | @cons id nodes left first ih => cases second with
    | cons remaining => exact congrArg (List.cons id) (ih remaining)

/-- Inversion uses the retained global instantiation and actual selected scope.
It preserves the original staged body outcome instead of wrapping an ordinary
execution. Source arity excludes only the separate pre-allocation fault. -/
theorem body_prefix {header : Header compiled (Program.ofChecked compiled.sourceProgram)} (sourceAt : NamedSourceAt header rawD function)
    (owners : ((Program.ofChecked compiled.sourceProgram).functions.map (fun definition => definition.body.owner)).Nodup)
    {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
    {context : SourceSemantics.Context} {before after : Dynamic.Heap}
    {arguments : List Dynamic.Value} {outcome : Staging.Recursive.Outcome} {size : Nat}
    (arity : header.function.parameters.length = arguments.length)
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) stages size invocation context before
      (.global function) arguments outcome after) :
    ∃ bodySize child environment bound finalContext bodyOutcome,
      stages.Closure header.function child ∧
      Dynamic.BindersAllocate [] before header.function.parameters arguments environment bound ∧
      Staging.Recursive.Size.Statements (Program.ofChecked compiled.sourceProgram) stages bodySize child header.context environment bound
        header.function.body finalContext bodyOutcome after ∧
      Staging.Recursive.BodyResult header.function.resultType bodyOutcome outcome ∧ bodySize < size := by
  have bodyUnique : ∀ actual, Dynamic.FunctionInstantiates (Program.ofChecked compiled.sourceProgram) function.instantiation actual →
      RecursiveNamedCatalog.Header.sourceBody header = actual := by
    intro actual instantiated
    exact BuiltinNamedCalls.instantiation_unique owners
      sourceAt.frame.instantiated instantiated
  cases trace with
  | @globalArity _ _ _ _ _ bodyInstance instantiates mismatch =>
    have same := bodyUnique bodyInstance instantiates
    cases same
    exact False.elim (mismatch (by simpa only [sourceAt.frame.parameters] using arity))
  | @global bodySize _ _ _ bound _ _ _ environment parameterTypes bodyContext finalContext
      bodyInstance roots child bodyOutcome _ instantiates covers rootsEq selected parameters allocate body converted =>
    have same := bodyUnique bodyInstance instantiates
    cases same
    have sameRoots := roots_functional rootsEq sourceAt.frame.roots
    subst_vars
    have actualParameters : MonoBindersExtend header.function.source.owner header.function.context
        header.function.parameters parameterTypes bodyContext := by
      simpa only [sourceAt.frame.source, sourceAt.frame.context, sourceAt.frame.parameters] using parameters
    have sameTypes := header.extended.bodyTypes_eq.symm.trans actualParameters.bodyTypes_eq
    subst_vars
    have sameContext := (header.extended.functional actualParameters).symm
    subst_vars
    have actualSelected : stages.Closure header.function child := by
      simpa only [CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts.global_view sourceAt] using selected
    exact ⟨_, _, _, _, _, _, actualSelected, sourceAt.frame.parameters.symm ▸ allocate,
      body, sourceAt.frame.result.symm ▸ converted,
      Staging.Recursive.Size.child_lt_stepSize (by simp)⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedAdmission
