import Solcore.SourceSemantics.CoreLowering.CallableCoercionSourceSelection
import Solcore.SourceSemantics.CoreLowering.CallableIndexedNamedGeneration
import Solcore.SourceSemantics.CoreLowering.NamedCallSource

/-! A selected source method has an exact body, ordered evidence and empty
lexical entry. A closure-shaped proof view relates its body trace to the
independent BodyInvokes/BodyFaults judgments. It is not a source closure or an
ordinary FunctionInstantiates claim. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableCoercionMethodFrame
open Frontend SourceInference
open CallableNamedMetadata (environment)
open CallableCoercionMethodInstantiation (bodyInstance Formation)

/-- Only source attribution belongs to this frame. Native captures and body
execution are separate judgments. -/
structure Frame (body : Dynamic.BodyInstance) (function : Dynamic.Closure) : Prop where
  source : function.source = body.source
  context : function.context = body.context
  parameters : function.parameters = body.source.inputs
  result : function.resultType = body.resultType
  captured : function.captured = []
  roots : Dynamic.StatementRoots body.source.roots function.body
  covers : function.evidence.Covers body.context

def view (body : Dynamic.BodyInstance) (evidence : Dynamic.EvidenceEnvironment)
    (statements : List StatementId) : Dynamic.Closure := {
  parameters := body.source.inputs, resultType := body.resultType, body := statements
  source := body.source, captured := [], context := body.context, evidence
}

abbrev BodyOutcome := NamedCalls.BodyOutcome

private theorem roots_of_map {source : TypedSource} {statements : List StatementId}
    (accepted : source.roots.mapM (m := Except SourceCoreGeneralFunctions.Error) (fun
      | .statement id => pure id | .expression id => throw (.expectedStatementRoot id)) = .ok statements) :
    Dynamic.StatementRoots source.roots statements := by
  generalize source.roots = roots at accepted ⊢
  induction roots generalizing statements with
  | nil => cases accepted; exact .nil
  | cons head rest ih =>
    cases head with
    | expression id => cases accepted
    | statement id =>
      simp only [List.mapM_cons, pure, Except.pure, bind, Except.bind] at accepted
      cases lowered : List.mapM (fun x => match x with
        | .statement id => Except.ok id
        | .expression id => throw (SourceCoreGeneralFunctions.Error.expectedStatementRoot id)) rest with
      | error error => simp only [lowered] at accepted; cases accepted
      | ok tail =>
        simp only [lowered] at accepted
        cases accepted
        exact .cons (ih lowered)


/-- Any actual source method selection supplies the same closure-shaped body
view. The emitted compilation contributes its exact ordered statement roots. -/
theorem of_selected {program : Program} {context : SourceSemantics.Context}
    {caller dictionary : Dynamic.EvidenceEnvironment} {traitName methodName : String}
    {requirements : List RequirementId} {body : Dynamic.BodyInstance}
    (selected : Dynamic.OperatorMethodSelected program context caller traitName methodName
      requirements body dictionary)
    {checked : SourceCoreCompatibleCatalog.Checked} {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
    {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Core.Expr}
    (compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code)
    (sameSource : CallableIndexedNamedGeneration.source named = body.source) :
    Frame body (view body dictionary compiled.statements) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · simpa only [sameSource, view] using roots_of_map compiled.roots
  · cases selected with | intro _ _ _ _ _ _ _ _ _ _ _ _ _ covers => exact covers

/-- The actual method selector and dictionary construct the source frame at
its actual residual context. The compiled root traversal supplies the body. -/
theorem of_compilation {loaded : LoadedProgram} {program : CheckedProgram}
    (loadedAccepted : Frontend.checkLoadedProgram loaded 1024 = .ok program)
    {caller : SourceSpecialization.SpecializedFunction} {node : ExpressionNode}
    {available dictionary : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    {step : CoercionStep} {method : ExecutableImplMethods.CheckedMethod} {context : SourceSemantics.Context}
    (receipt : CallableCoercionSourceSelection.Certificate program caller node available step method)
    (formed : Formation receipt.selected.implementation receipt.selected.declaration)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures program.signatures) method.specialized.parameterSubstitution)
    (signatures : context.signatures = program.signatures)
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (assumptions : ∀ goal, goal ∈ caller.assumptions → goal ∈ context.assumptions)
    (resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions = .ok available)
    (covered : CallableCoercionEvidenceOrigins.CallerCovered caller method)
    (materialized : SourceCompilationPlan.coercionMethodRuntimeEvidence program caller node step method = .ok dictionary)
    {checked : SourceCoreCompatibleCatalog.Checked} {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
    {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Core.Expr}
    (compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code)
    (completeRecord : named.specialized = method.specialized) :
    Dynamic.OperatorMethodSelected (Program.ofChecked program) context (environment available) "Coerce" "coerce"
      (step.requirement :: step.methodRequirements) (bodyInstance program method) (environment dictionary) ∧
    Frame (bodyInstance program method) (view (bodyInstance program method) (environment dictionary) compiled.statements) := by
  have selected := receipt.selects loadedAccepted formed range signatures ledger assumptions resolved covered materialized
  refine ⟨selected, of_selected selected compiled ?_⟩
  simp only [CallableIndexedNamedGeneration.source, completeRecord, bodyInstance]

variable {program : Program} {bodyInstance : Dynamic.BodyInstance} {function : Dynamic.Closure}

theorem Frame.body_of_trace {types : List TypeSystem.Ty} {context : SourceSemantics.Context}
    {before bound after : Dynamic.Heap} {arguments : List Dynamic.Value}
    {environment : Dynamic.Environment} {outcome : Dynamic.ExpressionOutcome}
    (frame : Frame bodyInstance function)
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
    (allocated : Dynamic.BindersAllocate [] before function.parameters arguments environment bound)
    (trace : FunctionCallBody.Trace program function context environment bound outcome after) :
    BodyOutcome program bodyInstance function.evidence before arguments outcome after := by
  have extension : MonoBindersExtend bodyInstance.source.owner bodyInstance.context bodyInstance.source.inputs types context := by
    simpa only [frame.source, frame.context, frame.parameters] using extended
  have allocation : Dynamic.BindersAllocate [] before bodyInstance.source.inputs arguments environment bound :=
    frame.parameters ▸ allocated
  cases trace with
  | returned executed =>
      exact .value (.returned frame.covers frame.roots extension allocation (frame.source ▸ executed) rfl)
  | unit same executed =>
      exact .value (.unit frame.covers (frame.result ▸ same) frame.roots extension allocation
        (frame.source ▸ executed) ⟨_, rfl⟩)
  | fault failed =>
      exact .fault (.statements frame.roots extension allocation (frame.source ▸ failed))
  | escaped executed escape =>
      exact .fault (.controlEscape frame.roots extension allocation (frame.source ▸ executed) escape)

private theorem roots_functional {nodes : List NodeId} {left right : List StatementId}
    (first : Dynamic.StatementRoots nodes left) (second : Dynamic.StatementRoots nodes right) : left = right := by
  induction first generalizing right with
  | nil => cases second; rfl
  | @cons id nodes left first ih => cases second with | cons remaining => exact congrArg (List.cons id) (ih remaining)

/-- Invert the independent body invocation at the statically retained call
context. Exact roots and monomorphic binder extension identify that context;
arity excludes the separate source arity-fault rule. -/
theorem Frame.trace_of_body {types : List TypeSystem.Ty} {context : SourceSemantics.Context}
    {before after : Dynamic.Heap} {arguments : List Dynamic.Value} {outcome : Dynamic.ExpressionOutcome}
    (frame : Frame bodyInstance function)
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
    (arity : function.parameters.length = arguments.length)
    (executed : BodyOutcome program bodyInstance function.evidence before arguments outcome after) :
    ∃ environment bound,
      Dynamic.BindersAllocate [] before function.parameters arguments environment bound ∧
      FunctionCallBody.Trace program function context environment bound outcome after := by
  have rootsUnique : ∀ {roots}, Dynamic.StatementRoots bodyInstance.source.roots roots → roots = function.body := by
    intro roots selected
    exact roots_functional selected frame.roots
  have contextUnique : ∀ {inputTypes actualContext},
      MonoBindersExtend bodyInstance.source.owner bodyInstance.context bodyInstance.source.inputs inputTypes actualContext →
      actualContext = context := by
    intro inputTypes actualContext extension
    have actual : MonoBindersExtend function.source.owner function.context function.parameters inputTypes actualContext := by
      simpa only [frame.source, frame.context, frame.parameters] using extension
    have same : types = inputTypes := extended.bodyTypes_eq.symm.trans actual.bodyTypes_eq
    subst inputTypes
    exact (extended.functional actual).symm
  cases executed with
  | value invokes =>
    cases invokes with
    | returned covers roots extension allocated execution returned =>
      have sameRoots := rootsUnique roots
      have sameContext := contextUnique extension
      subst_vars
      exact ⟨_, _, frame.parameters.symm ▸ allocated, .returned (frame.source.symm ▸ execution)⟩
    | unit covers same roots extension allocated execution fellThrough =>
      have sameRoots := rootsUnique roots
      have sameContext := contextUnique extension
      obtain ⟨_, rfl⟩ := fellThrough
      subst_vars
      exact ⟨_, _, frame.parameters.symm ▸ allocated, .unit (frame.result.symm ▸ same) (frame.source.symm ▸ execution)⟩
  | fault fails =>
    cases fails with
    | arity mismatch => exact False.elim (mismatch (by simpa only [frame.parameters] using arity))
    | statements roots extension allocated failed =>
      have sameRoots := rootsUnique roots
      have sameContext := contextUnique extension
      subst_vars
      exact ⟨_, _, frame.parameters.symm ▸ allocated, .fault (frame.source.symm ▸ failed)⟩
    | controlEscape roots extension allocated executed escape =>
      have sameRoots := rootsUnique roots
      have sameContext := contextUnique extension
      subst_vars
      exact ⟨_, _, frame.parameters.symm ▸ allocated, .escaped (frame.source.symm ▸ executed) escape⟩


end Solcore.SourceSemantics.CoreLowering.CallableCoercionMethodFrame
