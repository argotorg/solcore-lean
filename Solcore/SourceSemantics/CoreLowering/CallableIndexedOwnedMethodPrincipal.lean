import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodCaptureReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedActualNamedSourceReceipts

/-! A selected implementation method has independent Source authority and an
emitted named compiler seed. The compiler's synthetic function does not assert
top-level FunctionInstantiates. Exact cached preparation authenticates the full
Source seed; the real selector retains the method body and dictionary. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodPrincipal
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallablePreparedMethodRuntimeMeaning

/-- The original complete method selector accompanies its genuine cached row.
The Source dictionary and caller context are retained without projection. -/
structure Principal (compiled : SourceCoreUnifiedCompilation.Compiled)
    (method : ExecutableImplMethods.CheckedMethod) where
  cached : CallablePreparedMethodSelection.Cached compiled method.specialized
  callerContext : SourceSemantics.Context
  callerEvidence : Dynamic.EvidenceEnvironment
  traitName : String
  methodName : String
  requirements : List RequirementId
  dictionary : Dynamic.EvidenceEnvironment
  selected : Dynamic.OperatorMethodSelected (Program.ofChecked compiled.sourceProgram)
    callerContext callerEvidence traitName methodName requirements
    (CallableCoercionMethodInstantiation.bodyInstance compiled.sourceProgram method) dictionary

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {method : ExecutableImplMethods.CheckedMethod}

/-- Construction keeps the actual Source selector and cached compiler row. -/
def of_selected
    (cached : CallablePreparedMethodSelection.Cached compiled method.specialized)
    {context : SourceSemantics.Context} {caller dictionary : Dynamic.EvidenceEnvironment}
    {traitName methodName : String} {requirements : List RequirementId}
    (selected : Dynamic.OperatorMethodSelected (Program.ofChecked compiled.sourceProgram)
      context caller traitName methodName requirements
      (CallableCoercionMethodInstantiation.bodyInstance compiled.sourceProgram method) dictionary) :
    Principal compiled method :=
  ⟨cached, context, caller, traitName, methodName, requirements, dictionary, selected⟩

abbrev Principal.named (principal : Principal compiled method) : SourceCoreGeneralFunctions.Function :=
  principal.cached.named

abbrev Principal.sourceBody (principal : Principal compiled method) : Dynamic.BodyInstance :=
  let _ := principal
  CallableCoercionMethodInstantiation.bodyInstance compiled.sourceProgram method

abbrev Principal.sourceFunction (principal : Principal compiled method) : Dynamic.Closure :=
  methodFunction principal.cached.compilation principal.sourceBody principal.dictionary

/-- The same cached specialization fixes every Source node of the method. -/
theorem Principal.source_eq (principal : Principal compiled method) :
    CallableIndexedNamedGeneration.source principal.named = principal.sourceBody.source := by
  simp only [Principal.named, Principal.sourceBody, CallableIndexedNamedGeneration.source,
    principal.cached.same, CallableCoercionMethodInstantiation.bodyInstance]

/-- The full selector yields the genuine method frame, including its exact
dictionary, empty captures and emitted ordered statement roots. -/
theorem Principal.source_frame (principal : Principal compiled method) :
    CallableCoercionMethodFrame.Frame principal.sourceBody principal.sourceFunction :=
  principal.cached.frame principal.selected

/-- The actual Source authority is TraitMethodInstantiates. No ordinary named
function declaration is supplied by the synthetic compiler signature. -/
theorem Principal.source_instantiation (principal : Principal compiled method) :
    ∃ implementation methodSignature trait definition substitution,
      Dynamic.TraitMethodInstantiates (Program.ofChecked compiled.sourceProgram)
        implementation methodSignature trait definition substitution principal.sourceBody := by
  rcases principal with ⟨cached, context, caller, traitName, methodName, requirements, dictionary, selected⟩
  cases selected with
  | intro _ _ _ _ _ _ _ _ _ _ _ instantiated _ _ =>
    exact ⟨_, _, _, _, _, instantiated⟩

/-- The caller's real selector retains its complete callee evidence coverage. -/
theorem Principal.dictionary_covers (principal : Principal compiled method) :
    principal.dictionary.Covers principal.sourceBody.context :=
  principal.source_frame.covers

/-- Full cached preparation authenticates the exact specialization selected by
the accepted named hook, even when the original body is a trait method. -/
theorem Principal.record (principal : Principal compiled method) :
    SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan
      principal.named.signature.key = .ok principal.named.specialized :=
  CallableIndexedActualNamedSourceReceipts.cached_record compiled
    principal.cached.selected principal.cached.compilation.hook

/-- The emitted hook installs the complete compiler Source seed. Its physical
frame is supplied separately by the actual method parameter entry. -/
theorem Principal.hook_history (principal : Principal compiled method) :
    ∃ origin,
      compiled.indexed.ancestry.graph.inputs.callable.table.idAt?
        (.named principal.named.signature.key) = some origin ∧
      Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
        (SourceCoreCallableIndexedDispatch.namedFrame compiled.indexed.ancestry.graph.table origin)
        (.named origin) (some (CallableIndexedNamedGeneration.state principal.named)) ∧
      principal.cached.compilation.output = SourceCoreCallableIndexedFrames.withFrame
        (.var (compiled.indexed.base.globals.length + 1))
        (SourceCoreCallableIndexedDispatch.literal compiled.indexed.ancestry.layout.frame
          (SourceCoreCallableIndexedDispatch.namedFrame compiled.indexed.ancestry.graph.table origin))
        principal.cached.compilation.parameterCode :=
  principal.cached.compilation.history principal.record

/-- The real hook's original named history agrees with that same full Source
seed. Neither native typing nor a generic stable-owner gate identifies it. -/
theorem Principal.history_source (principal : Principal compiled method)
    {origin : Word} {native : NativeFrame} {metadata : MetadataState}
    (selected : compiled.indexed.ancestry.graph.inputs.callable.table.idAt?
      (.named principal.named.signature.key) = some origin)
    (history : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      native (.named origin) (some metadata)) :
    Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      native (.named origin) (some (CallableIndexedNamedGeneration.state principal.named)) := by
  have generated := CallableIndexedNamedGeneration.seed compiled.indexed selected principal.record
  have authenticated := history.authenticates
  cases authenticated with
  | named actual =>
    have same : metadata = CallableIndexedNamedGeneration.state principal.named :=
      Option.some.inj (actual.symm.trans generated)
    exact same ▸ history

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodPrincipal
