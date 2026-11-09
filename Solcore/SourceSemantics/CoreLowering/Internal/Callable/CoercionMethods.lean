import Solcore.SourceSemantics.CoreLowering.Internal.Callable.CoercionSpine
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.CoercionSourceSelection
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedLambdaValues
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.GlobalInitialization
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.BuiltinBodies

/-!
# Coercions: methods and paths

Method frames and entries of coercions, method body meaning, coercion paths and their selected invocation.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableCoercionMethodFrame
/-! A selected source method has an exact body, ordered evidence and empty
lexical entry. A closure-shaped proof view relates its body trace to the
independent BodyInvokes/BodyFaults judgments. It is not a source closure or an
ordinary FunctionInstantiates claim. -/
set_option autoImplicit false
set_option Elab.async false
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
      cases lowered : List.mapM (m := Except SourceCoreGeneralFunctions.Error) (fun x => match x with
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
theorem of_compilation {program : CheckedProgram}
    (loadedAccepted : CallableMethodBodyCoherence.Checked program)
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableCoercionMethodBodyMeaning
/-! The real indexed method prefix and a concrete builtin lexical body give
finite preservation and completed reflection for a fixed selected dictionary.
The semantic source frame retains residual type variables. Installed native
code, captures and administrative history remain explicit runtime receipts;
no body execution law is stored in a static certificate. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableCoercionMethodBody
open Core Frontend SourceInference GeneralHeap CoreProof ReadOnly CompatiblePayload
open CallableAncestryPairedLookup CallableIndexedHistory CallableIndexedParameterCertificates CallableIndexedParameterMeaning
open SourceCoreCallableIndexedFrames
open CallableCoercionMethodFrame (Frame BodyOutcome)

/-- The actual installed global cell retains its saved body and captures.
This observation grants no source attribution or body meaning. -/
structure Installed (call : CallableCoercionSpine.Call) (code : Expr) (ξ : Renaming)
    (caller captured : Environment) (store : Store) where
  location : Location
  lookup : caller[call.index]? = some (.cellRef (.sum .unit (.function call.signature.parameterType
    (LanguageResult.resultType call.signature.resultType))) location)
  read : store.read? location = some (.inRight .unit (.closure call.signature.parameterType
    (LanguageResult.resultType call.signature.resultType) (code.rename ξ) captured))

theorem Installed.invokes {call : CallableCoercionSpine.Call} {code : Expr} {ξ : Renaming}
    {caller captured : Environment} {store after : Store} {input result : Value}
    (installed : Installed call code ξ caller captured store)
    (executed : Evaluates (input :: captured) store (code.rename ξ) result after) (reason : Word) :
    CallableCoercionSpine.Invoke caller reason call store (.inRight .word input) result after :=
  .applied installed.lookup installed.read executed

/-- Reading this exact cell rules out an absent global. Inversion keeps the
stored code and captures unchanged, including under caller-slot renaming. -/
theorem Installed.completed {call : CallableCoercionSpine.Call} {code : Expr} {ξ : Renaming}
    {caller captured : Environment} {store after : Store} {input result : Value} {reason : Word}
    (installed : Installed call code ξ caller captured store)
    (completed : CallableCoercionSpine.Invoke caller reason call store (.inRight .word input) result after) :
    Evaluates (input :: captured) store (code.rename ξ) result after := by
  cases completed with
  | absent reference read =>
    have same := Option.some.inj (reference.symm.trans installed.lookup)
    cases same
    have impossible := Option.some.inj (read.symm.trans installed.read)
    cases impossible
  | applied reference read body =>
    have same := Option.some.inj (reference.symm.trans installed.lookup)
    cases same
    have same := Option.some.inj (read.symm.trans installed.read)
    cases same
    exact body

/-- The actual named callback uses this exact loop policy and source, including
its real diagnostic table. This is a compiler equation, not a body law. -/
theorem loops_accepted {checked : Checked} {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
    {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
    (compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code) :
    SourceCoreLoops.lowerStatementsWithPolicy
      (CompatibleNamedBody.bodyPolicy ((CallableIndexedNamedGeneration.representation prepared).atContext named.signature.key [])
        prepared.base.sourceProgram prepared.base.sourceProgram.signatures prepared.base.locals compiled.parents
        compiled.own.assignments diagnostics (CallableIndexedNamedGeneration.context prepared named) prepared.base.callableContext)
      prepared.fuel (CallableIndexedNamedGeneration.source named)
      (named.inputs.reverse.map fun binding => (binding.1.id, binding.2)) compiled.statements named.signature.resultType
      (diagnostics.reasonAt named.signature.key) compiled.own.fellThroughReason compiled.own.table.escapedReason = .ok compiled.body :=
  compiled.bodyCompiled

/-- The actual accepted callback is retained even when its independent source
context has residualTypeVariables=true. Tree/Syntax are an explicit finite
static profile; no ordinary contextual-extractor premise is imposed. -/
theorem certificate {checked : Checked} {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
    {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
    (compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code)
    {values : SourceCoreCompatibleValues.Context} {context : SourceSemantics.Context}
    {readFuel : Nat} {expected : TypeSystem.Ty} {flow : Expr}
    (projection : values.checked.catalog.project expected = .ok named.signature.resultType)
    (syntaxTree : BuiltinLexicalStatements.Syntax (CallableIndexedNamedGeneration.source named) context true compiled.statements expected)
    (emitted : compiled.body = CompatibleStatements.finish named.signature.resultType flow compiled.own.fellThroughReason compiled.own.table.escapedReason)
    (tree : BuiltinLexicalStatements.Tree prepared.layouts named.signature.key [] prepared.ancestry.layout.frame prepared.base.globals.length
      (fun error => .sourceAllocation (reprStr error)) readFuel values (CallableIndexedNamedGeneration.source named)
      named.specialized.function.solvedRequirements (diagnostics.reasonAt named.signature.key) context
      (named.inputs.reverse.map fun binding => (binding.1.id, binding.2)) true compiled.statements expected named.signature.resultType flow) :
    Nonempty (BuiltinNamedBody.Certificate prepared.layouts named.signature.key [] prepared.ancestry.layout.frame prepared.base.globals.length
      (fun error => .sourceAllocation (reprStr error)) readFuel values (CallableIndexedNamedGeneration.source named) context
      named.specialized.function.solvedRequirements (diagnostics.reasonAt named.signature.key)
      (named.inputs.reverse.map fun binding => (binding.1.id, binding.2)) compiled.statements expected named.signature.resultType
      (CompatibleNamedBody.bodyPolicy ((CallableIndexedNamedGeneration.representation prepared).atContext named.signature.key [])
        prepared.base.sourceProgram prepared.base.sourceProgram.signatures prepared.base.locals compiled.parents
        compiled.own.assignments diagnostics (CallableIndexedNamedGeneration.context prepared named) prepared.base.callableContext)
      prepared.fuel compiled.own.fellThroughReason compiled.own.table.escapedReason compiled.body) :=
  BuiltinNamedBody.of_tree (loops_accepted compiled) projection syntaxTree emitted tree

variable {checked : Checked} {base : Base checked}
  (prepared : SourceCoreCallableIndexedAncestry.Prepared base)
  {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : CompatiblePayload.FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) {function : Dynamic.Closure} {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {readFuel : Nat} {bindings : List Binding} {output : Ty} {policy : SourceCoreLoops.Policy}
  {fuel : Nat} {fellThrough escaped : Word} {body parameterCode : Expr}
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {allocationGlobals : Nat}
  (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
  (certificate : BuiltinNamedBody.Certificate layouts owner active prepared.layout.frame allocationGlobals onError readFuel values function.source context solved reasonAt
    (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) function.body function.resultType output
    policy fuel fellThrough escaped body)
  (parameters : function.parameters = bindings.map Prod.fst)
  (inputs : function.source.inputs = bindings.map Prod.fst)
  (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
  (contextValid : CompatibleExpressionLiterals.ContextValid solved context function.evidence)
  (unique : NodeOccurrencesUnique function.source) {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, CompatiblePayload.MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (acceptedPrefix : SourceCoreSourceCells.bindParameters
    (SourceCoreCallableIndexedAllocationFrames.allocator prepared.layout.frame allocationGlobals
      (layouts.allocatorAt owner active onError)) function.source [] bindings output
    SourceCoreFunctions.argumentProjection body = .ok parameterCode)
  (definitions : layouts.definitions = ambient.definitions) (registered : prepared.layout.frame.Registered ambient.definitions)
  {named : SourceCoreGeneralFunctions.Function} {code : Expr} {ξ : Renaming}
  (acceptedHook : SourceCoreCallableIndexedAncestry.namedBody prepared named parameterCode = .ok code)
  {mapping : LocationMap} {world : StoreTyping} {arguments : List Dynamic.Value} {nativeArguments : List Value}
  (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    mapping world bindings arguments nativeArguments)
  {administrative actualContext : Core.Context} {canonical actual : Environment} {before : Dynamic.Heap} {store : Store}
  {location : Location} {current : NativeFrame} {currentGhost : GhostFrame}
  {records : List CallableIndexedSnapshots.Record}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
    administrative [] [] canonical ambient.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
  (initialLocals : Dynamic.EnvironmentAgrees before function.context.locals [])
  (actualLayout : EnvironmentsAgree ξ (DataPatternValues.packValues nativeArguments :: canonical) actual)
  (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
  (canonicalReference : canonical[allocationGlobals]? = some (.cellRef prepared.layout.frame.type location))
  (actualReference : actual[ξ (base.globals.length + 1)]? = some (.cellRef prepared.layout.frame.type location))
  (unmapped : location ∉ mapping) (typed : world[location]? = some prepared.layout.frame.type)
  (caller : CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location current currentGhost store)
  (snapshots : CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame mapping store records)

  {sourceBody : Dynamic.BodyInstance}
  (sourceFrame : Frame sourceBody function)

include parameters extended represented sourceFrame in
/-- Shared source-method entry. Runtime and ordinary consumers supply their
concrete hook proof through this internal continuation. -/
theorem preserves_with
    (continuation : ∀ {environment : Dynamic.Environment} {bound after : Dynamic.Heap}
      {outcome : Dynamic.ExpressionOutcome},
      Dynamic.BindersAllocate [] before function.parameters arguments environment bound →
      FunctionCallBody.Trace program function context environment bound outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location current currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame finalMap finalStore records)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : BodyOutcome program sourceBody function.evidence before arguments outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location current currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame finalMap finalStore records := by
  have arity : function.parameters.length = arguments.length := by
    rw [parameters]
    simpa only [List.length_map] using represented.length.1
  obtain ⟨environment, bound, allocated, bodyTrace⟩ := sourceFrame.trace_of_body extended arity trace
  exact continuation allocated bodyTrace

include extended sourceFrame in
/-- Only the independently selected method frame turns a reflected actual hook
result into its source method body judgment. -/
theorem reflects_with {value : Value} {finalStore : Store}
    (continuation :
    ∃ environment bound outcome after finalMap finalWorld,
      Dynamic.BindersAllocate [] before function.parameters arguments environment bound ∧
      FunctionCallBody.Trace program function context environment bound outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location current currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame finalMap finalStore records) :
    ∃ outcome after finalMap finalWorld,
      BodyOutcome program sourceBody function.evidence before arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location current currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame finalMap finalStore records := by
  obtain ⟨environment, bound, outcome, after, finalMap, finalWorld, allocated, trace,
    related, finalHeaps, maps, worlds, frame, metadata, finalCaller, finalSnapshots⟩ := continuation
  exact ⟨outcome, after, finalMap, finalWorld, sourceFrame.body_of_trace extended allocated trace,
    related, finalHeaps, maps, worlds, frame, metadata, finalCaller, finalSnapshots⟩

include certificate parameters inputs extended acceptedPrefix definitions registered represented environments heaps initialLocals
  actualLayout canonicalReference actualReference unmapped typed caller snapshots acceptedHook extension
  contextValid unique uninitialized missing faithful functionLeaves functionTypes actualTyped sourceFrame in
/-- Independent method body execution drives the actual marked parameters,
frame install, concrete body and restoration. The selected evidence is fixed. -/
theorem preserves [FunctionCalls.FaultTokens faults] {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : BodyOutcome program sourceBody function.evidence before arguments outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location current currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame finalMap finalStore records := by
  apply preserves_with (prepared := prepared) (functions := functions) (program := program)
    (parameters := parameters) (extended := extended) (represented := represented) (sourceFrame := sourceFrame)
    (trace := trace)
  intro environment bound after outcome allocated bodyTrace
  obtain ⟨_, _, _, value, finalStore, finalMap, finalWorld, _, _, evaluated, related,
    finalHeaps, maps, worlds, frame, metadata, finalCaller, finalSnapshots, _⟩ :=
    BuiltinNamedCalls.hook_preserves
      (prepared := prepared) (functions := functions) (extension := extension) (program := program)
      (onError := onError) (certificate := certificate) (parameters := parameters) (inputs := inputs)
      (extended := extended) (contextValid := contextValid) (unique := unique) (uninitialized := uninitialized)
      (missing := missing) (faithful := faithful) (functionLeaves := functionLeaves) (functionTypes := functionTypes)
      (acceptedPrefix := acceptedPrefix) (definitions := definitions) (registered := registered) (acceptedHook := acceptedHook)
      (represented := represented) (environments := environments) (heaps := heaps) (initialLocals := initialLocals)
      (actualLayout := actualLayout) (actualTyped := actualTyped) (canonicalReference := canonicalReference) (actualReference := actualReference)
      (unmapped := unmapped) (typed := typed) (caller := caller) (snapshots := snapshots) allocated bodyTrace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, related, finalHeaps, maps, worlds,
    frame, metadata, finalCaller, finalSnapshots⟩

include certificate parameters inputs extended acceptedPrefix definitions registered represented environments heaps initialLocals
  actualLayout canonicalReference actualReference unmapped typed caller snapshots acceptedHook extension
  contextValid unique uninitialized missing faithful functionLeaves functionTypes actualTyped sourceFrame in
/-- A completed real hook supplies source allocation and a concrete body
trace. Source method invocation follows without ordinary global instantiation. -/
theorem reflects [FunctionCalls.FaultTokens faults] {value : Value} {finalStore : Store}
    (completed : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      BodyOutcome program sourceBody function.evidence before arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location current currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame finalMap finalStore records := by
  obtain ⟨_, _, _, environment, bound, outcome, after, finalMap, finalWorld, _, _, allocated, trace,
    related, finalHeaps, maps, worlds, frame, metadata, finalCaller, finalSnapshots, _⟩ :=
    BuiltinNamedCalls.hook_reflects
      (prepared := prepared) (functions := functions) (extension := extension) (program := program)
      (onError := onError) (certificate := certificate) (parameters := parameters) (inputs := inputs)
      (extended := extended) (contextValid := contextValid) (unique := unique) (uninitialized := uninitialized)
      (missing := missing) (faithful := faithful) (functionLeaves := functionLeaves) (functionTypes := functionTypes)
      (acceptedPrefix := acceptedPrefix) (definitions := definitions) (registered := registered) (acceptedHook := acceptedHook)
      (represented := represented) (environments := environments) (heaps := heaps) (initialLocals := initialLocals)
      (actualLayout := actualLayout) (actualTyped := actualTyped) (canonicalReference := canonicalReference) (actualReference := actualReference)
      (unmapped := unmapped) (typed := typed) (caller := caller) (snapshots := snapshots) completed
  exact reflects_with (prepared := prepared) (functions := functions) (program := program)
    (extended := extended) (sourceFrame := sourceFrame)
    ⟨environment, bound, outcome, after, finalMap, finalWorld, allocated, trace,
      related, finalHeaps, maps, worlds, frame, metadata, finalCaller, finalSnapshots⟩

include certificate parameters inputs extended acceptedPrefix definitions registered represented environments heaps initialLocals
  actualLayout canonicalReference actualReference unmapped typed caller snapshots acceptedHook extension
  contextValid unique uninitialized missing faithful functionLeaves functionTypes actualTyped sourceFrame in
theorem invoke_preserves [FunctionCalls.FaultTokens faults] {call : CallableCoercionSpine.Call} {callerEnvironment captured : Environment}
    {input : Dynamic.Value} {nativeInput : Value} {reason : Word}
    (sourceArgument : arguments = [input]) (nativeArgument : nativeArguments = [nativeInput])
    (entry : actual = nativeInput :: captured)
    (installed : Installed call code ξ callerEnvironment captured store)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : BodyOutcome program sourceBody function.evidence before [input] outcome after) :
    ∃ value finalStore finalMap finalWorld,
      CallableCoercionSpine.Invoke callerEnvironment reason call store (.inRight .word nativeInput) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location current currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame finalMap finalStore records := by
  subst arguments nativeArguments actual
  obtain ⟨value, finalStore, finalMap, finalWorld, executed, rest⟩ :=
    preserves
      (prepared := prepared) (functions := functions) (extension := extension) (program := program)
      (onError := onError) (certificate := certificate) (parameters := parameters) (inputs := inputs)
      (extended := extended) (contextValid := contextValid) (unique := unique) (uninitialized := uninitialized)
      (missing := missing) (faithful := faithful) (functionLeaves := functionLeaves) (functionTypes := functionTypes)
      (acceptedPrefix := acceptedPrefix) (definitions := definitions) (registered := registered) (acceptedHook := acceptedHook)
      (represented := represented) (environments := environments) (heaps := heaps) (initialLocals := initialLocals)
      (actualLayout := actualLayout) (actualTyped := actualTyped) (canonicalReference := canonicalReference) (actualReference := actualReference)
      (unmapped := unmapped) (typed := typed) (caller := caller) (snapshots := snapshots)
      (sourceFrame := sourceFrame) trace
  exact ⟨value, finalStore, finalMap, finalWorld, installed.invokes executed reason, rest⟩

include certificate parameters inputs extended acceptedPrefix definitions registered represented environments heaps initialLocals
  actualLayout canonicalReference actualReference unmapped typed caller snapshots acceptedHook extension
  contextValid unique uninitialized missing faithful functionLeaves functionTypes actualTyped sourceFrame in
theorem invoke_reflects [FunctionCalls.FaultTokens faults] {call : CallableCoercionSpine.Call} {callerEnvironment captured : Environment}
    {input : Dynamic.Value} {nativeInput : Value} {reason : Word}
    (sourceArgument : arguments = [input]) (nativeArgument : nativeArguments = [nativeInput])
    (entry : actual = nativeInput :: captured)
    (installed : Installed call code ξ callerEnvironment captured store)
    {value : Value} {finalStore : Store}
    (completed : CallableCoercionSpine.Invoke callerEnvironment reason call store (.inRight .word nativeInput) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      BodyOutcome program sourceBody function.evidence before [input] outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location current currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame finalMap finalStore records := by
  subst arguments nativeArguments actual
  exact reflects
      (prepared := prepared) (functions := functions) (extension := extension) (program := program)
      (onError := onError) (certificate := certificate) (parameters := parameters) (inputs := inputs)
      (extended := extended) (contextValid := contextValid) (unique := unique) (uninitialized := uninitialized)
      (missing := missing) (faithful := faithful) (functionLeaves := functionLeaves) (functionTypes := functionTypes)
      (acceptedPrefix := acceptedPrefix) (definitions := definitions) (registered := registered) (acceptedHook := acceptedHook)
      (represented := represented) (environments := environments) (heaps := heaps) (initialLocals := initialLocals)
      (actualLayout := actualLayout) (actualTyped := actualTyped) (canonicalReference := canonicalReference) (actualReference := actualReference)
      (unmapped := unmapped) (typed := typed) (caller := caller) (snapshots := snapshots)
      (sourceFrame := sourceFrame) (installed.completed completed)

end Solcore.SourceSemantics.CoreLowering.CallableCoercionMethodBody
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableCoercionMethodEntries
/-! A finite list retains actual method compilation, concrete body certificates
and independently selected source dictionaries. Runtime entries observe saved
closures and frame history only. No body execution law is a field. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableCoercionMethodEntries
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedParameterCertificates CallableIndexedParameterMeaning
open SourceCoreCallableIndexedFrames

abbrev ValuesContext := SourceCoreCompatibleValues.Context
abbrev Prepared := SourceCoreCallableIndexedPrograms.Prepared
abbrev BodyOutcome := CallableCoercionMethodFrame.BodyOutcome

def allocationError (error : SourceCoreAllocationLayouts.Error) : SourceCoreBasic.Error :=
  .sourceAllocation (reprStr error)

/-- Each row retains the actual compiler output and a concrete finite body
certificate. Source selection fixes one dictionary, without claiming its
uniqueness among all independently allowed source selections. Raw endpoint
and single-argument layout equations are independent static obligations. -/
structure Method {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (values : ValuesContext) (program : SourceSemantics.Program) (callerContext : SourceSemantics.Context)
    (callerEvidence : Dynamic.EvidenceEnvironment) where
  step : CoercionStep
  call : CallableCoercionSpine.Call
  named : SourceCoreGeneralFunctions.Function
  diagnostics : SourceCoreDataPlaceFaultSites.Program
  code : Expr
  compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code
  signature : named.signature = call.signature
  sourceBody : Dynamic.BodyInstance
  function : Dynamic.Closure
  selected : Dynamic.OperatorMethodSelected program callerContext callerEvidence "Coerce" "coerce"
    step.requirements sourceBody function.evidence
  frame : CallableCoercionMethodFrame.Frame sourceBody function
  source : function.source = CallableIndexedNamedGeneration.source named
  statements : function.body = compiled.statements
  input : TypedBinder
  bindings : named.inputs = [(input, call.signature.parameterType)]
  parameters : function.parameters = [input]
  inputs : function.source.inputs = [input]
  inputType : input.scheme.body = step.source
  result : function.resultType = step.target
  context : SourceSemantics.Context
  types : List TypeSystem.Ty
  extended : MonoBindersExtend function.source.owner function.context function.parameters types context
  valid : CompatibleExpressionLiterals.ContextValid named.specialized.function.solvedRequirements context function.evidence
  unique : NodeOccurrencesUnique function.source
  readFuel : Nat
  certificate : BuiltinNamedBody.Certificate prepared.layouts named.signature.key [] prepared.ancestry.layout.frame
    prepared.base.globals.length allocationError readFuel values function.source context named.specialized.function.solvedRequirements
    (diagnostics.reasonAt named.signature.key) (named.inputs.reverse.map fun binding => (binding.1.id, binding.2))
    function.body function.resultType named.signature.resultType
    (CompatibleNamedBody.bodyPolicy ((CallableIndexedNamedGeneration.representation prepared).atContext named.signature.key [])
      prepared.base.sourceProgram prepared.base.sourceProgram.signatures prepared.base.locals compiled.parents compiled.own.assignments
      diagnostics (CallableIndexedNamedGeneration.context prepared named) prepared.base.callableContext)
    prepared.fuel compiled.own.fellThroughReason compiled.own.table.escapedReason compiled.body

variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
  {values : ValuesContext} {program : SourceSemantics.Program} {callerContext : SourceSemantics.Context}
  {callerEvidence : Dynamic.EvidenceEnvironment}
abbrev Methods := List (Method prepared values program callerContext callerEvidence)

variable {programSource : SourceSemantics.Program}

/-- Each row is tied to the real compiler Step, including the complete selected
specialization and ordered dictionary. Renaming affects only the caller slot;
it never changes the dictionary or a saved capture. -/
inductive Emitted (program : CheckedProgram) (project : SourceCoreEvidence.Projector)
    (compilation : SourceCoreFunctions.Context) (caller : SourceSpecialization.SpecializedFunction)
    (available : SourceCompilationPlan.EvidenceEnvironment) (scope : SourceCoreBasic.Scope)
    (node : ExpressionNode) (policy : SourceCoreFunctions.CallablePolicy) (ξ : Renaming) :
    SourceCoreBasic.LoweredExpr → Methods (prepared := prepared) (values := values) (program := programSource)
      (callerContext := callerContext) (callerEvidence := callerEvidence) → SourceCoreBasic.LoweredExpr →
    List CallableCoercionSpine.Call → Prop where
  | nil {input} : Emitted program project compilation caller available scope node policy ξ input [] input []
  | cons {input middle output call calls method methods}
      (step : CallableCoercionSpine.Step program project compilation caller available scope node policy input method.step middle call)
      (slot : method.call = call.rename ξ)
      (completeRecord : method.named.specialized = step.specialized)
      (dictionary : method.function.evidence = CallableNamedMetadata.environment step.dictionary)
      (tail : Emitted program project compilation caller available scope node policy ξ middle methods output calls) :
      Emitted program project compilation caller available scope node policy ξ input (method :: methods) output (call :: calls)

variable {programSource : SourceSemantics.Program} {compilerProgram : CheckedProgram}
  {project : SourceCoreEvidence.Projector} {compilation : SourceCoreFunctions.Context}
  {callerFunction : SourceSpecialization.SpecializedFunction} {available : SourceCompilationPlan.EvidenceEnvironment}
  {scope : SourceCoreBasic.Scope} {node : ExpressionNode} {policy : SourceCoreFunctions.CallablePolicy} {ξ : Renaming}
  {input output : SourceCoreBasic.LoweredExpr}
  {profiles : Methods (prepared := prepared) (values := values) (program := programSource)
    (callerContext := callerContext) (callerEvidence := callerEvidence)} {calls : List CallableCoercionSpine.Call}

theorem Emitted.spine (emitted : Emitted compilerProgram project compilation callerFunction available scope node policy ξ input profiles output calls) :
    CallableCoercionSpine.Spine compilerProgram project compilation callerFunction available scope node policy input (profiles.map (·.step)) output calls := by
  induction emitted with
  | nil => exact .nil
  | cons step _ _ _ tail ih => exact .cons step ih

theorem Emitted.calls_eq (emitted : Emitted compilerProgram project compilation callerFunction available scope node policy ξ input profiles output calls) :
    profiles.map (·.call) = calls.map (CallableCoercionSpine.Call.rename ξ) := by
  induction emitted with
  | nil => rfl
  | cons step slot _ _ tail ih => simp only [List.map_cons, slot, ih]

/-- Actual capture values are never renamed; the saved body syntax and capture
lookup embedding are retained separately. -/
structure Capture (method : Method prepared values program callerContext callerEvidence)
    (definitions : DataEnvironment) (frameLocation : Location) (caller : Environment)
    (mapping : LocationMap) (world : StoreTyping) (heap : Dynamic.Heap) (store : Store) where
  administrative : Core.Context
  canonical : Environment
  captured : Environment
  capturedContext : Core.Context
  embedding : Renaming
  environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
    mapping world administrative [] [] canonical definitions
  locals : Dynamic.EnvironmentAgrees heap method.function.context.locals []
  layout : EnvironmentsAgree embedding canonical captured
  typed : RuntimeEnvironmentHasTypes world captured capturedContext definitions
  reference : canonical[prepared.base.globals.length]? = some (.cellRef prepared.ancestry.layout.frame.type frameLocation)
  capturedReference : captured[embedding prepared.base.globals.length]? = some (.cellRef prepared.ancestry.layout.frame.type frameLocation)
  installed : CallableCoercionMethodBody.Installed method.call method.compiled.output embedding.lift caller captured store
  unmapped : installed.location ∉ mapping

structure Entry (methods : Methods (prepared := prepared) (values := values) (program := program)
      (callerContext := callerContext) (callerEvidence := callerEvidence))
    (definitions : DataEnvironment) (caller : Environment)
    (mapping : LocationMap) (world : StoreTyping) (heap : Dynamic.Heap) (store : Store) where
  frameLocation : Location
  unmapped : frameLocation ∉ mapping
  typed : world[frameLocation]? = some prepared.ancestry.layout.frame.type
  current : NativeFrame
  ghost : GhostFrame
  frame : CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame
    frameLocation current ghost store
  records : List CallableIndexedSnapshots.Record
  snapshots : CallableIndexedSnapshots.All prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame mapping store records
  captures : ∀ method, method ∈ methods → Nonempty (Capture method definitions frameLocation caller mapping world heap store)

variable {methods : Methods (prepared := prepared) (values := values) (program := program)
    (callerContext := callerContext) (callerEvidence := callerEvidence)}
  {definitions : DataEnvironment} {caller : Environment}
  {mapping futureMap : LocationMap} {world futureWorld : StoreTyping} {heap after : Dynamic.Heap} {store futureStore : Store}

/-- Source heap effects preserve every protected global cell, including later
methods. The proof uses the original full stored closure and captures. -/
def Capture.extend {method : Method prepared values program callerContext callerEvidence} {location : Location}
    (capture : Capture method definitions location caller mapping world heap store)
    (maps : LocationMap.Extends mapping futureMap) (worlds : WorldExtends world futureWorld)
    (frame : AdministrativePreserved mapping store futureMap futureStore)
    (metadata : Dynamic.HeapMetadataExtend heap after) :
    Capture method definitions location caller futureMap futureWorld after futureStore := by
  have retained := frame capture.installed.location capture.unmapped (List.getElem?_eq_some_iff.mp capture.installed.read).1
  exact { capture with
    environments := capture.environments.extend maps worlds
    locals := capture.locals.mono metadata
    typed := capture.typed.weaken worlds
    installed := {capture.installed with read := retained.2.trans capture.installed.read}
    unmapped := retained.1 }

def Entry.extend (entry : Entry methods definitions caller mapping world heap store)
    (maps : LocationMap.Extends mapping futureMap) (worlds : WorldExtends world futureWorld)
    (frame : AdministrativePreserved mapping store futureMap futureStore)
    (metadata : Dynamic.HeapMetadataExtend heap after) :
    Entry methods definitions caller futureMap futureWorld after futureStore := by
  have retained := frame entry.frameLocation entry.unmapped (List.getElem?_eq_some_iff.mp entry.frame.read).1
  refine { entry with
    unmapped := retained.1
    typed := worlds.lookup entry.typed
    frame := ⟨retained.2.trans entry.frame.read, entry.frame.history⟩
    snapshots := entry.snapshots.transport frame
    captures := ?_ }
  intro method member
  obtain ⟨capture⟩ := entry.captures method member
  exact ⟨capture.extend maps worlds frame metadata⟩

def Entry.restrict {subset : Methods (prepared := prepared) (values := values) (program := program)
      (callerContext := callerContext) (callerEvidence := callerEvidence)}
    (entry : Entry methods definitions caller mapping world heap store)
    (included : ∀ method ∈ subset, method ∈ methods) :
    Entry subset definitions caller mapping world heap store :=
  {entry with captures := fun method member => entry.captures method (included method member)}

end Solcore.SourceSemantics.CoreLowering.CallableCoercionMethodEntries
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableCoercionPathMeaning
/-! Ordered coercion paths reuse the concrete method body theorem. The forward
trace records the actual selected dictionaries; it is a restricted annotation
of independent source body derivations. Reflection constructs ordinary source
path judgments. Neither direction assumes a universal method-body meaning. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableCoercionPathMeaning
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedParameterCertificates CallableIndexedParameterMeaning
open SourceCoreCallableIndexedFrames CallableCoercionMethodEntries

variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
  {values : ValuesContext} {program : SourceSemantics.Program} {context : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment}
abbrev MethodProfile := Method prepared values program context evidence
abbrev Profiles := List (MethodProfile (prepared := prepared) (values := values) (program := program) (context := context) (evidence := evidence))

/-- Raw source endpoints and native slots compose separately. Projection alone
cannot identify the source types. These are static layout equations. -/
inductive Chain : TypeSystem.Ty → Ty → Profiles (prepared := prepared) (values := values) (program := program) (context := context) (evidence := evidence) → TypeSystem.Ty → Ty → Prop where
  | nil (source : TypeSystem.Ty) (native : Ty) : Chain source native [] source native
  | cons {method : MethodProfile (prepared := prepared) (values := values) (program := program) (context := context) (evidence := evidence)}
      {methods : Profiles (prepared := prepared) (values := values) (program := program) (context := context) (evidence := evidence)} {target : TypeSystem.Ty} {native : Ty}
      (tail : Chain method.step.target method.call.signature.resultType methods target native) :
      Chain method.step.source method.call.signature.parameterType (method :: methods) target native

/-- The annotation retains independent BodyInvokes/BodyFaults at the specific
selected body and dictionary. Its erasure is the existing source path judgment;
there is no evidence-uniqueness claim for arbitrary source derivations. -/
inductive SelectedTrace : Profiles (prepared := prepared) (values := values) (program := program) (context := context) (evidence := evidence) →
    Dynamic.Heap → Dynamic.Value → Dynamic.ExpressionOutcome → Dynamic.Heap → Prop where
  | nil {heap input} : SelectedTrace [] heap input (.value input) heap
  | cons {method methods before middle after input value outcome}
      (body : Dynamic.BodyInvokes program method.sourceBody method.function.evidence before [input] value middle)
      (tail : SelectedTrace methods middle value outcome after) :
      SelectedTrace (method :: methods) before input outcome after
  | fault {method methods before after input reason}
      (body : Dynamic.BodyFaults program method.sourceBody method.function.evidence before [input] reason after) :
      SelectedTrace (method :: methods) before input (.fault reason) after

def PathOutcome (methods : Profiles (prepared := prepared) (values := values) (program := program) (context := context) (evidence := evidence))
    (before : Dynamic.Heap) (input : Dynamic.Value) (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap) : Prop :=
  match outcome with
  | .value result => Dynamic.CoercionPathExecutes program context evidence before (methods.map (·.step)) input result after
  | .fault reason => Dynamic.CoercionPathFaults program context evidence before (methods.map (·.step)) input reason after

theorem SelectedTrace.sound {methods : Profiles (prepared := prepared) (values := values) (program := program) (context := context) (evidence := evidence)}
    {before after : Dynamic.Heap} {input : Dynamic.Value} {outcome : Dynamic.ExpressionOutcome}
    (trace : SelectedTrace methods before input outcome after) : PathOutcome methods before input outcome after := by
  induction trace with
  | nil => exact .nil
  | @cons method methods before middle after input value outcome invoked tail ih =>
    cases outcome with
    | value result => exact .cons (.method method.selected invoked) ih
    | fault reason => exact .tail (.method method.selected invoked) ih
  | @fault method methods before after input reason failed => exact .head (.method method.selected failed)

variable {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (definitions : prepared.layouts.definitions = ambient.definitions)
  (registered : prepared.ancestry.layout.frame.Registered ambient.definitions)
  {faults : FunctionCalls.FaultRep} {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  {methods : Profiles (prepared := prepared) (values := values) (program := program) (context := context) (evidence := evidence)}
  (uninitialized : ∀ method ∈ methods, ∀ id location, faults (.uninitializedLocation location) (method.diagnostics.reasonAt method.named.signature.key id))
  (missing : ∀ method ∈ methods, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((method.diagnostics.reasonAt method.named.signature.key id).add tag))

private theorem arguments {method : MethodProfile (prepared := prepared) (values := values) (program := program) (context := context) (evidence := evidence)}
    {mapping : LocationMap} {world : StoreTyping} {input : Dynamic.Value} {native : Value}
    (represented : ValueRep values.checked registry functions mapping world method.step.source input native method.call.signature.parameterType) :
    Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions) mapping world method.named.inputs [input] [native] := by
  rw [method.bindings]
  apply Arguments.cons _ Arguments.nil
  change ValueRep _ _ _ _ _ method.input.scheme.body _ _ _
  simpa only [method.inputType] using represented

include extension definitions registered faithful observations runtimeViews uninitialized missing in
/-- One reached call consumes only concrete body semantics. All future captures
are transported from actual administrative preservation. -/
theorem method_preserves [FunctionCalls.FaultTokens faults] {method : MethodProfile (prepared := prepared) (values := values) (program := program) (context := context) (evidence := evidence)}
    (member : method ∈ methods) {caller : Environment} {mapping : LocationMap} {world : StoreTyping}
    {before after : Dynamic.Heap} {store : Store} {input : Dynamic.Value} {native : Value}
    (entry : Entry methods ambient.definitions caller mapping world before store)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (represented : ValueRep values.checked registry functions mapping world method.step.source input native method.call.signature.parameterType)
    {outcome : Dynamic.ExpressionOutcome} (trace : BodyOutcome program method.sourceBody method.function.evidence before [input] outcome after)
    (reason : Word) :
    ∃ value finalStore finalMap finalWorld,
      CallableCoercionSpine.Invoke caller reason method.call store (.inRight .word native) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        method.step.target method.call.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry methods ambient.definitions caller finalMap finalWorld after finalStore) := by
  obtain ⟨capture⟩ := entry.captures method member
  have parameterEq : method.function.parameters = method.named.inputs.map Prod.fst := by simp only [method.parameters, method.bindings, List.map_cons, List.map_nil]
  have inputEq : method.function.source.inputs = method.named.inputs.map Prod.fst := by simp only [method.inputs, method.bindings, List.map_cons, List.map_nil]
  have parametersCompiled := method.compiled.parametersCompiled
  rw [← method.source] at parametersCompiled
  have reference : (native :: capture.captured)[capture.embedding.lift (prepared.base.globals.length + 1)]? =
      some (.cellRef prepared.ancestry.layout.frame.type entry.frameLocation) := by
    simpa only [Renaming.lift, Nat.succ_sub_one, List.getElem?_cons_succ] using capture.capturedReference
  obtain ⟨value, finalStore, finalMap, finalWorld, invoked, related, finalHeaps, maps, worlds, frame, metadata, _, _⟩ :=
    CallableCoercionMethodBody.invoke_preserves (prepared := prepared.ancestry) (functions := functions)
      (extension := extension) (program := program) (onError := allocationError) (certificate := method.certificate)
      (parameters := parameterEq) (inputs := inputEq) (extended := method.extended) (contextValid := method.valid)
      (unique := method.unique) (uninitialized := uninitialized method member) (missing := missing method member)
      (faithful := faithful) (functionLeaves := observations) (functionTypes := runtimeViews)
      (acceptedPrefix := parametersCompiled) (definitions := definitions) (registered := registered)
      (acceptedHook := method.compiled.hook) (represented := arguments functions represented)
      (environments := capture.environments) (heaps := heaps) (initialLocals := capture.locals)
      (actualLayout := by
        intro index value found
        exact Core.ReadOnly.EnvironmentsAgree.lift capture.layout native found)
      (actualTyped := .cons represented.runtime_hasType capture.typed)
      (canonicalReference := capture.reference) (actualReference := reference) (unmapped := entry.unmapped)
      (typed := entry.typed) (caller := entry.frame) (snapshots := entry.snapshots) (sourceFrame := method.frame)
      rfl rfl rfl capture.installed trace
  exact ⟨value, finalStore, finalMap, finalWorld, invoked, by simpa only [method.result, method.signature] using related,
    finalHeaps, maps, worlds, frame, metadata, ⟨entry.extend maps worlds frame metadata⟩⟩

include extension definitions registered faithful observations runtimeViews uninitialized missing in
theorem method_reflects [FunctionCalls.FaultTokens faults] {method : MethodProfile (prepared := prepared) (values := values) (program := program) (context := context) (evidence := evidence)}
    (member : method ∈ methods) {caller : Environment} {mapping : LocationMap} {world : StoreTyping}
    {before : Dynamic.Heap} {store finalStore : Store} {input : Dynamic.Value} {native value : Value} {reason : Word}
    (entry : Entry methods ambient.definitions caller mapping world before store)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (represented : ValueRep values.checked registry functions mapping world method.step.source input native method.call.signature.parameterType)
    (completed : CallableCoercionSpine.Invoke caller reason method.call store (.inRight .word native) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      BodyOutcome program method.sourceBody method.function.evidence before [input] outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        method.step.target method.call.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry methods ambient.definitions caller finalMap finalWorld after finalStore) := by
  obtain ⟨capture⟩ := entry.captures method member
  have parameterEq : method.function.parameters = method.named.inputs.map Prod.fst := by simp only [method.parameters, method.bindings, List.map_cons, List.map_nil]
  have inputEq : method.function.source.inputs = method.named.inputs.map Prod.fst := by simp only [method.inputs, method.bindings, List.map_cons, List.map_nil]
  have parametersCompiled := method.compiled.parametersCompiled
  rw [← method.source] at parametersCompiled
  have reference : (native :: capture.captured)[capture.embedding.lift (prepared.base.globals.length + 1)]? =
      some (.cellRef prepared.ancestry.layout.frame.type entry.frameLocation) := by
    simpa only [Renaming.lift, Nat.succ_sub_one, List.getElem?_cons_succ] using capture.capturedReference
  obtain ⟨outcome, after, finalMap, finalWorld, trace, related, finalHeaps, maps, worlds, frame, metadata, _, _⟩ :=
    CallableCoercionMethodBody.invoke_reflects (prepared := prepared.ancestry) (functions := functions)
      (extension := extension) (program := program) (onError := allocationError) (certificate := method.certificate)
      (parameters := parameterEq) (inputs := inputEq) (extended := method.extended) (contextValid := method.valid)
      (unique := method.unique) (uninitialized := uninitialized method member) (missing := missing method member)
      (faithful := faithful) (functionLeaves := observations) (functionTypes := runtimeViews)
      (acceptedPrefix := parametersCompiled) (definitions := definitions) (registered := registered)
      (acceptedHook := method.compiled.hook) (represented := arguments functions represented)
      (environments := capture.environments) (heaps := heaps) (initialLocals := capture.locals)
      (actualLayout := by
        intro index value found
        exact Core.ReadOnly.EnvironmentsAgree.lift capture.layout native found)
      (actualTyped := .cons represented.runtime_hasType capture.typed)
      (canonicalReference := capture.reference) (actualReference := reference) (unmapped := entry.unmapped)
      (typed := entry.typed) (caller := entry.frame) (snapshots := entry.snapshots) (sourceFrame := method.frame)
      rfl rfl rfl capture.installed completed
  exact ⟨outcome, after, finalMap, finalWorld, trace, by simpa only [method.result, method.signature] using related,
    finalHeaps, maps, worlds, frame, metadata, ⟨entry.extend maps worlds frame metadata⟩⟩

theorem Chain.final_type {source target : TypeSystem.Ty} {input output : Ty}
    (chain : Chain source input methods target output) :
    CallableCoercionSpine.finalType input (methods.map (·.call)) = output := by
  induction chain with
  | nil => rfl
  | cons tail ih => exact ih

/-- Failure inversion follows the actual ordered native calls, so every
unreached method keeps both the payload and the exact failure store. -/
theorem failed_runs {caller : Environment} {reason : Word} {store finalStore : Store}
    {tag : Ty} {payload value : Value} {calls : List CallableCoercionSpine.Call}
    (runs : CallableCoercionSpine.Runs caller reason store (.inLeft tag payload) calls value finalStore) :
    value = .inLeft (CallableCoercionSpine.finalType tag calls) payload ∧ finalStore = store := by
  generalize inputEq : Value.inLeft tag payload = input at runs
  induction runs generalizing tag with
  | nil => cases inputEq; exact ⟨rfl, rfl⟩
  | cons head tail ih =>
    cases inputEq
    cases head with
    | skipped => exact ih rfl

section Common

/-- The source and native endpoints of one actual ordered method row. Concrete
body receipts and saved entries stay in the caller's row type. -/
structure Row where
  step : CoercionStep
  call : CallableCoercionSpine.Call
  body : Dynamic.BodyInstance
  dictionary : Dynamic.EvidenceEnvironment

inductive ChainFor {α : Type} (row : α → Row) :
    TypeSystem.Ty → Ty → List α → TypeSystem.Ty → Ty → Prop where
  | nil (source : TypeSystem.Ty) (native : Ty) : ChainFor row source native [] source native
  | cons {method : α} {methods : List α} {target : TypeSystem.Ty} {native : Ty}
      (tail : ChainFor row (row method).step.target (row method).call.signature.resultType methods target native) :
      ChainFor row (row method).step.source (row method).call.signature.parameterType (method :: methods) target native

inductive SelectedTraceFor {α : Type} (row : α → Row) (program : Program) :
    List α → Dynamic.Heap → Dynamic.Value → Dynamic.ExpressionOutcome → Dynamic.Heap → Prop where
  | nil {heap input} : SelectedTraceFor row program [] heap input (.value input) heap
  | cons {method methods before middle after input value outcome}
      (body : Dynamic.BodyInvokes program (row method).body (row method).dictionary before [input] value middle)
      (tail : SelectedTraceFor row program methods middle value outcome after) :
      SelectedTraceFor row program (method :: methods) before input outcome after
  | fault {method methods before after input reason}
      (body : Dynamic.BodyFaults program (row method).body (row method).dictionary before [input] reason after) :
      SelectedTraceFor row program (method :: methods) before input (.fault reason) after

variable {α : Type} {row : α → Row}

theorem ChainFor.final_type {source target : TypeSystem.Ty} {input output : Ty} {methods : List α}
    (chain : ChainFor row source input methods target output) :
    CallableCoercionSpine.finalType input (methods.map (fun method => (row method).call)) = output := by
  induction chain with
  | nil => rfl
  | cons tail ih => exact ih

variable {State : LocationMap → StoreTyping → Dynamic.Heap → Store → Type}
  {caller : Environment} {reason : Word}

/-- Internal one-step continuation for the shared ordered proof. A public
concrete consumer supplies it from its actual static body certificate. -/
def StepPreservesFor (row : α → Row)
    (State : LocationMap → StoreTyping → Dynamic.Heap → Store → Type)
    (functions : FunctionModel values.checked.catalog ambient)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (program : Program) (caller : Environment) (reason : Word) (methods : List α) : Prop :=
  ∀ {method mapping world before after store input native outcome}, method ∈ methods →
    State mapping world before store →
    CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store →
    ValueRep values.checked registry functions mapping world (row method).step.source input native
      (row method).call.signature.parameterType →
    BodyOutcome program (row method).body (row method).dictionary before [input] outcome after →
    ∃ result finalStore finalMap finalWorld,
      CallableCoercionSpine.Invoke caller reason (row method).call store (.inRight .word native) result finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        (row method).step.target (row method).call.signature.resultType faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (State finalMap finalWorld after finalStore)

/-- Relate actual states at their original heap/store indices. -/
def StateRelation (State : LocationMap → StoreTyping → Dynamic.Heap → Store → Type) :=
  ∀ {mapping nextMap : LocationMap} {world nextWorld : StoreTyping}
    {before after : Dynamic.Heap} {store finalStore : Store},
    State mapping world before store → State nextMap nextWorld after finalStore → Prop

variable (relation : StateRelation State)

/-- The actual empty path retains exactly its input state. -/
def StateReflexive : Prop :=
  ∀ {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    (entry : State mapping world heap store), relation entry entry

/-- Actual successive method states compose through their common reached state. -/
def StateTransitive : Prop :=
  ∀ {mapping middleMap finalMap : LocationMap} {world middleWorld finalWorld : StoreTyping}
    {before middle after : Dynamic.Heap} {store middleStore finalStore : Store}
    {entry : State mapping world before store} {reached : State middleMap middleWorld middle middleStore}
    {returned : State finalMap finalWorld after finalStore},
    relation entry reached → relation reached returned → relation entry returned

def StepPreservesForWithState (row : α → Row)
    (State : LocationMap → StoreTyping → Dynamic.Heap → Store → Type)
    (relation : StateRelation State)
    (functions : FunctionModel values.checked.catalog ambient)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (program : Program) (caller : Environment) (reason : Word) (methods : List α) : Prop :=
  ∀ {method mapping world before after store input native outcome}, method ∈ methods →
    ∀ entry : State mapping world before store,
    CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store →
    ValueRep values.checked registry functions mapping world (row method).step.source input native
      (row method).call.signature.parameterType →
    BodyOutcome program (row method).body (row method).dictionary before [input] outcome after →
    ∃ result finalStore finalMap finalWorld,
      CallableCoercionSpine.Invoke caller reason (row method).call store (.inRight .word native) result finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        (row method).step.target (row method).call.signature.resultType faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ returned : State finalMap finalWorld after finalStore, relation entry returned

theorem preserves_for_with_state
    (reflexive : StateReflexive (State := State) @relation) (transitive : StateTransitive (State := State) @relation)
    {source target : TypeSystem.Ty} {inputType outputType : Ty} {methods : List α}
    (step : StepPreservesForWithState row State relation functions registry faults program caller reason methods)
    (chain : ChainFor row source inputType methods target outputType)
    {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap} {store : Store}
    {input : Dynamic.Value} {native : Value} {outcome : Dynamic.ExpressionOutcome}
    (entry : State mapping world before store)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (represented : ValueRep values.checked registry functions mapping world source input native inputType)
    (trace : SelectedTraceFor row program methods before input outcome after) :
    ∃ value finalStore finalMap finalWorld,
      CallableCoercionSpine.Runs caller reason store (.inRight .word native) (methods.map (fun method => (row method).call)) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        target outputType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ returned : State finalMap finalWorld after finalStore, relation entry returned := by
  induction chain generalizing mapping world before after store input native outcome with
  | nil source type =>
    cases trace
    exact ⟨_, _, _, _, .nil, .value represented, heaps, .refl _, .refl _, .refl _ _, .refl _, ⟨entry, reflexive entry⟩⟩
  | @cons method rest target output chain ih =>
    cases trace with
    | @cons _ _ _ middle _ _ value _ body tail =>
      obtain ⟨result, middleStore, middleMap, middleWorld, invoked, related, middleHeaps, maps, worlds, frame, metadata, nextEntry, headRelated⟩ :=
        step (List.mem_cons_self) entry heaps represented (.value body)
      cases related with
      | value middleRepresented =>
        obtain ⟨result, finalStore, finalMap, finalWorld, runs, related, finalHeaps, tailMaps, tailWorlds, tailFrame, tailMetadata, finalEntry, tailRelated⟩ :=
          ih (fun member => step (List.mem_cons_of_mem _ member)) nextEntry middleHeaps middleRepresented tail
        exact ⟨_, _, _, _, .cons invoked runs, related, finalHeaps, maps.trans tailMaps, worlds.trans tailWorlds,
          frame.trans tailFrame, metadata.trans tailMetadata,
          finalEntry, transitive headRelated tailRelated⟩
    | fault body =>
      obtain ⟨result, finalStore, finalMap, finalWorld, invoked, related, finalHeaps, maps, worlds, frame, metadata, finalEntry⟩ :=
        step (List.mem_cons_self) entry heaps represented (.fault body)
      cases related with
      | fault faultRep =>
        refine ⟨_, _, _, _, .cons invoked (CallableCoercionSpine.Runs.failure caller reason finalStore _ _ _),
          ?_, finalHeaps, maps, worlds, frame, metadata, finalEntry⟩
        rw [chain.final_type]
        exact .fault faultRep

def StepReflectsFor (row : α → Row)
    (State : LocationMap → StoreTyping → Dynamic.Heap → Store → Type)
    (functions : FunctionModel values.checked.catalog ambient)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (program : Program)
    (invocation : CallableCoercionSpine.Call → Store → Value → Value → Store → Prop) (methods : List α) : Prop :=
  ∀ {method mapping world before store finalStore input native value}, method ∈ methods →
    State mapping world before store →
    CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store →
    ValueRep values.checked registry functions mapping world (row method).step.source input native
      (row method).call.signature.parameterType →
    invocation (row method).call store (.inRight .word native) value finalStore →
    ∃ outcome after finalMap finalWorld,
      BodyOutcome program (row method).body (row method).dictionary before [input] outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        (row method).step.target (row method).call.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (State finalMap finalWorld after finalStore)

def StepReflectsForWithState (row : α → Row)
    (State : LocationMap → StoreTyping → Dynamic.Heap → Store → Type)
    (relation : StateRelation State)
    (functions : FunctionModel values.checked.catalog ambient)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (program : Program)
    (invocation : CallableCoercionSpine.Call → Store → Value → Value → Store → Prop) (methods : List α) : Prop :=
  ∀ {method mapping world before store finalStore input native value}, method ∈ methods →
    ∀ entry : State mapping world before store,
    CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store →
    ValueRep values.checked registry functions mapping world (row method).step.source input native
      (row method).call.signature.parameterType →
    invocation (row method).call store (.inRight .word native) value finalStore →
    ∃ outcome after finalMap finalWorld,
      BodyOutcome program (row method).body (row method).dictionary before [input] outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        (row method).step.target (row method).call.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ returned : State finalMap finalWorld after finalStore, relation entry returned

theorem reflects_for_with_state
    {invocation : CallableCoercionSpine.Call → Store → Value → Value → Store → Prop}
    (forget : ∀ {call before input result after}, invocation call before input result after →
      CallableCoercionSpine.Invoke caller reason call before input result after)
    (reflexive : StateReflexive (State := State) @relation) (transitive : StateTransitive (State := State) @relation)
    {source target : TypeSystem.Ty} {inputType outputType : Ty} {methods : List α}
    (step : StepReflectsForWithState row State relation functions registry faults program invocation methods)
    (chain : ChainFor row source inputType methods target outputType)
    {mapping : LocationMap} {world : StoreTyping}
    {before : Dynamic.Heap} {store finalStore : Store} {input : Dynamic.Value} {native value : Value}
    (entry : State mapping world before store)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (represented : ValueRep values.checked registry functions mapping world source input native inputType)
    (runs : CallableCoercionSpine.RunsFor invocation store (.inRight .word native) (methods.map (fun method => (row method).call)) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      SelectedTraceFor row program methods before input outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        target outputType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ returned : State finalMap finalWorld after finalStore, relation entry returned := by
  induction chain generalizing mapping world before store input native value finalStore with
  | nil source type =>
    cases runs
    exact ⟨_, _, _, _, .nil, .value represented, heaps, .refl _, .refl _, .refl _ _, .refl _, ⟨entry, reflexive entry⟩⟩
  | @cons method rest target output chain ih =>
    cases runs with
    | cons invoked tail =>
      obtain ⟨outcome, middle, middleMap, middleWorld, body, related, middleHeaps, maps, worlds, frame, metadata, nextEntry, headRelated⟩ :=
        step (List.mem_cons_self) entry heaps represented invoked
      cases related with
      | value middleRepresented =>
        obtain ⟨outcome, after, finalMap, finalWorld, traced, related, finalHeaps, tailMaps, tailWorlds, tailFrame, tailMetadata, finalEntry, tailRelated⟩ :=
          ih (fun member => step (List.mem_cons_of_mem _ member)) nextEntry middleHeaps middleRepresented tail
        have invoked := by cases body with | value body => exact body
        exact ⟨_, _, _, _, .cons invoked traced, related, finalHeaps, maps.trans tailMaps, worlds.trans tailWorlds,
          frame.trans tailFrame, metadata.trans tailMetadata,
          finalEntry, transitive headRelated tailRelated⟩
      | fault faultRep =>
        obtain ⟨rfl, rfl⟩ := failed_runs (tail.map forget).toRuns
        have failed := by cases body with | fault body => exact body
        refine ⟨_, _, _, _, .fault failed, ?_, middleHeaps, maps, worlds, frame, metadata, nextEntry, headRelated⟩
        rw [chain.final_type]
        exact .fault faultRep

theorem preserves_for
    (extendState : ∀ {mapping nextMap world nextWorld before after store finalStore},
      State mapping world before store → LocationMap.Extends mapping nextMap → WorldExtends world nextWorld →
      AdministrativePreserved mapping store nextMap finalStore → Dynamic.HeapMetadataExtend before after →
      State nextMap nextWorld after finalStore)
    {source target : TypeSystem.Ty} {inputType outputType : Ty} {methods : List α}
    (step : StepPreservesFor row State functions registry faults program caller reason methods)
    (chain : ChainFor row source inputType methods target outputType)
    {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap} {store : Store}
    {input : Dynamic.Value} {native : Value} {outcome : Dynamic.ExpressionOutcome}
    (entry : State mapping world before store)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (represented : ValueRep values.checked registry functions mapping world source input native inputType)
    (trace : SelectedTraceFor row program methods before input outcome after) :
    ∃ value finalStore finalMap finalWorld,
      CallableCoercionSpine.Runs caller reason store (.inRight .word native) (methods.map (fun method => (row method).call)) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        target outputType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (State finalMap finalWorld after finalStore) := by
  let _legacyTransport := @extendState
  obtain ⟨value, finalStore, finalMap, finalWorld, runs, related, finalHeaps,
    maps, worlds, frame, metadata, returned, _⟩ :=
    preserves_for_with_state (functions := functions) (State := State) (relation := fun _ _ => True) (fun _ => True.intro) (fun _ _ => True.intro)
      (by
        intro method mapping world before after store input native outcome member initial heaps represented trace
        obtain ⟨value, finalStore, finalMap, finalWorld, invoked, related, finalHeaps,
          maps, worlds, frame, metadata, ⟨returned⟩⟩ := step member initial heaps represented trace
        exact ⟨value, finalStore, finalMap, finalWorld, invoked, related, finalHeaps,
          maps, worlds, frame, metadata, returned, True.intro⟩)
      chain entry heaps represented trace
  exact ⟨value, finalStore, finalMap, finalWorld, runs, related, finalHeaps, maps, worlds, frame, metadata, ⟨returned⟩⟩

theorem reflects_for
    {invocation : CallableCoercionSpine.Call → Store → Value → Value → Store → Prop}
    (forget : ∀ {call before input result after}, invocation call before input result after →
      CallableCoercionSpine.Invoke caller reason call before input result after)
    (extendState : ∀ {mapping nextMap world nextWorld before after store finalStore},
      State mapping world before store → LocationMap.Extends mapping nextMap → WorldExtends world nextWorld →
      AdministrativePreserved mapping store nextMap finalStore → Dynamic.HeapMetadataExtend before after →
      State nextMap nextWorld after finalStore)
    {source target : TypeSystem.Ty} {inputType outputType : Ty} {methods : List α}
    (step : StepReflectsFor row State functions registry faults program invocation methods)
    (chain : ChainFor row source inputType methods target outputType)
    {mapping : LocationMap} {world : StoreTyping}
    {before : Dynamic.Heap} {store finalStore : Store} {input : Dynamic.Value} {native value : Value}
    (entry : State mapping world before store)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (represented : ValueRep values.checked registry functions mapping world source input native inputType)
    (runs : CallableCoercionSpine.RunsFor invocation store (.inRight .word native) (methods.map (fun method => (row method).call)) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      SelectedTraceFor row program methods before input outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        target outputType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (State finalMap finalWorld after finalStore) := by
  let _legacyTransport := @extendState
  obtain ⟨outcome, after, finalMap, finalWorld, traced, related, finalHeaps,
    maps, worlds, frame, metadata, returned, _⟩ :=
    reflects_for_with_state (functions := functions) (State := State) (relation := fun _ _ => True) forget (fun _ => True.intro) (fun _ _ => True.intro)
      (by
        intro method mapping world before store finalStore input native value member initial heaps represented invoked
        obtain ⟨outcome, after, finalMap, finalWorld, body, related, finalHeaps,
          maps, worlds, frame, metadata, ⟨returned⟩⟩ := step member initial heaps represented invoked
        exact ⟨outcome, after, finalMap, finalWorld, body, related, finalHeaps,
          maps, worlds, frame, metadata, returned, True.intro⟩)
      chain entry heaps represented runs
  exact ⟨outcome, after, finalMap, finalWorld, traced, related, finalHeaps, maps, worlds, frame, metadata, ⟨returned⟩⟩


end Common


/-- The legacy receipt keeps exactly the same selected row in the common path. -/
def MethodProfile.row (method : MethodProfile (prepared := prepared) (values := values)
    (program := program) (context := context) (evidence := evidence)) : Row :=
  ⟨method.step, method.call, method.sourceBody, method.function.evidence⟩

theorem Chain.toFor {source target : TypeSystem.Ty} {input output : Ty}
    (chain : Chain source input methods target output) :
    ChainFor MethodProfile.row source input methods target output := by
  induction chain with
  | nil => exact .nil _ _
  | cons tail ih => exact .cons ih

theorem SelectedTrace.toFor {before after : Dynamic.Heap} {input : Dynamic.Value}
    {outcome : Dynamic.ExpressionOutcome} (trace : SelectedTrace methods before input outcome after) :
    SelectedTraceFor MethodProfile.row program methods before input outcome after := by
  induction trace with
  | nil => exact .nil
  | cons body tail ih => exact .cons body ih
  | fault body => exact .fault body

theorem SelectedTrace.ofFor {before after : Dynamic.Heap} {input : Dynamic.Value}
    {outcome : Dynamic.ExpressionOutcome}
    (trace : SelectedTraceFor MethodProfile.row program methods before input outcome after) :
    SelectedTrace methods before input outcome after := by
  induction trace with
  | nil => exact .nil
  | cons body tail ih => exact .cons body ih
  | fault body => exact .fault body

include extension definitions registered faithful observations runtimeViews in
/-- Forward preservation uses independent body traces at the actual selected
method dictionaries. Arbitrary source dictionaries need a separate coherence
or evidence-independence theorem. -/
theorem preserves [FunctionCalls.FaultTokens faults] (uninitialized : ∀ method ∈ methods, ∀ id location,
      faults (.uninitializedLocation location) (method.diagnostics.reasonAt method.named.signature.key id))
    (missing : ∀ method ∈ methods, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
      faults (.missingMappingDefault value) ((method.diagnostics.reasonAt method.named.signature.key id).add tag))
    {source target : TypeSystem.Ty} {inputType outputType : Ty}
    (chain : Chain source inputType methods target outputType)
    {caller : Environment} {mapping : LocationMap} {world : StoreTyping}
    {before after : Dynamic.Heap} {store : Store} {input : Dynamic.Value} {native : Value}
    (entry : Entry methods ambient.definitions caller mapping world before store)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (represented : ValueRep values.checked registry functions mapping world source input native inputType)
    {outcome : Dynamic.ExpressionOutcome} (trace : SelectedTrace methods before input outcome after)
    (reason : Word) :
    ∃ value finalStore finalMap finalWorld,
      CallableCoercionSpine.Runs caller reason store (.inRight .word native) (methods.map (·.call)) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        target outputType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry methods ambient.definitions caller finalMap finalWorld after finalStore) := by
  exact preserves_for (functions := functions)
    (State := Entry methods ambient.definitions caller)
    (fun entry maps worlds frame metadata => entry.extend maps worlds frame metadata)
    (fun member entry heaps represented trace =>
      method_preserves functions extension definitions registered faithful observations runtimeViews
        uninitialized missing member entry heaps represented trace reason)
    chain.toFor entry heaps represented trace.toFor

include extension definitions registered faithful observations runtimeViews in
/-- Every completed native path reconstructs an independent source path with
its actual selected dictionaries. It needs no source completion premise. -/
theorem reflects [FunctionCalls.FaultTokens faults] (uninitialized : ∀ method ∈ methods, ∀ id location,
      faults (.uninitializedLocation location) (method.diagnostics.reasonAt method.named.signature.key id))
    (missing : ∀ method ∈ methods, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
      faults (.missingMappingDefault value) ((method.diagnostics.reasonAt method.named.signature.key id).add tag))
    {source target : TypeSystem.Ty} {inputType outputType : Ty}
    (chain : Chain source inputType methods target outputType)
    {caller : Environment} {mapping : LocationMap} {world : StoreTyping}
    {before : Dynamic.Heap} {store finalStore : Store} {input : Dynamic.Value} {native value : Value} {reason : Word}
    (entry : Entry methods ambient.definitions caller mapping world before store)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (represented : ValueRep values.checked registry functions mapping world source input native inputType)
    (runs : CallableCoercionSpine.Runs caller reason store (.inRight .word native) (methods.map (·.call)) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      SelectedTrace methods before input outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        target outputType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry methods ambient.definitions caller finalMap finalWorld after finalStore) := by
  obtain ⟨outcome, after, finalMap, finalWorld, trace, related, heaps, maps, worlds, frame, metadata, next⟩ :=
    reflects_for (functions := functions) (State := Entry methods ambient.definitions caller)
      (fun invoked => invoked)
      (fun entry maps worlds frame metadata => entry.extend maps worlds frame metadata)
      (fun member entry heaps represented completed =>
        method_reflects functions extension definitions registered faithful observations runtimeViews
          uninitialized missing member entry heaps represented completed)
      chain.toFor entry heaps represented runs.toFor
  exact ⟨outcome, after, finalMap, finalWorld, SelectedTrace.ofFor trace, related, heaps, maps, worlds, frame, metadata, next⟩

variable {compilerProgram : CheckedProgram} {project : SourceCoreEvidence.Projector}
  {compilation : SourceCoreFunctions.Context} {callerFunction : SourceSpecialization.SpecializedFunction}
  {available : SourceCompilationPlan.EvidenceEnvironment} {scope : SourceCoreBasic.Scope}
  {node : ExpressionNode} {policy : SourceCoreFunctions.CallablePolicy} {ξ : Renaming}
  {inputCode outputCode : SourceCoreBasic.LoweredExpr} {calls : List CallableCoercionSpine.Call}

include extension definitions registered faithful observations runtimeViews uninitialized missing in
/-- The actual emitted expression, after a successful operand, preserves the
annotated source path. The operand is outside this path-only theorem. -/
theorem emitted_preserves [FunctionCalls.FaultTokens faults]
    (emitted : Emitted compilerProgram project compilation callerFunction available scope node policy ξ inputCode methods outputCode calls)
    {source target : TypeSystem.Ty} (chain : Chain source inputCode.type methods target outputCode.type)
    {caller : Environment} {mapping : LocationMap} {world : StoreTyping}
    {before after : Dynamic.Heap} {initialStore store : Store} {input : Dynamic.Value} {native : Value}
    (entry : Entry methods ambient.definitions caller mapping world before store)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (represented : ValueRep values.checked registry functions mapping world source input native inputCode.type)
    (operand : Evaluates caller initialStore (inputCode.expression.rename ξ) (.inRight .word native) store)
    {outcome : Dynamic.ExpressionOutcome} (trace : SelectedTrace methods before input outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates caller initialStore (outputCode.expression.rename ξ) value finalStore ∧
      PathOutcome methods before input outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        target outputCode.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry methods ambient.definitions caller finalMap finalWorld after finalStore) := by
  obtain ⟨value, finalStore, finalMap, finalWorld, runs, related, finalHeaps, maps, worlds, frame, metadata, finalEntry⟩ :=
    preserves functions extension definitions registered faithful observations runtimeViews uninitialized missing chain entry heaps represented trace compilation.internalReason
  refine ⟨_, _, _, _, (emitted.spine.renamed_completed_iff ξ).mpr ?_, trace.sound, related,
    finalHeaps, maps, worlds, frame, metadata, finalEntry⟩
  exact ⟨_, _, operand, emitted.calls_eq ▸ runs⟩

include extension definitions registered faithful observations runtimeViews uninitialized missing in
/-- Completion of the actual renamed emitted code yields the independent source
path at the real dictionaries. The known operand trace fixes its reached state
by evaluation determinism; saved captures are never renamed. -/
theorem emitted_reflects [FunctionCalls.FaultTokens faults]
    (emitted : Emitted compilerProgram project compilation callerFunction available scope node policy ξ inputCode methods outputCode calls)
    {source target : TypeSystem.Ty} (chain : Chain source inputCode.type methods target outputCode.type)
    {caller : Environment} {mapping : LocationMap} {world : StoreTyping}
    {before : Dynamic.Heap} {initialStore store finalStore : Store} {input : Dynamic.Value} {native value : Value}
    (entry : Entry methods ambient.definitions caller mapping world before store)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (represented : ValueRep values.checked registry functions mapping world source input native inputCode.type)
    (operand : Evaluates caller initialStore (inputCode.expression.rename ξ) (.inRight .word native) store)
    (completed : Evaluates caller initialStore (outputCode.expression.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      SelectedTrace methods before input outcome after ∧ PathOutcome methods before input outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        target outputCode.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry methods ambient.definitions caller finalMap finalWorld after finalStore) := by
  obtain ⟨actualInput, reached, actualOperand, runs⟩ := (emitted.spine.renamed_completed_iff ξ).mp completed
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic actualOperand operand
  rw [← emitted.calls_eq] at runs
  obtain ⟨outcome, after, finalMap, finalWorld, trace, related, finalHeaps, maps, worlds, frame, metadata, finalEntry⟩ :=
    reflects functions extension definitions registered faithful observations runtimeViews uninitialized missing chain entry heaps represented runs
  exact ⟨_, _, _, _, trace, trace.sound, related, finalHeaps, maps, worlds, frame, metadata, finalEntry⟩


end Solcore.SourceSemantics.CoreLowering.CallableCoercionPathMeaning
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableCoercionMethodEvidenceInvariant
/-! The concrete builtin body certificate does not inspect a runtime source
dictionary. Its source validity uses only coverage; all retained ledger rows,
source code, actual parameter/frame hooks and saved capture observations are
unchanged. This unit permits a different covering dictionary for the same
source BodyInstance. It does not assert that two selections have that body,
that evidence trees are equal, or that arbitrary bodies ignore evidence. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableCoercionMethodEvidenceInvariant
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedParameterCertificates CallableIndexedParameterMeaning
open SourceCoreCallableIndexedFrames CallableCoercionMethodEntries
open CallableCoercionPathMeaning (MethodProfile Profiles)

variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
  {values : ValuesContext} {program : SourceSemantics.Program} {context : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment}

/-- A proof-facing closure view, not a mutation of the actual saved closure. -/
def view (method : MethodProfile (prepared := prepared) (values := values) (program := program)
    (context := context) (evidence := evidence)) (dictionary : Dynamic.EvidenceEnvironment) : Dynamic.Closure :=
  {method.function with evidence := dictionary}

/-- Source attribution and roots are preserved in full; only coverage changes. -/
theorem frame (method : MethodProfile (prepared := prepared) (values := values) (program := program)
    (context := context) (evidence := evidence)) (dictionary : Dynamic.EvidenceEnvironment)
    (covers : dictionary.Covers method.sourceBody.context) :
    CallableCoercionMethodFrame.Frame method.sourceBody (view method dictionary) :=
  {method.frame with covers}

private theorem covers_extended {owner : Resolved.DeclarationId}
    {initial final : SourceSemantics.Context} {binders : List TypedBinder} {types : List TypeSystem.Ty}
    {dictionary : Dynamic.EvidenceEnvironment}
    (extension : MonoBindersExtend owner initial binders types final)
    (covers : dictionary.Covers initial) : dictionary.Covers final := by
  have same : final.signatures = initial.signatures := by
    clear covers
    induction extension with
    | nil => rfl
    | cons _ head _ ih => exact ih.trans head.context_fields.1
  simpa only [Dynamic.EvidenceEnvironment.Covers, same, extension.assumptions_eq] using covers

/-- The ordered retained requirement ledger and its validity are unchanged.
Monomorphic binder extension preserves the covered assumptions. -/
theorem valid (method : MethodProfile (prepared := prepared) (values := values) (program := program)
    (context := context) (evidence := evidence)) (dictionary : Dynamic.EvidenceEnvironment)
    (covers : dictionary.Covers method.sourceBody.context) :
    CompatibleExpressionLiterals.ContextValid method.named.specialized.function.solvedRequirements
      method.context dictionary :=
  {method.valid with covers := covers_extended method.extended (method.frame.context.symm ▸ covers)}

variable {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (definitions : prepared.layouts.definitions = ambient.definitions)
  (registered : prepared.ancestry.layout.frame.Registered ambient.definitions)
  {faults : FunctionCalls.FaultRep} {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  {methods : Profiles (prepared := prepared) (values := values) (program := program) (context := context) (evidence := evidence)}
  (uninitialized : ∀ method ∈ methods, ∀ id location, faults (.uninitializedLocation location) (method.diagnostics.reasonAt method.named.signature.key id))
  (missing : ∀ method ∈ methods, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((method.diagnostics.reasonAt method.named.signature.key id).add tag))

private theorem arguments {method : MethodProfile (prepared := prepared) (values := values) (program := program) (context := context) (evidence := evidence)}
    {mapping : LocationMap} {world : StoreTyping} {input : Dynamic.Value} {native : Value}
    (represented : ValueRep values.checked registry functions mapping world method.step.source input native method.call.signature.parameterType) :
    Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions) mapping world method.named.inputs [input] [native] := by
  rw [method.bindings]
  apply Arguments.cons _ Arguments.nil
  change ValueRep _ _ _ _ _ method.input.scheme.body _ _ _
  simpa only [method.inputType] using represented

include extension definitions registered faithful observations runtimeViews uninitialized missing in
/-- An independent body derivation may use any covering dictionary for this
exact source body. The same compiled call and saved capture execute it. No
equality with the actual selected dictionary is required. -/
theorem preserves [FunctionCalls.FaultTokens faults] {method : MethodProfile (prepared := prepared) (values := values) (program := program) (context := context) (evidence := evidence)}
    (member : method ∈ methods) {caller : Environment} {mapping : LocationMap} {world : StoreTyping}
    {before after : Dynamic.Heap} {store : Store} {input : Dynamic.Value} {native : Value}
    (entry : Entry methods ambient.definitions caller mapping world before store)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (represented : ValueRep values.checked registry functions mapping world method.step.source input native method.call.signature.parameterType)
    {outcome : Dynamic.ExpressionOutcome} (dictionary : Dynamic.EvidenceEnvironment)
    (covers : dictionary.Covers method.sourceBody.context)
    (trace : BodyOutcome program method.sourceBody dictionary before [input] outcome after)
    (reason : Word) :
    ∃ value finalStore finalMap finalWorld,
      CallableCoercionSpine.Invoke caller reason method.call store (.inRight .word native) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        method.step.target method.call.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry methods ambient.definitions caller finalMap finalWorld after finalStore) := by
  obtain ⟨capture⟩ := entry.captures method member
  have parameterEq : method.function.parameters = method.named.inputs.map Prod.fst := by simp only [method.parameters, method.bindings, List.map_cons, List.map_nil]
  have inputEq : method.function.source.inputs = method.named.inputs.map Prod.fst := by simp only [method.inputs, method.bindings, List.map_cons, List.map_nil]
  have parametersCompiled := method.compiled.parametersCompiled
  rw [← method.source] at parametersCompiled
  have reference : (native :: capture.captured)[capture.embedding.lift (prepared.base.globals.length + 1)]? =
      some (.cellRef prepared.ancestry.layout.frame.type entry.frameLocation) := by
    simpa only [Renaming.lift, Nat.succ_sub_one, List.getElem?_cons_succ] using capture.capturedReference
  obtain ⟨value, finalStore, finalMap, finalWorld, invoked, related, finalHeaps, maps, worlds, frame, metadata, _, _⟩ :=
    CallableCoercionMethodBody.invoke_preserves (prepared := prepared.ancestry) (functions := functions)
      (extension := extension) (program := program) (onError := allocationError) (function := view method dictionary) (certificate := method.certificate)
      (parameters := parameterEq) (inputs := inputEq) (extended := method.extended) (contextValid := valid method dictionary covers)
      (unique := method.unique) (uninitialized := uninitialized method member) (missing := missing method member)
      (faithful := faithful) (functionLeaves := observations) (functionTypes := runtimeViews)
      (acceptedPrefix := parametersCompiled) (definitions := definitions) (registered := registered)
      (acceptedHook := method.compiled.hook) (represented := arguments functions represented)
      (environments := capture.environments) (heaps := heaps) (initialLocals := capture.locals)
      (actualLayout := by
        intro index value found
        exact Core.ReadOnly.EnvironmentsAgree.lift capture.layout native found)
      (actualTyped := .cons represented.runtime_hasType capture.typed)
      (canonicalReference := capture.reference) (actualReference := reference) (unmapped := entry.unmapped)
      (typed := entry.typed) (caller := entry.frame) (snapshots := entry.snapshots) (sourceFrame := frame method dictionary covers)
      rfl rfl rfl capture.installed trace
  exact ⟨value, finalStore, finalMap, finalWorld, invoked, by simpa only [view, method.result, method.signature] using related,
    finalHeaps, maps, worlds, frame, metadata, ⟨entry.extend maps worlds frame metadata⟩⟩

include extension definitions registered faithful observations runtimeViews uninitialized missing in
/-- A completed actual call reflects at any covering dictionary for this exact
body. This does not identify dictionary trees or source method selections. -/
theorem reflects [FunctionCalls.FaultTokens faults] {method : MethodProfile (prepared := prepared) (values := values) (program := program) (context := context) (evidence := evidence)}
    (member : method ∈ methods) {caller : Environment} {mapping : LocationMap} {world : StoreTyping}
    {before : Dynamic.Heap} {store finalStore : Store} {input : Dynamic.Value} {native value : Value} {reason : Word}
    (entry : Entry methods ambient.definitions caller mapping world before store)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (represented : ValueRep values.checked registry functions mapping world method.step.source input native method.call.signature.parameterType)
    (dictionary : Dynamic.EvidenceEnvironment)
    (covers : dictionary.Covers method.sourceBody.context)
    (completed : CallableCoercionSpine.Invoke caller reason method.call store (.inRight .word native) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      BodyOutcome program method.sourceBody dictionary before [input] outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        method.step.target method.call.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry methods ambient.definitions caller finalMap finalWorld after finalStore) := by
  obtain ⟨capture⟩ := entry.captures method member
  have parameterEq : method.function.parameters = method.named.inputs.map Prod.fst := by simp only [method.parameters, method.bindings, List.map_cons, List.map_nil]
  have inputEq : method.function.source.inputs = method.named.inputs.map Prod.fst := by simp only [method.inputs, method.bindings, List.map_cons, List.map_nil]
  have parametersCompiled := method.compiled.parametersCompiled
  rw [← method.source] at parametersCompiled
  have reference : (native :: capture.captured)[capture.embedding.lift (prepared.base.globals.length + 1)]? =
      some (.cellRef prepared.ancestry.layout.frame.type entry.frameLocation) := by
    simpa only [Renaming.lift, Nat.succ_sub_one, List.getElem?_cons_succ] using capture.capturedReference
  obtain ⟨outcome, after, finalMap, finalWorld, trace, related, finalHeaps, maps, worlds, frame, metadata, _, _⟩ :=
    CallableCoercionMethodBody.invoke_reflects (prepared := prepared.ancestry) (functions := functions)
      (extension := extension) (program := program) (onError := allocationError) (function := view method dictionary) (certificate := method.certificate)
      (parameters := parameterEq) (inputs := inputEq) (extended := method.extended) (contextValid := valid method dictionary covers)
      (unique := method.unique) (uninitialized := uninitialized method member) (missing := missing method member)
      (faithful := faithful) (functionLeaves := observations) (functionTypes := runtimeViews)
      (acceptedPrefix := parametersCompiled) (definitions := definitions) (registered := registered)
      (acceptedHook := method.compiled.hook) (represented := arguments functions represented)
      (environments := capture.environments) (heaps := heaps) (initialLocals := capture.locals)
      (actualLayout := by
        intro index value found
        exact Core.ReadOnly.EnvironmentsAgree.lift capture.layout native found)
      (actualTyped := .cons represented.runtime_hasType capture.typed)
      (canonicalReference := capture.reference) (actualReference := reference) (unmapped := entry.unmapped)
      (typed := entry.typed) (caller := entry.frame) (snapshots := entry.snapshots) (sourceFrame := frame method dictionary covers)
      rfl rfl rfl capture.installed completed
  exact ⟨outcome, after, finalMap, finalWorld, trace, by simpa only [view, method.result, method.signature] using related,
    finalHeaps, maps, worlds, frame, metadata, ⟨entry.extend maps worlds frame metadata⟩⟩

end Solcore.SourceSemantics.CoreLowering.CallableCoercionMethodEvidenceInvariant
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableCoercionSelectedInvocation
/-! Actual compiler selection fixes the complete independent source body.
An arbitrary selected dictionary is kept unchanged by the body theorem; no
semantic law is stored in the static receipt or runtime Entry. The concrete
body certificate and saved closure/capture authority remain explicit. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableCoercionSelectedInvocation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CallableIndexedHistory
open SourceCoreCallableIndexedFrames CallableCoercionMethodEntries CallableCoercionPathMeaning

variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
  {values : ValuesContext} {compilerProgram : CheckedProgram} {raw : Workspace.RawWorkspace} {checkFuel : Nat}
  (checkedAccepted : checkProgram raw checkFuel = .ok compilerProgram)
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {method : MethodProfile (prepared := prepared) (values := values) (program := Program.ofChecked compilerProgram)
    (context := context) (evidence := evidence)}
  {rest : Profiles (prepared := prepared) (values := values) (program := Program.ofChecked compilerProgram)
    (context := context) (evidence := evidence)}
  {project : SourceCoreEvidence.Projector} {compilation : SourceCoreFunctions.Context}
  {callerFunction : SourceSpecialization.SpecializedFunction} {available : SourceCompilationPlan.EvidenceEnvironment}
  {scope : SourceCoreBasic.Scope} {node : ExpressionNode} {policy : SourceCoreFunctions.CallablePolicy}
  {ξ : Renaming} {input output : SourceCoreBasic.LoweredExpr} {calls : List CallableCoercionSpine.Call}
  (ledger : context.solvedRequirements = callerFunction.function.solvedRequirements)
  (emitted : Emitted compilerProgram project compilation callerFunction available scope node policy ξ input (method :: rest) output calls)

include checkedAccepted ledger emitted in
/-- The complete source body, including context and ordered retained ledger,
is fixed. Actual emitted records and dictionaries are retained by `emitted`. -/
theorem source_body {selectedBody : Dynamic.BodyInstance} {dictionary : Dynamic.EvidenceEnvironment}
    (selected : Dynamic.OperatorMethodSelected (Program.ofChecked compilerProgram) context evidence "Coerce" "coerce"
      method.step.requirements selectedBody dictionary) : selectedBody = method.sourceBody := by
  cases emitted with
  | cons actual _ _ _ tail =>
    obtain ⟨receipt⟩ := CallableCoercionMethodCertificates.of_accepted actual.selectedMethod
    exact CallableCoercionSelectionIdentity.body_eq (CallableCoercionSelectionIdentity.Catalog.of_checked checkedAccepted)
      (CallableCoercionSelectionIdentity.primary_unique ledger receipt.primarySelected) selected method.selected

variable {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (definitions : prepared.layouts.definitions = ambient.definitions)
  (registered : prepared.ancestry.layout.frame.Registered ambient.definitions)
  {faults : FunctionCalls.FaultRep} {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  {methods : Profiles (prepared := prepared) (values := values) (program := Program.ofChecked compilerProgram)
    (context := context) (evidence := evidence)}
  (uninitialized : ∀ method ∈ methods, ∀ id location, faults (.uninitializedLocation location) (method.diagnostics.reasonAt method.named.signature.key id))
  (missing : ∀ method ∈ methods, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((method.diagnostics.reasonAt method.named.signature.key id).add tag))
  (member : method ∈ methods) {caller : Environment} {mapping : LocationMap} {world : StoreTyping}
  {before : Dynamic.Heap} {store : Store} {value : Dynamic.Value} {native : Value}
  (entry : Entry methods ambient.definitions caller mapping world before store)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
  (represented : ValueRep values.checked registry functions mapping world method.step.source value native method.call.signature.parameterType)

include checkedAccepted ledger emitted extension definitions registered faithful observations runtimeViews uninitialized missing member entry heaps represented in
/-- Independent selection and body evaluation drive the actual call. Neither
the source body nor the dictionary is required equal to a compiler annotation. -/
theorem preserves [FunctionCalls.FaultTokens faults] {selectedBody : Dynamic.BodyInstance} {dictionary : Dynamic.EvidenceEnvironment}
    (selected : Dynamic.OperatorMethodSelected (Program.ofChecked compilerProgram) context evidence "Coerce" "coerce"
      method.step.requirements selectedBody dictionary)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : BodyOutcome (Program.ofChecked compilerProgram) selectedBody dictionary before [value] outcome after)
    (reason : Word) :
    ∃ result finalStore finalMap finalWorld,
      CallableCoercionSpine.Invoke caller reason method.call store (.inRight .word native) result finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        method.step.target method.call.signature.resultType faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry methods ambient.definitions caller finalMap finalWorld after finalStore) := by
  have same := source_body checkedAccepted ledger emitted selected
  subst selectedBody
  have covers : dictionary.Covers method.sourceBody.context := by
    cases selected with
    | intro _ _ _ _ _ _ _ _ _ _ _ _ _ covers => exact covers
  exact CallableCoercionMethodEvidenceInvariant.preserves functions extension definitions registered faithful observations runtimeViews
    uninitialized missing member entry heaps represented dictionary covers trace reason

include checkedAccepted ledger emitted extension definitions registered faithful observations runtimeViews uninitialized missing member entry heaps represented in
/-- A completed actual call reflects at any independently selected source body
and dictionary. Its source outcome and heap are existential, not identified by
evidence equality or by a source/native fuel comparison. -/
theorem reflects [FunctionCalls.FaultTokens faults] {selectedBody : Dynamic.BodyInstance} {dictionary : Dynamic.EvidenceEnvironment}
    (selected : Dynamic.OperatorMethodSelected (Program.ofChecked compilerProgram) context evidence "Coerce" "coerce"
      method.step.requirements selectedBody dictionary)
    {result : Value} {finalStore : Store} {reason : Word}
    (completed : CallableCoercionSpine.Invoke caller reason method.call store (.inRight .word native) result finalStore) :
    ∃ outcome after finalMap finalWorld,
      BodyOutcome (Program.ofChecked compilerProgram) selectedBody dictionary before [value] outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        method.step.target method.call.signature.resultType faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry methods ambient.definitions caller finalMap finalWorld after finalStore) := by
  have same := source_body checkedAccepted ledger emitted selected
  subst selectedBody
  have covers : dictionary.Covers method.sourceBody.context := by
    cases selected with
    | intro _ _ _ _ _ _ _ _ _ _ _ _ _ covers => exact covers
  exact CallableCoercionMethodEvidenceInvariant.reflects functions extension definitions registered faithful observations runtimeViews
    uninitialized missing member entry heaps represented dictionary covers completed

end Solcore.SourceSemantics.CoreLowering.CallableCoercionSelectedInvocation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableCoercionRequirementSafety
/-! Actual singleton selection excludes unavailable requirements only at reached
identities. The ordered list may repeat identities; no global ledger uniqueness
or dictionary equality is assumed. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableCoercionRequirementSafety
open Frontend SourceInference Solcore.SourceSemantics.Dynamic

abbrev UniqueAt (context : Context) (id : RequirementId) : Prop :=
  ∀ first second, ContainsRequirement context id first → ContainsRequirement context id second → first = second

theorem excludes_unavailable {context : Context} {caller : EvidenceEnvironment}
    {id : RequirementId} {goal : ProgramPredicate} {closed : TraitEvidence}
    (unique : UniqueAt context id) (produces : RequirementProducesEvidence context caller id goal closed)
    (fault : RequirementUnavailable context caller id) : False := by
  cases produces with
  | intro contains _ representation _ closes _ =>
    cases fault with
    | missing absent => exact absent _ contains.1 contains.2
    | evidence otherContains otherRepresentation failed =>
      cases unique _ _ contains otherContains
      cases representation.functional otherRepresentation
      exact closes.excludes_fault failed

theorem excludes_list_fault {context : Context} {caller returned : EvidenceEnvironment}
    {ids : List RequirementId} {goals : List ProgramPredicate} {failed : RequirementId}
    (unique : ∀ id ∈ ids, UniqueAt context id)
    (produces : RequirementsProduceEnvironment context caller ids goals returned)
    (fault : RequirementListFaults context caller ids failed) : False := by
  induction produces generalizing failed with
  | nil => cases fault
  | cons head tail ih =>
    cases fault with
    | head unavailable => exact excludes_unavailable (unique _ (by simp)) head unavailable
    | tail _ failed => exact ih (fun id member => unique id (List.mem_cons_of_mem _ member)) failed

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {value : β}
    (accepted : action >>= next = .ok value) : ∃ item, action = .ok item ∧ next item = .ok value := by
  cases action with
  | error error => cases accepted
  | ok item => exact ⟨item, rfl, accepted⟩

/-- Each actual list row has its own singleton receipt, even when an identity
occurs again later in the list. Unrelated ledger rows are unconstrained. -/
theorem list_unique {program : CheckedProgram} {caller : SourceSpecialization.SpecializedFunction}
    {node : ExpressionNode} {available returned : SourceCompilationPlan.EvidenceEnvironment}
    {ids : List RequirementId} {goals : List ProgramPredicate} {context : Context}
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (accepted : SourceCompilationPlan.exactRuntimeRequirementEvidenceList program caller node available ids goals = .ok returned) :
    ∀ id ∈ ids, UniqueAt context id := by
  induction ids generalizing goals returned with
  | nil => simp
  | cons id ids ih =>
    cases goals with
    | nil => cases accepted
    | cons goal goals =>
      unfold SourceCompilationPlan.exactRuntimeRequirementEvidenceList at accepted
      obtain ⟨head, headAccepted, accepted⟩ := bind_ok accepted
      obtain ⟨tail, tailAccepted, _⟩ := bind_ok accepted
      intro key member
      rcases List.mem_cons.mp member with rfl | member
      · exact CallableCoercionSelectionIdentity.primary_unique ledger headAccepted
      · exact ih tailAccepted key member

/-- Actual primary and ordered method roots exclude faults for any method
selector. Only the reached ledger rows are identified. -/
theorem selected_safe_for {compiler : CheckedProgram} {caller : SourceSpecialization.SpecializedFunction}
    {node : ExpressionNode} {available : SourceCompilationPlan.EvidenceEnvironment}
    {primaryId : RequirementId} {methodIds : List RequirementId} {arity : Nat}
    {traitName methodName : String} {method : ExecutableImplMethods.CheckedMethod} {context : Context}
    {program : Program} {evidence dictionary : EvidenceEnvironment} {body : BodyInstance}
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (roots : CallableCoercionMethodCertificates.Roots compiler caller node available
      primaryId methodIds arity methodName method)
    (selected : OperatorMethodSelected program context evidence traitName methodName
      (primaryId :: methodIds) body dictionary)
    {failed : RequirementId} (fault : RequirementListFaults context evidence (primaryId :: methodIds) failed) : False := by
  have primaryUnique := CallableCoercionSelectionIdentity.primary_unique ledger roots.primarySelected
  have remainingUnique := list_unique ledger roots.methodsSelected
  cases selected with
  | intro primary _ _ _ _ _ _ _ _ _ remaining _ _ _ =>
    cases primary with
    | intro produced _ =>
      cases fault with
      | head unavailable => exact excludes_unavailable primaryUnique produced unavailable
      | tail _ failed => exact excludes_list_fault remainingUnique remaining failed


/-- Successful source selection provides the real evidence closures; actual
compiler selection identifies the ledger rows used by any competing fault. -/
theorem selected_safe {compiler : CheckedProgram} {caller : SourceSpecialization.SpecializedFunction}
    {node : ExpressionNode} {available : SourceCompilationPlan.EvidenceEnvironment}
    {step : CoercionStep} {method : ExecutableImplMethods.CheckedMethod} {context : Context}
    {program : Program} {evidence dictionary : EvidenceEnvironment} {body : BodyInstance}
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (accepted : SourceCompilationPlan.checkedCoercionMethod compiler caller node available step = .ok method)
    (selected : OperatorMethodSelected program context evidence "Coerce" "coerce" step.requirements body dictionary)
    {failed : RequirementId} (fault : RequirementListFaults context evidence step.requirements failed) : False := by
  obtain ⟨receipt⟩ := CallableCoercionMethodCertificates.of_accepted accepted
  exact selected_safe_for ledger receipt.roots selected fault

end Solcore.SourceSemantics.CoreLowering.CallableCoercionRequirementSafety
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableCoercionSourcePathMeaning
/-! Any independent finite source coercion path drives the actual ordered
compiler calls. Real selected rows exclude requirement faults; arbitrary source
method dictionaries pass unchanged to the concrete body theorem. Initial saved
captures, frame history and operand evaluation remain explicit. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableCoercionSourcePathMeaning
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CallableIndexedHistory
open SourceCoreCallableIndexedFrames CallableCoercionMethodEntries CallableCoercionPathMeaning

section Common
variable {α : Type} {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}

def PathFor (row : α → Row) (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (methods : List α)
    (before : Dynamic.Heap) (input : Dynamic.Value) (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap) : Prop :=
  match outcome with
  | .value result => Dynamic.CoercionPathExecutes program context evidence before (methods.map (fun method => (row method).step)) input result after
  | .fault reason => Dynamic.CoercionPathFaults program context evidence before (methods.map (fun method => (row method).step)) input reason after

def StepOutcomeFor (step : CoercionStep) (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (before : Dynamic.Heap) (input : Dynamic.Value)
    (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap) : Prop :=
  match outcome with
  | .value result => Dynamic.CoercionStepExecutes program context evidence before step input result after
  | .fault reason => Dynamic.CoercionStepFaults program context evidence before step input reason after

private theorem path_cons_for {row : α → Row} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {method : α} {rest : List α}
    {before after : Dynamic.Heap} {input : Dynamic.Value} {outcome : Dynamic.ExpressionOutcome}
    (trace : PathFor row program context evidence (method :: rest) before input outcome after) :
    (∃ middle value, Dynamic.CoercionStepExecutes program context evidence before (row method).step input value middle ∧
      PathFor row program context evidence rest middle value outcome after) ∨
    (∃ reason, outcome = .fault reason ∧ Dynamic.CoercionStepFaults program context evidence before (row method).step input reason after) := by
  cases outcome with
  | value result => cases trace with | cons head tail => exact .inl ⟨_, _, head, tail⟩
  | fault reason =>
    cases trace with
    | head failed => exact .inr ⟨_, rfl, failed⟩
    | tail head failed => exact .inl ⟨_, _, head, failed⟩

/-- Internal one-step continuation for an independent source path. Concrete
public consumers close it with their actual source selection and body tree. -/
def StepPreservesFor (row : α → Row)
    (State : LocationMap → StoreTyping → Dynamic.Heap → Store → Type)
    (functions : FunctionModel values.checked.catalog ambient)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (caller : Environment) (reason : Word) (methods : List α) : Prop :=
  ∀ {method mapping world before after store input native outcome}, method ∈ methods →
    State mapping world before store →
    CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store →
    ValueRep values.checked registry functions mapping world (row method).step.source input native
      (row method).call.signature.parameterType →
    StepOutcomeFor (row method).step program context evidence before input outcome after →
    ∃ result finalStore finalMap finalWorld,
      CallableCoercionSpine.Invoke caller reason (row method).call store (.inRight .word native) result finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        (row method).step.target (row method).call.signature.resultType faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (State finalMap finalWorld after finalStore)

variable {row : α → Row} {State : LocationMap → StoreTyping → Dynamic.Heap → Store → Type}
  {functions : FunctionModel values.checked.catalog ambient} {registry : SourceCoreRawMetadata.Registry}
  {faults : FunctionCalls.FaultRep} {program : Program} {context : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment} {caller : Environment} {reason : Word}

theorem preserves_for
    (extendState : ∀ {mapping nextMap world nextWorld before after store finalStore},
      State mapping world before store → LocationMap.Extends mapping nextMap → WorldExtends world nextWorld →
      AdministrativePreserved mapping store nextMap finalStore → Dynamic.HeapMetadataExtend before after →
      State nextMap nextWorld after finalStore)
    {source target : TypeSystem.Ty} {inputType outputType : Ty} {methods : List α}
    (step : StepPreservesFor row State functions registry faults program context evidence caller reason methods)
    (chain : ChainFor row source inputType methods target outputType)
    {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap} {store : Store}
    {input : Dynamic.Value} {native : Value} {outcome : Dynamic.ExpressionOutcome}
    (entry : State mapping world before store)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (represented : ValueRep values.checked registry functions mapping world source input native inputType)
    (trace : PathFor row program context evidence methods before input outcome after) :
    ∃ value finalStore finalMap finalWorld,
      CallableCoercionSpine.Runs caller reason store (.inRight .word native) (methods.map (fun method => (row method).call)) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        target outputType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (State finalMap finalWorld after finalStore) := by
  induction chain generalizing mapping world before after store input native outcome with
  | nil source type =>
    cases outcome with
    | value value =>
      cases trace
      exact ⟨_, _, _, _, .nil, .value represented, heaps, .refl _, .refl _, .refl _ _, .refl _, ⟨entry⟩⟩
    | fault reason => cases trace
  | @cons method rest target output chain ih =>
    rcases path_cons_for trace with ⟨middle, converted, head, tail⟩ | ⟨failed, rfl, head⟩
    · obtain ⟨result, middleStore, middleMap, middleWorld, invoked, related, middleHeaps, maps, worlds, frame, metadata, ⟨nextEntry⟩⟩ :=
        step (outcome := .value converted) (List.mem_cons_self) entry heaps represented head
      cases related with
      | value middleRepresented =>
        obtain ⟨result, finalStore, finalMap, finalWorld, runs, related, finalHeaps, tailMaps, tailWorlds, tailFrame, tailMetadata, _⟩ :=
          ih (fun member => step (List.mem_cons_of_mem _ member)) nextEntry middleHeaps middleRepresented tail
        exact ⟨_, _, _, _, .cons invoked runs, related, finalHeaps, maps.trans tailMaps, worlds.trans tailWorlds,
          frame.trans tailFrame, metadata.trans tailMetadata,
          ⟨extendState entry (maps.trans tailMaps) (worlds.trans tailWorlds) (frame.trans tailFrame) (metadata.trans tailMetadata)⟩⟩
    · obtain ⟨result, finalStore, finalMap, finalWorld, invoked, related, finalHeaps, maps, worlds, frame, metadata, finalEntry⟩ :=
        step (outcome := .fault failed) (List.mem_cons_self) entry heaps represented head
      cases related with
      | fault faultRep =>
        refine ⟨_, _, _, _, .cons invoked (CallableCoercionSpine.Runs.failure caller reason finalStore _ _ _),
          ?_, finalHeaps, maps, worlds, frame, metadata, finalEntry⟩
        rw [chain.final_type]
        exact .fault faultRep

end Common

variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
  {values : ValuesContext} {compilerProgram : CheckedProgram} {raw : Workspace.RawWorkspace} {checkFuel : Nat}
  (checkedAccepted : checkProgram raw checkFuel = .ok compilerProgram)
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {method : MethodProfile (prepared := prepared) (values := values) (program := Program.ofChecked compilerProgram)
    (context := context) (evidence := evidence)}
  {rest : Profiles (prepared := prepared) (values := values) (program := Program.ofChecked compilerProgram)
    (context := context) (evidence := evidence)}
  {project : SourceCoreEvidence.Projector} {compilation : SourceCoreFunctions.Context}
  {callerFunction : SourceSpecialization.SpecializedFunction} {available : SourceCompilationPlan.EvidenceEnvironment}
  {scope : SourceCoreBasic.Scope} {node : ExpressionNode} {policy : SourceCoreFunctions.CallablePolicy}
  {ξ : Renaming} {input output : SourceCoreBasic.LoweredExpr} {calls : List CallableCoercionSpine.Call}
  (ledger : context.solvedRequirements = callerFunction.function.solvedRequirements)
  (emitted : Emitted compilerProgram project compilation callerFunction available scope node policy ξ input (method :: rest) output calls)

section Step
variable {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (definitions : prepared.layouts.definitions = ambient.definitions)
  (registered : prepared.ancestry.layout.frame.Registered ambient.definitions)
  {faults : FunctionCalls.FaultRep} {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  {methods : Profiles (prepared := prepared) (values := values) (program := Program.ofChecked compilerProgram)
    (context := context) (evidence := evidence)}
  (uninitialized : ∀ method ∈ methods, ∀ id location, faults (.uninitializedLocation location) (method.diagnostics.reasonAt method.named.signature.key id))
  (missing : ∀ method ∈ methods, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((method.diagnostics.reasonAt method.named.signature.key id).add tag))
  (member : method ∈ methods) {caller : Environment} {mapping : LocationMap} {world : StoreTyping}
  {before : Dynamic.Heap} {store : Store} {value : Dynamic.Value} {native : Value}
  (entry : Entry methods ambient.definitions caller mapping world before store)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
  (represented : ValueRep values.checked registry functions mapping world method.step.source value native method.call.signature.parameterType)

include checkedAccepted ledger emitted extension definitions registered faithful observations runtimeViews uninitialized missing member entry heaps represented in
/-- Independent selection and body evaluation drive the actual call. Neither
the source body nor the dictionary is required equal to a compiler annotation. -/
theorem step_preserves [FunctionCalls.FaultTokens faults] {sourceResult : Dynamic.Value} {after : Dynamic.Heap}
    (trace : Dynamic.CoercionStepExecutes (Program.ofChecked compilerProgram) context evidence before method.step value sourceResult after)
    (reason : Word) :
    ∃ result finalStore finalMap finalWorld,
      CallableCoercionSpine.Invoke caller reason method.call store (.inRight .word native) result finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        method.step.target method.call.signature.resultType faults (.value sourceResult) result ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry methods ambient.definitions caller finalMap finalWorld after finalStore) := by
  cases trace with
  | primitive absent _ => exact False.elim (absent _ _ method.selected)
  | method selected invoked =>
    exact CallableCoercionSelectedInvocation.preserves checkedAccepted ledger emitted functions extension definitions registered
      faithful observations runtimeViews uninitialized missing member entry heaps represented selected (.value invoked) reason

include checkedAccepted ledger emitted extension definitions registered faithful observations runtimeViews uninitialized missing member entry heaps represented in
/-- Independent selection and body evaluation drive the actual call. Neither
the source body nor the dictionary is required equal to a compiler annotation. -/
theorem step_fault_preserves [FunctionCalls.FaultTokens faults] {fault : Dynamic.SemanticFault} {after : Dynamic.Heap}
    (trace : Dynamic.CoercionStepFaults (Program.ofChecked compilerProgram) context evidence before method.step value fault after)
    (reason : Word) :
    ∃ result finalStore finalMap finalWorld,
      CallableCoercionSpine.Invoke caller reason method.call store (.inRight .word native) result finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        method.step.target method.call.signature.resultType faults (.fault fault) result ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry methods ambient.definitions caller finalMap finalWorld after finalStore) := by
  cases trace with
  | requirement failed =>
    cases emitted with
    | cons actual _ _ _ _ =>
      exact False.elim (CallableCoercionRequirementSafety.selected_safe ledger actual.selectedMethod method.selected failed)
  | primitiveInput absent _ _ => exact False.elim (absent _ _ method.selected)
  | method selected failed =>
    exact CallableCoercionSelectedInvocation.preserves checkedAccepted ledger emitted functions extension definitions registered
      faithful observations runtimeViews uninitialized missing member entry heaps represented selected (.fault failed) reason

end Step

variable {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (definitions : prepared.layouts.definitions = ambient.definitions)
  (registered : prepared.ancestry.layout.frame.Registered ambient.definitions)
  {faults : FunctionCalls.FaultRep} {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  {methods : Profiles (prepared := prepared) (values := values) (program := Program.ofChecked compilerProgram)
    (context := context) (evidence := evidence)}
  (uninitialized : ∀ method ∈ methods, ∀ id location, faults (.uninitializedLocation location) (method.diagnostics.reasonAt method.named.signature.key id))
  (missing : ∀ method ∈ methods, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((method.diagnostics.reasonAt method.named.signature.key id).add tag))

private theorem path_cons {before after : Dynamic.Heap} {input : Dynamic.Value} {outcome : Dynamic.ExpressionOutcome}
    (trace : PathOutcome (method :: rest) before input outcome after) :
    (∃ middle value, Dynamic.CoercionStepExecutes (Program.ofChecked compilerProgram) context evidence
      before method.step input value middle ∧ PathOutcome rest middle value outcome after) ∨
    (∃ reason, outcome = .fault reason ∧ Dynamic.CoercionStepFaults (Program.ofChecked compilerProgram)
      context evidence before method.step input reason after) := by
  exact path_cons_for (row := MethodProfile.row) trace

private theorem emitted_singleton
    {inputCode outputCode : SourceCoreBasic.LoweredExpr} {calls : List CallableCoercionSpine.Call}
    (emitted : Emitted compilerProgram project compilation callerFunction available scope node policy ξ inputCode methods outputCode calls)
    {method : MethodProfile (prepared := prepared) (values := values) (program := Program.ofChecked compilerProgram)
      (context := context) (evidence := evidence)} (member : method ∈ methods) :
    ∃ input output call, Emitted compilerProgram project compilation callerFunction available scope node policy ξ input [method] output [call] := by
  induction emitted with
  | nil => cases member
  | @cons input middle output call calls head rest actual slot record dictionary tail ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨input, middle, call, .cons actual slot record dictionary .nil⟩
    · exact ih member

include checkedAccepted ledger extension definitions registered faithful observations runtimeViews in
/-- Preserve the original independent path, including its exact successful
prefix and first fault. No selected-dictionary annotation is required. -/
theorem preserves
    [FunctionCalls.FaultTokens faults] (uninitialized : ∀ method ∈ methods, ∀ id location,
      faults (.uninitializedLocation location) (method.diagnostics.reasonAt method.named.signature.key id))
    (missing : ∀ method ∈ methods, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
      faults (.missingMappingDefault value) ((method.diagnostics.reasonAt method.named.signature.key id).add tag))
    {inputCode outputCode : SourceCoreBasic.LoweredExpr} {calls : List CallableCoercionSpine.Call}
    (emitted : Emitted compilerProgram project compilation callerFunction available scope node policy ξ inputCode methods outputCode calls)
    {source target : TypeSystem.Ty} {inputType outputType : Ty}
    (chain : Chain source inputType methods target outputType)
    {caller : Environment} {mapping : LocationMap} {world : StoreTyping}
    {before after : Dynamic.Heap} {store : Store} {input : Dynamic.Value} {native : Value}
    (entry : Entry methods ambient.definitions caller mapping world before store)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (represented : ValueRep values.checked registry functions mapping world source input native inputType)
    {outcome : Dynamic.ExpressionOutcome} (trace : PathOutcome methods before input outcome after)
    (reason : Word) :
    ∃ value finalStore finalMap finalWorld,
      CallableCoercionSpine.Runs caller reason store (.inRight .word native) (methods.map (·.call)) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        target outputType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry methods ambient.definitions caller finalMap finalWorld after finalStore) := by
  apply preserves_for (row := MethodProfile.row)
    (State := fun mapping world heap store => Entry methods ambient.definitions caller mapping world heap store)
    (fun entry maps worlds frame metadata => entry.extend maps worlds frame metadata)
    (functions := functions) (registry := registry) (faults := faults)
    (program := Program.ofChecked compilerProgram) (context := context) (evidence := evidence)
    (caller := caller) (reason := reason) (chain := chain.toFor)
    (entry := entry) (heaps := heaps) (represented := represented) (trace := trace)
  intro method mapping world before after store input native outcome member entry heaps represented execution
  obtain ⟨inputCode, outputCode, call, actual⟩ := emitted_singleton emitted member
  cases outcome with
  | value value =>
    exact step_preserves checkedAccepted ledger actual functions extension definitions registered faithful observations runtimeViews
      uninitialized missing member entry heaps represented execution reason
  | fault failed =>
    exact step_fault_preserves checkedAccepted ledger actual functions extension definitions registered faithful observations runtimeViews
      uninitialized missing member entry heaps represented execution reason

variable {inputCode outputCode : SourceCoreBasic.LoweredExpr}

include checkedAccepted ledger extension definitions registered faithful observations runtimeViews uninitialized missing in
/-- The actual emitted expression, after a successful operand, preserves the
independent source path. The operand is outside this path-only theorem. -/
theorem emitted_preserves [FunctionCalls.FaultTokens faults]
    (emitted : Emitted compilerProgram project compilation callerFunction available scope node policy ξ inputCode methods outputCode calls)
    {source target : TypeSystem.Ty} (chain : Chain source inputCode.type methods target outputCode.type)
    {caller : Environment} {mapping : LocationMap} {world : StoreTyping}
    {before after : Dynamic.Heap} {initialStore store : Store} {input : Dynamic.Value} {native : Value}
    (entry : Entry methods ambient.definitions caller mapping world before store)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (represented : ValueRep values.checked registry functions mapping world source input native inputCode.type)
    (operand : Evaluates caller initialStore (inputCode.expression.rename ξ) (.inRight .word native) store)
    {outcome : Dynamic.ExpressionOutcome} (trace : PathOutcome methods before input outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates caller initialStore (outputCode.expression.rename ξ) value finalStore ∧
      PathOutcome methods before input outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        target outputCode.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry methods ambient.definitions caller finalMap finalWorld after finalStore) := by
  obtain ⟨value, finalStore, finalMap, finalWorld, runs, related, finalHeaps, maps, worlds, frame, metadata, finalEntry⟩ :=
    preserves checkedAccepted ledger functions extension definitions registered faithful observations runtimeViews uninitialized missing emitted chain entry heaps represented trace compilation.internalReason
  refine ⟨_, _, _, _, (emitted.spine.renamed_completed_iff ξ).mpr ?_, trace, related,
    finalHeaps, maps, worlds, frame, metadata, finalEntry⟩
  exact ⟨_, _, operand, emitted.calls_eq ▸ runs⟩

include extension definitions registered faithful observations runtimeViews uninitialized missing in
/-- Completion of the actual renamed emitted code yields the independent source
path at the real dictionaries. The known operand trace fixes its reached state
by evaluation determinism; saved captures are never renamed. -/
theorem emitted_reflects [FunctionCalls.FaultTokens faults]
    (emitted : Emitted compilerProgram project compilation callerFunction available scope node policy ξ inputCode methods outputCode calls)
    {source target : TypeSystem.Ty} (chain : Chain source inputCode.type methods target outputCode.type)
    {caller : Environment} {mapping : LocationMap} {world : StoreTyping}
    {before : Dynamic.Heap} {initialStore store finalStore : Store} {input : Dynamic.Value} {native value : Value}
    (entry : Entry methods ambient.definitions caller mapping world before store)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (represented : ValueRep values.checked registry functions mapping world source input native inputCode.type)
    (operand : Evaluates caller initialStore (inputCode.expression.rename ξ) (.inRight .word native) store)
    (completed : Evaluates caller initialStore (outputCode.expression.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      PathOutcome methods before input outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        target outputCode.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry methods ambient.definitions caller finalMap finalWorld after finalStore) := by
  obtain ⟨outcome, after, finalMap, finalWorld, _, trace, related, finalHeaps, maps, worlds, frame, metadata, finalEntry⟩ :=
    CallableCoercionPathMeaning.emitted_reflects functions extension definitions registered faithful observations runtimeViews
      uninitialized missing emitted chain entry heaps represented operand completed
  exact ⟨_, _, _, _, trace, related, finalHeaps, maps, worlds, frame, metadata, finalEntry⟩

end Solcore.SourceSemantics.CoreLowering.CallableCoercionSourcePathMeaning
end
