import Solcore.SourceSemantics.CoreLowering.CallableCoercionMethodFrame
import Solcore.SourceSemantics.CoreLowering.BuiltinNamedCallMeaning
import Solcore.SourceSemantics.CoreLowering.CallableCoercionSpineEvaluation

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
theorem preserves {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
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
theorem reflects {value : Value} {finalStore : Store}
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
theorem invoke_preserves {call : CallableCoercionSpine.Call} {callerEnvironment captured : Environment}
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
theorem invoke_reflects {call : CallableCoercionSpine.Call} {callerEnvironment captured : Environment}
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
