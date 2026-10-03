import Solcore.SourceSemantics.CoreLowering.CallableCoercionMethodEvidenceInvariant
import Solcore.Test.SourceCompilerFeatureSupport

/-! The same accepted concrete method body is consumed at arbitrary covering
source dictionaries. None of the formal consumers identify evidence trees or
assume a universal body law. The structural origin example is about the source
relation; it is not a counterexample to compiler acceptance. Runtime checks use
actual differently ordered caller dictionaries, unchanged selected full method
records, exact effects and public suspension/resumption. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
namespace Tests.SourceCoreCallableCoercionMethodEvidenceInvariant
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CallableIndexedHistory SourceCoreCallableIndexedFrames
open CallableCoercionMethodEntries CallableCoercionPathMeaning

/-- Origin attribution preserves duplicate positions but does not choose a
unique full tree among a caller and a root with the same goal. -/
theorem origins_not_functional {goal : ProgramPredicate} {left right : TraitEvidence}
    (rightGoal : right.goal = goal) (different : left ≠ right) :
    Dynamic.EvidenceEnvironment.AssembledFrom [(goal, left)] [right] [goal, goal]
      [(goal, left), (goal, right)] ∧
    Dynamic.EvidenceEnvironment.AssembledFrom [(goal, left)] [right] [goal, goal]
      [(goal, right), (goal, left)] ∧
    [(goal, left), (goal, right)] ≠ [(goal, right), (goal, left)] := by
  have caller : Dynamic.EvidenceEntryOriginates [(goal, left)] [right] goal left := .caller .head
  have root : Dynamic.EvidenceEntryOriginates [(goal, left)] [right] goal right :=
    .root (by simp) (.self _) rightGoal
  refine ⟨.cons caller (.cons root .nil), .cons root (.cons caller .nil), ?_⟩
  intro equal
  exact different (congrArg Prod.snd (List.cons.inj equal).1)

variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
  {values : ValuesContext} {program : SourceSemantics.Program} {context : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment}
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

variable {method : MethodProfile (prepared := prepared) (values := values) (program := program)
    (context := context) (evidence := evidence)}
  (member : method ∈ methods) {caller : Environment} {mapping : LocationMap} {world : StoreTyping}
  {before : Dynamic.Heap} {store : Store} {input : Dynamic.Value} {native : Value}
  (entry : Entry methods ambient.definitions caller mapping world before store)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
  (represented : ValueRep values.checked registry functions mapping world method.step.source input native method.call.signature.parameterType)

include extension definitions registered faithful observations runtimeViews uninitialized missing member entry heaps represented in
/-- The source selector supplies coverage. Its dictionary need not equal the
one in the static Method receipt; the actual saved call is unchanged. -/
theorem arbitrary_selected_preserves {dictionary : Dynamic.EvidenceEnvironment}
    (selected : Dynamic.OperatorMethodSelected program context evidence "Coerce" "coerce"
      method.step.requirements method.sourceBody dictionary)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
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
  have covered : dictionary.Covers method.sourceBody.context := by
    cases selected with | intro _ _ _ _ _ _ _ _ _ _ _ _ _ covered => exact covered
  exact CallableCoercionMethodEvidenceInvariant.preserves functions extension definitions registered faithful observations runtimeViews
    uninitialized missing member entry heaps represented dictionary covered trace reason

include extension definitions registered faithful observations runtimeViews uninitialized missing member entry heaps represented in
/-- One completed actual call reflects under both covering dictionaries. The
outcomes and heaps remain separately represented; no source determinism or
source dictionary equality is inferred from native determinism. -/
theorem completed_at_two_dictionaries
    (first second : Dynamic.EvidenceEnvironment)
    (firstCovers : first.Covers method.sourceBody.context)
    (secondCovers : second.Covers method.sourceBody.context)
    {result : Value} {finalStore : Store} {reason : Word}
    (completed : CallableCoercionSpine.Invoke caller reason method.call store (.inRight .word native) result finalStore) :
    (∃ outcome after finalMap finalWorld,
      BodyOutcome program method.sourceBody first before [input] outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        method.step.target method.call.signature.resultType faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore) ∧
    (∃ outcome after finalMap finalWorld,
      BodyOutcome program method.sourceBody second before [input] outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        method.step.target method.call.signature.resultType faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore) := by
  obtain ⟨firstOutcome, firstHeap, firstMap, firstWorld, firstBody, firstResult, firstHeapRep, _⟩ :=
    CallableCoercionMethodEvidenceInvariant.reflects functions extension definitions registered faithful observations runtimeViews
      uninitialized missing member entry heaps represented first firstCovers completed
  obtain ⟨secondOutcome, secondHeap, secondMap, secondWorld, secondBody, secondResult, secondHeapRep, _⟩ :=
    CallableCoercionMethodEvidenceInvariant.reflects functions extension definitions registered faithful observations runtimeViews
      uninitialized missing member entry heaps represented second secondCovers completed
  exact ⟨⟨_, _, _, _, firstBody, firstResult, firstHeapRep⟩, ⟨_, _, _, _, secondBody, secondResult, secondHeapRep⟩⟩

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Marker<T> {}", "impl Marker<Bool> {}",
    "trait Witness<T> {}", "impl Witness<Bool> {}",
    "trait Coerce<From, To> where From: Marker { function coerce(value: From) returns (To) where From: Witness; }",
    "impl Coerce<Bool, Word> where Bool: Marker { function coerce(value: Bool) returns (Word) where Bool: Witness { let m: mapping(Bool => Word); let first = m[value]; { let shadow: Word = first + 6; shadow; } if (value) { return first + 19; } let gap: Word; return gap; } }",
    "function covered(flag: Bool) returns (Word) where Bool: Marker, Bool: Marker, Bool: Witness { let converted: Word = flag; return converted; }",
    "function reordered(flag: Bool) returns (Word) where Bool: Witness, Bool: Marker, Bool: Marker { let converted: Word = flag; return converted; }",
    "function early() returns (Word) where Bool: Marker { let missing: Bool; let converted: Word = missing; return converted; }"
  ]}] }

private def methodAt (entry : SourceCompilerFeatureSupport.Entry) : IO (ExecutableImplMethods.CheckedMethod × SourceCompilationPlan.EvidenceEnvironment × SourceCompilationPlan.EvidenceEnvironment) := do
  let base := entry.cached.indexed.base
  let named ← match base.functions.find? (·.signature.key == entry.key) with
    | some named => pure named | none => throw (IO.userError "method caller missing")
  let caller := named.specialized
  let available ← SourceCompilerFeatureSupport.get "caller evidence"
    (SourceCompilationPlan.resolveRuntimeEvidenceEnvironment base.sourceProgram caller.key caller.assumptions)
  for item in caller.function.typedBody.nodes do
    if let .expression node := item then
      for step in node.coercions do
        let method ← SourceCompilerFeatureSupport.get "actual coercion method"
          (SourceCompilationPlan.checkedCoercionMethod base.sourceProgram caller node available step)
        let dictionary ← SourceCompilerFeatureSupport.get "actual method dictionary"
          (SourceCompilationPlan.coercionMethodRuntimeEvidence base.sourceProgram caller node step method)
        let selected ← SourceCompilerFeatureSupport.get "selected full method"
          (SourceCompilationPlan.exactSpecialization base.plan method.specialized.key)
        let emitted ← match base.functions.find? (·.signature.key == method.specialized.key) with
          | some emitted => pure emitted | none => throw (IO.userError "method native row missing")
        let trait ← match base.sourceProgram.signatures.traits.find? (·.name == "Coerce") with
          | some trait => pure trait | none => throw (IO.userError "Coerce trait missing")
        SourceCompilerFeatureSupport.require
          (selected == method.specialized && emitted.specialized == selected &&
            selected.function.typedBody.inputs.length == 1 && emitted.inputs.length == 1 &&
            trait.parameters.length == 2 && emitted.signature.parameterType == .bool && emitted.signature.resultType == .word)
          "method full record, trait type arity or runtime arity changed"
        SourceCompilerFeatureSupport.require
          (method.traitPredicates.all caller.assumptions.contains && dictionary.length == 3 &&
            dictionary[0]? == dictionary[1]? && dictionary[1]? != dictionary[2]? &&
            dictionary.map SourceCompilationPlan.runtimeEvidenceGoal == selected.assumptions)
          "covered dictionary full order/duplicates changed"
        return (method, available, dictionary)
  throw (IO.userError "caller has no actual method coercion")

private def cells (state : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) (label : String) : IO Unit :=
  SourceCompilerFeatureSupport.require (reprStr (state.heap.map fun cell => (cell.type, cell.value)) == reprStr expected)
    s!"method {label} source cell order/effects changed: {reprStr state.heap}"

private def publicFaultResume (entry : SourceCompilerFeatureSupport.Entry) (arguments : List SourceCoreExecution.Value) : IO Unit := do
  let artifact ← entry.execution.open
  let initial ← SourceCompilerFeatureSupport.boot artifact
  let completed ← SourceCompilerFeatureSupport.get "method public fault"
    (← initial.run entry.key arguments SourceCompilerFeatureSupport.executionOptions)
  let (reason, session) ← match completed with
    | .failed reason session => pure (reason, session)
    | _ => throw (IO.userError "method public outcome must fail")
  let baseline ← SourceCompilerFeatureSupport.get "method fault snapshot" (← session.snapshot 2048)
  for budget in [0, 31, 97] do
    let started ← SourceCompilerFeatureSupport.get "method suspended public call"
      (← initial.run entry.key arguments {SourceCompilerFeatureSupport.executionOptions with executionFuel := budget})
    let resumed ← match started with
      | .outOfFuel checkpoint => checkpoint.resume 300000 2048
      | outcome => pure outcome
    match resumed with
    | .failed resumed session =>
      let snapshot ← SourceCompilerFeatureSupport.get "method resumed fault snapshot" (← session.snapshot 2048)
      SourceCompilerFeatureSupport.require (resumed == reason && reprStr snapshot.cells == reprStr baseline.cells)
        "method resumed fault changed diagnostic or complete source heap"
    | _ => throw (IO.userError "method resumed call changed failure")

def run : IO Unit := do
  let program ← SourceCompilerFeatureSupport.get "method evidence checker" (checkProgram workspace 1024)
  let entry ← SourceCompilerFeatureSupport.compileNamed program "covered"
  let reordered ← SourceCompilerFeatureSupport.compileNamed program "reordered"
  let (method, caller, dictionary) ← methodAt entry
  let (otherMethod, otherCaller, otherDictionary) ← methodAt reordered
  SourceCompilerFeatureSupport.require (caller != otherCaller && caller.length == 3 && otherCaller.length == 3 &&
    dictionary == otherDictionary && method.specialized == otherMethod.specialized)
    "method evidence caller order was erased or complete selected method changed"
  let gap ← match (SourceCoreDataPlaces.declaredBinders method.specialized.function.typedBody).filter (·.name == "gap") with
    | [binder] => pure binder.id | _ => throw (IO.userError "actual method gap missing")
  let early ← SourceCompilerFeatureSupport.compileNamed program "early"
  let _ ← methodAt early
  let word (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
  for budget in [0, 31, 97, 300000] do
    for target in [entry, reordered] do
      for flag in [true, false] do
        let started ← target.audit [.bool flag] budget
        let resumed ← SourceCompilerFeatureSupport.get "method evidence native resume" (started.resume 300000)
        let priorCells : List (TypeSystem.Ty × Option SourceTypedRuntime.Value) :=
          [(.bool, some (.bool flag)), (.bool, some (.bool flag)),
           (.mapping .bool .word, some (.mapping .bool .word [])),
           (.word, some (word 0)), (.word, some (word 6))]
        match resumed.observation with
        | .done value state =>
          SourceCompilerFeatureSupport.require (flag && reprStr value == reprStr (word 19)) "method evidence success changed"
          cells state (priorCells ++ [(.word, some (word 19))]) "returned"
        | .fault (.uninitializedLocal actual) state =>
          SourceCompilerFeatureSupport.require (!flag && actual == gap) "method evidence fault changed origin"
          cells state (priorCells ++ [(.word, none)]) "fault"
        | other => throw (IO.userError s!"method evidence outcome changed: {reprStr other}")
    let started ← early.audit [] budget
    let resumed ← SourceCompilerFeatureSupport.get "method pre-call fault resume" (started.resume 300000)
    match resumed.observation with
    | .fault (.uninitializedLocal _) state => cells state [(.bool, none)] "pre-call fault"
    | other => throw (IO.userError s!"method pre-call fault changed: {reprStr other}")
  entry.checkResume [.bool true] (SourceCompilerFeatureSupport.scalar 19) 31
  reordered.checkResume [.bool true] (SourceCompilerFeatureSupport.scalar 19) 31
  publicFaultResume entry [.bool false]
  publicFaultResume reordered [.bool false]
  publicFaultResume early []
  IO.println "method evidence: distinct ordered caller dictionaries, same full compiled method, concrete lexical body, exact source cells/faults and public resume GREEN"

end Tests.SourceCoreCallableCoercionMethodEvidenceInvariant
