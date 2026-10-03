import Solcore.SourceSemantics.CoreLowering.CallableCoercionSelectedInvocation
import Solcore.Test.SourceCompilerFeatureSupport

/-! Actual emitted compiler receipts determine the complete independent body;
an arbitrary source selector and dictionary are consumed without body equality
or a universal body law. Runtime cases exercise generic parameter reordering,
full method carrier substitution, exact source faults and public resume. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreCallableCoercionSelectedInvocation
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CallableIndexedHistory SourceCoreCallableIndexedFrames
open CallableCoercionMethodEntries CallableCoercionPathMeaning
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
theorem source_step_preserves {sourceResult : Dynamic.Value} {after : Dynamic.Heap}
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
/-- A completed actual call reflects at any independently selected source body
and dictionary. Its source outcome and heap are existential, not identified by
evidence equality or by a source/native fuel comparison. -/
theorem arbitrary_selection_reflects {selectedBody : Dynamic.BodyInstance} {dictionary : Dynamic.EvidenceEnvironment}
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
  exact CallableCoercionSelectedInvocation.reflects checkedAccepted ledger emitted functions extension definitions registered
    faithful observations runtimeViews uninitialized missing member entry heaps represented selected completed

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Coerce<From, To> { function coerce(value: From) returns (To); }",
    "impl<B, A> Coerce<(A, B), Bool> { function coerce(value: (A, B)) returns (Bool) { let visited: Word = 7; return true; } }",
    "impl<B, A> Coerce<(A, B), Word> { function coerce(value: (A, B)) returns (Word) { let visited: Word = 9; let gap: Word; return gap; } }",
    "function converted(left: Word, right: Bool) returns (Bool) { let value: (Word, Bool) = (left, right); return value; }",
    "function failed(left: Word, right: Bool) returns (Word) { let value: (Word, Bool) = (left, right); return value; }",
    "function later(left: Word, right: Bool) returns (Word) { let value: (Word, Bool) = (left, right); let chosen: Bool = value; let gap: Word; return gap; }",
    "function early() returns (Bool) { let missing: Word; let value: (Word, Bool) = (missing, false); return value; }"
  ]}] }

private def inspect (entry : SourceCompilerFeatureSupport.Entry) : IO ExecutableImplMethods.CheckedMethod := do
  let base := entry.cached.indexed.base
  let caller ← match base.functions.find? (·.signature.key == entry.key) with
    | some named => pure named.specialized | none => throw (IO.userError "selected invocation caller missing")
  let available ← SourceCompilerFeatureSupport.get "selected invocation caller evidence"
    (SourceCompilationPlan.resolveRuntimeEvidenceEnvironment base.sourceProgram caller.key caller.assumptions)
  for item in caller.function.typedBody.nodes do
    if let .expression node := item then
      for step in node.coercions do
        let method ← SourceCompilerFeatureSupport.get "selected invocation actual method"
          (SourceCompilationPlan.checkedCoercionMethod base.sourceProgram caller node available step)
        let implementation ← match base.sourceProgram.signatures.implementations.filter (·.id == method.id.implementation) with
          | [value] => pure value | _ => throw (IO.userError "selected invocation implementation not unique")
        let declaration ← match implementation.methods.filter (·.id == method.id) with
          | [value] => pure value | _ => throw (IO.userError "selected invocation method not unique")
        let trait ← match base.sourceProgram.signatures.trait? declaration.traitMethod.trait with
          | some value => pure value | _ => throw (IO.userError "selected invocation trait missing")
        let retained ← match base.sourceProgram.methods.filter (·.id == method.id) with
          | [value] => pure value | _ => throw (IO.userError "selected invocation retained method not unique")
        let primary ← match caller.function.solvedRequirements.filter (·.id == step.requirement) with
          | [value] => pure value | _ => throw (IO.userError "selected invocation primary row not unique")
        let generic ← SourceCompilerFeatureSupport.get "selected invocation same checker"
          (checkFunctionBody base.sourceProgram.environment base.sourceProgram.signatures
            (implementation.functionSignatureOfMethodWithTrait trait declaration) 1024)
        let selected ← SourceCompilerFeatureSupport.get "selected invocation final plan record"
          (SourceCompilationPlan.exactSpecialization base.plan method.specialized.key)
        let dictionary ← SourceCompilerFeatureSupport.get "selected invocation method dictionary"
          (SourceCompilationPlan.coercionMethodRuntimeEvidence base.sourceProgram caller node step method)
        let substitution := method.specialized.parameterSubstitution
        SourceCompilerFeatureSupport.require
          (substitution.map Prod.fst == implementation.parameters && substitution.map Prod.snd == [.bool, .word] &&
            TypedTraitResolution.ruleParameters implementation.implRule == implementation.parameters.reverse &&
            implementation.parameters != implementation.parameters.reverse &&
            ProgramPredicate.applyParameters substitution implementation.head == primary.predicate)
          "selected invocation ordered head determination changed or became trivial"
        SourceCompilerFeatureSupport.require
          (selected == method.specialized && generic == retained.checked &&
            selected.function == SourceSpecialization.applyCheckedFunction substitution retained.checked &&
            selected.function.typedBody == StructuralSubstitution.applyTypedSource substitution retained.checked.typedBody &&
            selected.function.typedBody != retained.checked.typedBody &&
            selected.function.typedBody.owner == implementation.id &&
            selected.function.typedBody.roots == retained.checked.typedBody.roots &&
            selected.function.solvedRequirements == retained.checked.solvedRequirements.map
              (StructuralSubstitution.applySolvedRequirement substitution) &&
            selected.function.inferredBodyType == substitution.apply retained.checked.inferredBodyType &&
            selected.assumptions == (implementation.methodAssumptions trait declaration).map
              (ProgramPredicate.applyParameters substitution) &&
            dictionary.map SourceCompilationPlan.runtimeEvidenceGoal == selected.assumptions)
          "selected invocation full source body/context/result/ledger identity changed"
        return method
  throw (IO.userError "selected invocation no coercion")

private def cells (state : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) (label : String) : IO Unit :=
  SourceCompilerFeatureSupport.require (reprStr (state.heap.map fun cell => (cell.type, cell.value)) == reprStr expected)
    s!"selected invocation {label} complete ordered source heap changed: {reprStr state.heap}"

private def publicFaultResume (entry : SourceCompilerFeatureSupport.Entry) (arguments : List SourceCoreExecution.Value) : IO Unit := do
  let artifact ← entry.execution.open
  let initial ← SourceCompilerFeatureSupport.boot artifact
  let completed ← SourceCompilerFeatureSupport.get "selected invocation public fault"
    (← initial.run entry.key arguments SourceCompilerFeatureSupport.executionOptions)
  let (reason, session) ← match completed with
    | .failed reason session => pure (reason, session)
    | _ => throw (IO.userError "selected invocation public outcome must fail")
  let baseline ← SourceCompilerFeatureSupport.get "selected invocation fault snapshot" (← session.snapshot 2048)
  for budget in [0, 31, 97] do
    let started ← SourceCompilerFeatureSupport.get "selected invocation suspended public call"
      (← initial.run entry.key arguments {SourceCompilerFeatureSupport.executionOptions with executionFuel := budget})
    let resumed ← match started with
      | .outOfFuel checkpoint => checkpoint.resume 300000 2048
      | outcome => pure outcome
    match resumed with
    | .failed resumed session =>
      let snapshot ← SourceCompilerFeatureSupport.get "selected invocation resumed fault snapshot" (← session.snapshot 2048)
      SourceCompilerFeatureSupport.require (resumed == reason && reprStr snapshot.cells == reprStr baseline.cells)
        "selected invocation resumed fault changed diagnostic or complete source heap"
    | _ => throw (IO.userError "selected invocation resumed call changed failure")

def run : IO Unit := do
  let program ← SourceCompilerFeatureSupport.get "selected invocation checker" (checkProgram workspace 1024)
  let converted ← SourceCompilerFeatureSupport.compileNamed program "converted"
  let failed ← SourceCompilerFeatureSupport.compileNamed program "failed"
  let later ← SourceCompilerFeatureSupport.compileNamed program "later"
  let early ← SourceCompilerFeatureSupport.compileNamed program "early"
  let goodMethod ← inspect converted
  let badMethod ← inspect failed
  let laterMethod ← inspect later
  let _ ← inspect early
  SourceCompilerFeatureSupport.require (goodMethod.id != badMethod.id && goodMethod.specialized == laterMethod.specialized)
    "selected invocation conflated different methods or changed the same complete body"
  let methodGap ← match (SourceCoreDataPlaces.declaredBinders badMethod.specialized.function.typedBody).filter (·.name == "gap") with
    | [binder] => pure binder.id | _ => throw (IO.userError "selected invocation method gap missing")
  let word (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
  let pair : SourceTypedRuntime.Value := .product (word 8) (.bool false)
  let pairType : TypeSystem.Ty := .product .word .bool
  let prior : List (TypeSystem.Ty × Option SourceTypedRuntime.Value) :=
    [(.word, some (word 8)), (.bool, some (.bool false)), (pairType, some pair), (pairType, some pair)]
  for budget in [0, 31, 97, 300000] do
    for target in [converted, failed, later] do
      let started ← target.audit [SourceCompilerFeatureSupport.scalar 8, .bool false] budget
      let resumed ← SourceCompilerFeatureSupport.get "selected invocation resume" (started.resume 300000)
      if target.key == converted.key then
        match resumed.observation with
        | .done value state =>
          SourceCompilerFeatureSupport.require (reprStr value == reprStr (SourceTypedRuntime.Value.bool true)) "selected invocation success changed"
          cells state (prior ++ [(.word, some (word 7))]) "success"
        | other => throw (IO.userError s!"selected invocation expected success: {reprStr other}")
      else
        match resumed.observation with
        | .fault (.uninitializedLocal actual) state =>
          if target.key == failed.key then
            SourceCompilerFeatureSupport.require (actual == methodGap) "selected invocation method fault identity changed"
            cells state (prior ++ [(.word, some (word 9)), (.word, none)]) "method fault"
          else
            cells state (prior ++ [(.word, some (word 7)), (.bool, some (.bool true)), (.word, none)]) "later caller fault"
        | other => throw (IO.userError s!"selected invocation expected failure: {reprStr other}")
    let started ← early.audit [] budget
    let resumed ← SourceCompilerFeatureSupport.get "selected invocation early resume" (started.resume 300000)
    match resumed.observation with
    | .fault (.uninitializedLocal _) state => cells state [(.word, none)] "pre-method fault"
    | other => throw (IO.userError s!"selected invocation early failure changed: {reprStr other}")
  converted.checkResume [SourceCompilerFeatureSupport.scalar 8, .bool false] (.bool true) 31
  publicFaultResume failed [SourceCompilerFeatureSupport.scalar 8, .bool false]
  publicFaultResume later [SourceCompilerFeatureSupport.scalar 8, .bool false]
  publicFaultResume early []
  IO.println "selected coercion invocation: actual generic head order, full body/context/ledger, independent source selection, exact failure heaps and public resume GREEN"

end Tests.SourceCoreCallableCoercionSelectedInvocation
