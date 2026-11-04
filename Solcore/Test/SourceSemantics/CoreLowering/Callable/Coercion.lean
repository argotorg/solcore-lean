import Solcore.SourceSemantics.CoreLowering.CallableCoercionBodyProvenance
import Solcore.Test.Frontend.Source.CompilerFeatureSupport
import Solcore.SourceSemantics.CoreLowering.CallableCoercionEvidenceOrigins
import Solcore.SourceSemantics.CoreLowering.CallableCoercionExpressionMeaning
import Solcore.SourceSemantics.CoreLowering.CallableCoercionMethodBodyMeaning
import Solcore.SourceSemantics.CoreLowering.CallableCoercionMethodEvidenceInvariant
import Solcore.SourceSemantics.CoreLowering.CallableCoercionPathMeaning
import Solcore.SourceSemantics.CoreLowering.CallableCoercionPlanProvenance
import Solcore.SourceSemantics.CoreLowering.CallableCoercionPreparation
import Solcore.SourceSemantics.CoreLowering.CallableCoercionRawGroupMeaning
import Solcore.SourceSemantics.CoreLowering.CallableCoercionRawNamedCallAdmission
import Solcore.SourceSemantics.CoreLowering.CallableCoercionRawNamedCallBuiltinArguments
import Solcore.SourceSemantics.CoreLowering.CallableCoercionRawNamedCallScalarArguments
import Solcore.SourceSemantics.CoreLowering.CallableCoercionRawNamedCallMeaning
import Solcore.SourceSemantics.CoreLowering.CallableCoercionSelectedInvocation
import Solcore.SourceSemantics.CoreLowering.CallableCoercionSourcePathMeaning
import Solcore.SourceSemantics.CoreLowering.CallableCoercionSourceSelection
import Solcore.SourceSemantics.CoreLowering.CallableCoercionSpineEvaluation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedCatalogAdmission
import Solcore.Test.SourceCoreCoercionPublicCatalog
import Solcore.Test.SourceCoreCoercionPublicKeepCompilerSupport
import Solcore.Test.SourceCoreCoercionPublicCommon

/-!
# Callable coercion tests

Coerced callables: bodies, evidence, paths, plans, raw calls and spines.
-/

section
-- leanmerge: from Solcore.Test.SourceCoreCallableCoercionBodyProvenance
/-! Actual generic coercion rechecking is tied to the loaded method carrier,
then to structural source substitution. Executable checks use the public Core
boundary; they do not stand in for source coercion execution proofs. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCallableCoercionBodyProvenance
open Solcore Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CallableCoercionBodyProvenance

/-- No separate recheck equality or generic source-body premise is supplied. -/
theorem actual_method_body {loaded : LoadedProgram} {program : CheckedProgram}
    (loadedAccepted : Frontend.checkLoadedProgram loaded 1024 = .ok program)
    {caller : SourceSpecialization.SpecializedFunction} {node : ExpressionNode}
    {available : SourceTypedRuntime.RuntimeEvidenceEnvironment} {coercion : CoercionStep}
    {method : ExecutableImplMethods.CheckedMethod}
    (accepted : SourceCompilationPlan.checkedCoercionMethod program caller node available coercion = .ok method) :
    ∃ retained, retained ∈ program.methods ∧ retained.id = method.id ∧
      method.specialized.function.typedBody = StructuralSubstitution.applyTypedSource
        method.specialized.parameterSubstitution retained.checked.typedBody ∧
      method.specialized.function.solvedRequirements = retained.checked.solvedRequirements.map
        (StructuralSubstitution.applySolvedRequirement method.specialized.parameterSubstitution) := by
  obtain ⟨receipt⟩ := of_accepted (CoreLowering.CallableMethodBodyCoherence.of_loaded loadedAccepted) accepted
  exact ⟨receipt.retained, receipt.retainedMember, receipt.retainedId, receipt.body, receipt.ledger⟩

/-- Actual plan extension supplies emitted carrier identity, independently of
same-fuel loaded body checking. Neither a source call nor closure history is assumed. -/
theorem actual_emitted_body {loaded : LoadedProgram} {program : CheckedProgram}
    (loadedAccepted : Frontend.checkLoadedProgram loaded 1024 = .ok program)
    {project : CallableCoercionSpine.Projector} {context : CallableCoercionSpine.Context}
    {caller : SourceSpecialization.SpecializedFunction} {available : CallableCoercionSpine.RuntimeEvidence}
    {scope : CallableCoercionSpine.Scope} {node : ExpressionNode} {policy : SourceCoreFunctions.CallablePolicy}
    {input output : CallableCoercionSpine.Lowered} {coercion : CoercionStep} {call : CallableCoercionSpine.Call}
    (step : CallableCoercionSpine.Step program project context caller available scope node policy input coercion output call)
    {before : SourceSpecializationWorklist.Plan} {edge : SourceSpecializationWorklist.CallEdge} {budget : Nat}
    (extended : SourceSpecializationWorklist.extendCompletePlan program before step.method.specialized edge budget =
      .ok (.complete context.plan)) :
    ∃ retained, retained ∈ program.methods ∧ retained.id = step.method.id ∧
      step.specialized.function.typedBody = StructuralSubstitution.applyTypedSource
        step.specialized.parameterSubstitution retained.checked.typedBody ∧
      step.specialized.function.solvedRequirements = retained.checked.solvedRequirements.map
        (StructuralSubstitution.applySolvedRequirement step.specialized.parameterSubstitution) := by
  rw [CallableCoercionPlanProvenance.step_specialized step extended]
  exact actual_method_body loadedAccepted step.selectedMethod

/-- The retained body's context, owner and root order are tied to that same
carrier, rather than reconstructed from the specialized key. -/
theorem context_and_owner {program : CheckedProgram} {method : ExecutableImplMethods.CheckedMethod}
    (receipt : Certificate program method) :
    method.specialized.function.typedBody.owner = receipt.implementation.id ∧
    method.specialized.function.typedBody.inputs = receipt.retained.checked.typedBody.inputs.map
      (StructuralSubstitution.applyBinder method.specialized.parameterSubstitution) ∧
    method.specialized.function.typedBody.roots = receipt.retained.checked.typedBody.roots :=
  ⟨receipt.owner, receipt.inputs, receipt.roots⟩

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Marker<T> {}", "impl Marker<Word> {}",
    "trait Witness<T> {}", "impl Witness<Word> {}",
    "trait Coerce<From, To> where From: Marker { function coerce(value: From) returns (To) where From: Witness; }",
    "function hold<T>(value: T) returns (T) where T: Witness { return value; }",
    "impl<T> Coerce<T, Bool> where T: Marker { function coerce(value: T) returns (Bool) where T: Witness { let local: T = hold(value); return true; } }",
    "function converted(value: Word) returns (Bool) where Word: Marker { return value; }"
  ]}] }

private def audit (entry : SourceCompilerFeatureSupport.Entry) : IO Unit := do
  let program := entry.cached.indexed.base.sourceProgram
  let mut observed := false
  for named in entry.cached.indexed.base.functions do
    if named.signature.key == entry.key then
      let caller := named.specialized
      let available ← SourceCompilerFeatureSupport.get "caller resolver"
        (SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions)
      for item in caller.function.typedBody.nodes do
        match item with
        | .expression node =>
          for step in node.coercions do
            let method ← SourceCompilerFeatureSupport.get "actual coercion selector"
              (SourceCompilationPlan.checkedCoercionMethod program caller node available step)
            let implementation ← match program.signatures.implementations.filter (·.id == method.id.implementation) with
              | [value] => pure value | _ => throw (IO.userError "implementation singleton missing")
            let declaration ← match implementation.methods.filter (·.id == method.id) with
              | [value] => pure value | _ => throw (IO.userError "method singleton missing")
            let trait ← match program.signatures.trait? declaration.traitMethod.trait with
              | some value => pure value | _ => throw (IO.userError "trait missing")
            let retained ← match program.methods.filter (·.id == method.id) with
              | [value] => pure value | _ => throw (IO.userError "retained generic method missing")
            let generic ← SourceCompilerFeatureSupport.get "same-fuel complete recheck"
              (checkFunctionBody program.environment program.signatures
                (implementation.functionSignatureOfMethodWithTrait trait declaration) 1024)
            SourceCompilerFeatureSupport.require (generic == retained.checked)
              "same-fuel full checker carrier changed"
            let substitution := method.specialized.parameterSubstitution
            SourceCompilerFeatureSupport.require (substitution.length == 1 && substitution.map Prod.snd == [.word])
              "generic method was not actually specialized"
            SourceCompilerFeatureSupport.require
              (method.checked == method.specialized.function && method.specialized.function == SourceSpecialization.applyCheckedFunction substitution retained.checked)
              "complete specialized carrier differs from retained application"
            SourceCompilerFeatureSupport.require
              (method.specialized.function.typedBody == StructuralSubstitution.applyTypedSource substitution retained.checked.typedBody &&
                !(method.specialized.function.typedBody == retained.checked.typedBody))
              "independent structural source substitution was trivial or changed"
            SourceCompilerFeatureSupport.require
              (!retained.checked.solvedRequirements.isEmpty &&
                method.specialized.function.solvedRequirements == retained.checked.solvedRequirements.map
                  (StructuralSubstitution.applySolvedRequirement substitution))
              "ordered generic evidence substitution changed"
            SourceCompilerFeatureSupport.require
              (method.specialized.assumptions == (implementation.methodAssumptions trait declaration).map (ProgramPredicate.applyParameters substitution) &&
                method.specialized.function.typedBody.owner == implementation.id &&
                method.specialized.function.typedBody.roots == retained.checked.typedBody.roots)
              "synthetic context/owner/roots changed"
            let emitted ← SourceCompilerFeatureSupport.get "plan selected method"
              (SourceCompilationPlan.exactSpecialization entry.cached.indexed.base.plan method.specialized.key)
            SourceCompilerFeatureSupport.require (emitted == method.specialized) "emitter selected another complete method carrier"
            observed := true
        | _ => pure ()
  SourceCompilerFeatureSupport.require observed "coercion not reached"

def run : IO Unit := do
  let program ← SourceCompilerFeatureSupport.get "checker" (Frontend.checkProgram workspace 1024)
  let entry ← SourceCompilerFeatureSupport.compileNamed program "converted"
  audit entry
  entry.checkResume [SourceCompilerFeatureSupport.scalar 9] (.bool true) 7
  SourceCompilerFeatureSupport.require ((← entry.run [SourceCompilerFeatureSupport.scalar 0]) == .bool true)
    "specialized method execution changed"
  IO.println "coercion body provenance: same-fuel retained carrier, generic source/context/evidence substitution, plan identity and resume GREEN"

end Tests.SourceCoreCallableCoercionBodyProvenance
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableCoercionEvidenceOrigins
/-! Actual selector/materializer receipts supply independent dictionary origin.
Tests retain first-match behavior, repeated goals, source order and the explicit
caller-covered profile; source method execution is not asserted here. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreCallableCoercionEvidenceOrigins
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CallableNamedMetadata (evidence environment)
open CallableCoercionMethodCertificates (Dictionary)
open CallableCoercionEvidenceOrigins

/-- The consumer starts from actual compiler actions, with no dictionary-origin
or body-meaning premise. The complete selected roots are returned. -/
theorem accepted_origins {program : CheckedProgram} {caller : SourceSpecialization.SpecializedFunction}
    {node : ExpressionNode} {available dictionary : Dictionary} {step : CoercionStep}
    {method : ExecutableImplMethods.CheckedMethod} {context : SourceSemantics.Context}
    (selected : SourceCompilationPlan.checkedCoercionMethod program caller node available step = .ok method)
    (resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions = .ok available)
    (materialized : SourceCompilationPlan.coercionMethodRuntimeEvidence program caller node step method = .ok dictionary)
    (covered : CallerCovered caller method)
    (signatures : context.signatures = program.signatures) (assumptions : context.assumptions = method.specialized.assumptions) :
    ∃ receipt : CallableCoercionMethodCertificates.Certificate program caller node available step method,
      Dynamic.EvidenceEnvironment.AssembledFrom (environment available)
        (evidence receipt.primary :: receipt.methodEvidence.map evidence) method.specialized.assumptions (environment dictionary) ∧
      (environment dictionary).Valid program.signatures.resolutionRules ∧
      (environment dictionary).Covers context ∧ dictionary.length = method.specialized.assumptions.length := by
  obtain ⟨receipt⟩ := CallableCoercionMethodCertificates.of_accepted selected
  obtain ⟨origins, valid, _⟩ := Certificate.origins receipt covered resolved materialized
  exact ⟨receipt, origins, valid, Certificate.covers receipt covered resolved materialized signatures assumptions,
    by simpa only [environment, List.length_map] using origins.length_eq⟩

theorem empty_headers {program : CheckedProgram} {caller : SourceSpecialization.SpecializedFunction}
    {node : ExpressionNode} {available dictionary : Dictionary} {step : CoercionStep}
    {method : ExecutableImplMethods.CheckedMethod}
    (selected : SourceCompilationPlan.checkedCoercionMethod program caller node available step = .ok method)
    (resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions = .ok available)
    (materialized : SourceCompilationPlan.coercionMethodRuntimeEvidence program caller node step method = .ok dictionary)
    (empty : method.traitPredicates = []) :
    ∃ receipt : CallableCoercionMethodCertificates.Certificate program caller node available step method,
      Dynamic.EvidenceEnvironment.AssembledFrom (environment available)
        (evidence receipt.primary :: receipt.methodEvidence.map evidence) method.specialized.assumptions (environment dictionary) := by
  obtain ⟨receipt⟩ := CallableCoercionMethodCertificates.of_accepted selected
  exact ⟨receipt, (Certificate.origins receipt (by simp [CallerCovered, empty]) resolved materialized).1⟩

private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def wordGoal : ProgramPredicate := ProgramSignatures.builtinIntWordRule.head
private def integerGoal : ProgramPredicate := ProgramSignatures.builtinIntIntegerRule.head
private def wordEvidence : TypedTraitResolution.Evidence := .byImpl wordGoal (.builtin .intWord) []
private def integerEvidence : TypedTraitResolution.Evidence := .byImpl integerGoal (.builtin .intInteger) []

theorem repeated_ordered_lookup (program : CheckedProgram) (key : SourceCompilationPlan.Key) :
    let program := { program with signatures := signatures }
    SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program key [wordGoal, integerGoal, wordGoal] =
      .ok [wordEvidence, integerEvidence, wordEvidence] ∧
    (environment [wordEvidence, integerEvidence, wordEvidence]).LooksUp wordGoal (evidence wordEvidence) ∧
    (environment [wordEvidence, integerEvidence, wordEvidence]).LooksUp integerGoal (evidence integerEvidence) := by
  dsimp only
  have accepted : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment { program with signatures := signatures }
      key [wordGoal, integerGoal, wordGoal] = .ok [wordEvidence, integerEvidence, wordEvidence] := rfl
  have resolved := caller_resolved accepted
  exact ⟨accepted, resolved.lookup (by simp) rfl, resolved.lookup (by simp) rfl⟩

/-- Equal goals alone cannot supply the fresh resolver tree from an arbitrary
caller. The actual caller resolver premise is essential. -/
theorem wrong_first_tree_rejected :
    ¬ (environment [.byImpl wordGoal (.builtin .intInteger) [], wordEvidence]).LooksUp wordGoal (evidence wordEvidence) := by
  intro found
  have first : (environment [.byImpl wordGoal (.builtin .intInteger) [], wordEvidence]).LooksUp
      wordGoal (evidence (.byImpl wordGoal (.builtin .intInteger) [])) := .head
  have same := first.functional found
  simp only [evidence, wordEvidence, List.map_nil] at same
  cases same

theorem nonempty_header_profile (seed : SourceSpecialization.SpecializedFunction)
    (method : ExecutableImplMethods.CheckedMethod) :
    CallerCovered {seed with assumptions := [wordGoal, integerGoal, wordGoal]}
      {method with traitPredicates := [integerGoal, wordGoal, integerGoal]} ∧
    ¬ CallerCovered {seed with assumptions := []} {method with traitPredicates := [wordGoal]} := by
  simp [CallerCovered]

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Marker<T> {}",
    "impl Marker<Bool> {}",
    "trait Witness<T> {}",
    "impl Witness<Bool> {}",
    "trait Coerce<From, To> where From: Marker { function coerce(value: From) returns (To) where From: Witness; }",
    "impl Coerce<Bool, Word> where Bool: Marker { function coerce(value: Bool) returns (Word) where Bool: Witness { return value ? 17 : 4; } }",
    "function covered(flag: Bool) returns (Word) where Bool: Marker { return flag; }",
    "function repeated(flag: Bool) returns (Word) where Bool: Marker, Bool: Marker { return flag; }",
    "function uncovered(flag: Bool) returns (Word) { return flag; }"
  ]}] }

private def audit (entry : SourceCompilerFeatureSupport.Entry) (expectCovered : Bool) : IO Unit := do
  let base := entry.cached.indexed.base
  let mut observed := false
  for named in base.functions do
    if named.signature.key == entry.key then
      let caller := named.specialized
      let available ← SourceCompilerFeatureSupport.get "caller resolver"
        (SourceCompilationPlan.resolveRuntimeEvidenceEnvironment base.sourceProgram caller.key caller.assumptions)
      for item in caller.function.typedBody.nodes do
        match item with
        | .expression node =>
          for step in node.coercions do
            let method ← SourceCompilerFeatureSupport.get "actual coercion selector"
              (SourceCompilationPlan.checkedCoercionMethod base.sourceProgram caller node available step)
            let dictionary ← SourceCompilerFeatureSupport.get "actual method dictionary"
              (SourceCompilationPlan.coercionMethodRuntimeEvidence base.sourceProgram caller node step method)
            let headers ← SourceCompilerFeatureSupport.get "fresh header resolver"
              (SourceCompilationPlan.resolveRuntimeEvidenceEnvironment base.sourceProgram method.specialized.key method.traitPredicates)
            SourceCompilerFeatureSupport.require (!headers.isEmpty &&
              dictionary == headers ++ method.implementationPremises ++ method.methodPremises &&
              dictionary.map SourceCompilationPlan.runtimeEvidenceGoal == method.specialized.assumptions)
              "ordered header/implementation/method dictionary changed"
            let covered := method.traitPredicates.all caller.assumptions.contains
            SourceCompilerFeatureSupport.require (covered == expectCovered) "caller-covered profile changed"
            if covered then
              for fresh in headers do
                let found := available.find? fun item =>
                  SourceCompilationPlan.runtimeEvidenceGoal item == SourceCompilationPlan.runtimeEvidenceGoal fresh
                SourceCompilerFeatureSupport.require (found == some fresh) "fresh full tree differs from caller first match"
            observed := true
        | _ => pure ()
  SourceCompilerFeatureSupport.require observed "actual coercion selector was not reached"

def run : IO Unit := do
  let program ← SourceCompilerFeatureSupport.get "coercion origin checker" (checkProgram workspace)
  for name in ["covered", "repeated", "uncovered"] do
    let entry ← SourceCompilerFeatureSupport.compileNamed program name
    audit entry (name != "uncovered")
    entry.checkResume [.bool true] (SourceCompilerFeatureSupport.scalar 17) 7
    SourceCompilerFeatureSupport.require ((← entry.run [.bool false]) == SourceCompilerFeatureSupport.scalar 4)
      "false branch result changed"
  IO.println "coercion origins: actual selection, caller-covered headers, duplicates, dictionary order and resume GREEN"

end Tests.SourceCoreCallableCoercionEvidenceOrigins
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableCoercionExpressions
/-! Actual outer acceptance retains raw arguments, selected slots and emitted
suffixes. The formal consumers keep the original raw-form laws explicit; they
do not claim recursive expression meaning. Runtime checks cover real delegated
and direct output coercions, ordered effects and resumed fault prefixes. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
namespace Tests.SourceCoreCallableCoercionExpressions
open Solcore SourceSemantics SourceSemantics.CoreLowering Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CallableIndexedHistory
open SourceCoreCallableIndexedFrames CallableCoercionMethodEntries CallableCoercionPathMeaning
open CallableCoercionExpressionCertificates CallableCoercionExpressionMeaning

section Receipt
variable {program : CheckedProgram} {project : Projector} {callerFunction : Specialized}
  {compilation : SourceCoreFunctions.Context} {child : SourceCoreEvidence.Child} {fuel : Nat}
  {source : TypedSource} {scope : Scope} {id callee : ExpressionId} {arguments : List ExpressionId}
  {instantiation : DeclarationInstantiation} {reasonAt : ExpressionId → Word}
  {policy : SourceCoreFunctions.CallablePolicy} {node : ExpressionNode} {output : Lowered}

theorem direct_result_from_outer
    (found : source.lookupExpression? id = some node)
    (form : node.form = .call callee arguments (.declaration instantiation))
    (accepted : SourceCoreEvidence.lowerWithProjector program project callerFunction compilation child fuel source scope id reasonAt policy = .ok (some output)) :
    ∃ receipt : Direct program project callerFunction compilation child fuel source scope id callee arguments instantiation reasonAt policy node output,
      CallableNamedMetadata.Matches receipt.selection.specialized instantiation ∧
      arguments.mapM (fun argument => child fuel source scope argument reasonAt) = .ok receipt.loweredArguments ∧
      compilation.globals.zipIdx.filter (fun row => decide (row.1.key = receipt.selection.key)) = [(receipt.native.signature, receipt.native.index)] ∧
      receipt.operand = ⟨receipt.native.signature.resultType, SourceCoreCalls.call receipt.native.signature
        (scope.length + compilation.administrativePrefix + receipt.native.index)
        (SourceCoreCalls.packArguments receipt.loweredArguments).expression compilation.internalReason⟩ := by
  obtain ⟨receipt⟩ := CallableCoercionExpressionCertificates.direct_of_accepted found form accepted
  exact ⟨receipt, receipt.selection.metadata, receipt.argumentsAccepted, receipt.native.global, receipt.native.emitted⟩

theorem delegated_result_from_outer {ordinary : List RequirementId}
    (found : source.lookupExpression? id = some node)
    (ordinaryAccepted : SourceCompilationPlan.ordinaryOwnedRequirements? node = some ordinary)
    (delegates : Delegates node ordinary)
    (accepted : SourceCoreEvidence.lowerWithProjector program project callerFunction compilation child fuel source scope id reasonAt policy = .ok (some output)) :
    ∃ receipt : Delegated program project callerFunction compilation child fuel source scope id reasonAt policy node output,
      child fuel (SourceCoreEvidence.withNode source (rawNode node receipt.ordinary)) scope id reasonAt = .ok receipt.operand ∧
      SourceCoreEvidence.applyCoercions program project compilation callerFunction receipt.available scope node policy receipt.operand node.coercions = .ok output := by
  obtain ⟨receipt⟩ := CallableCoercionExpressionCertificates.delegated_of_accepted found ordinaryAccepted delegates accepted
  exact ⟨receipt, receipt.childAccepted, receipt.suffix.accepted⟩
end Receipt

section Meaning
variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
  {values : ValuesContext} {compilerProgram : CheckedProgram}
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {source : TypedSource} {environment : Dynamic.Environment} {before : Dynamic.Heap}
  {caller : Environment} {mapping : LocationMap} {world : StoreTyping} {store : Store}
  {node : ExpressionNode} {ξ : Renaming} {operand : Lowered}

variable {raw : Workspace.RawWorkspace} {checkFuel : Nat}
  (checkedAccepted : checkProgram raw checkFuel = .ok compilerProgram)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (definitions : prepared.layouts.definitions = ambient.definitions)
  (registered : prepared.ancestry.layout.frame.Registered ambient.definitions)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  {methods : Profiles (prepared := prepared) (values := values) (program := Program.ofChecked compilerProgram)
    (context := context) (evidence := evidence)}
  (uninitialized : ∀ method ∈ methods, ∀ id location, faults (.uninitializedLocation location) (method.diagnostics.reasonAt method.named.signature.key id))
  (missing : ∀ method ∈ methods, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((method.diagnostics.reasonAt method.named.signature.key id).add tag))
  {project : Projector} {compilation : SourceCoreFunctions.Context} {callerFunction : Specialized} {available : Available}
  {scope : Scope} {id : ExpressionId} {child : SourceCoreEvidence.Child} {fuel : Nat}
  {reasonAt : ExpressionId → Word} {policy : SourceCoreFunctions.CallablePolicy} {output : Lowered}
  {calls : List CallableCoercionSpine.Call}
  {callee : ExpressionId} {arguments : List ExpressionId} {instantiation : DeclarationInstantiation}
  (receipt : Direct compilerProgram project callerFunction compilation child fuel source scope id callee arguments instantiation reasonAt policy node output)
  (emitted : Emitted compilerProgram project compilation callerFunction receipt.available scope node policy ξ receipt.operand methods output calls)
  (steps : methods.map (·.step) = node.coercions)
  (chain : Chain node.rawType receipt.operand.type methods node.type output.type)
  (ledger : context.solvedRequirements = callerFunction.function.solvedRequirements)
  (entry : Entry methods ambient.definitions caller mapping world before store)

include checkedAccepted extension definitions registered faithful observations runtimeViews uninitialized missing ledger emitted steps chain entry in
/-- Preserve an independent whole source outcome with its original raw form and
ordered coercions. The raw law is the remaining expression-grammar interface. -/
theorem direct_expression_preserves
    (unique : NodeOccurrencesUnique source)
    (rawMeaning : RawFormPreserves (compilerProgram := compilerProgram) (context := context) (evidence := evidence) (registry := registry)
      functions faults source environment before caller mapping world store node ξ receipt.operand)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : Dynamic.ExpressionEvaluatesOutcome (Program.ofChecked compilerProgram) context evidence source environment before id outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates caller store (output.expression.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        node.type output.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry methods ambient.definitions caller finalMap finalWorld after finalStore) := by
  exact CallableCoercionExpressionMeaning.preserves functions checkedAccepted extension definitions registered faithful observations runtimeViews
    uninitialized missing receipt.toOutput emitted steps chain ledger entry unique (by intros; simp [receipt.form]) rawMeaning trace

include extension definitions registered faithful observations runtimeViews uninitialized missing emitted steps chain entry in
/-- Reflect only finite completion of the real emitted expression. The source
form and path derivations retain their separate heaps and independent costs. -/
theorem direct_expression_reflects
    (rawMeaning : RawFormReflects (compilerProgram := compilerProgram) (context := context) (evidence := evidence) (registry := registry)
      functions faults source environment before caller mapping world store node ξ receipt.operand)
    {value : Value} {finalStore : Store}
    (completed : Evaluates caller store (output.expression.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome (Program.ofChecked compilerProgram) context evidence source environment before id outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        node.type output.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry methods ambient.definitions caller finalMap finalWorld after finalStore) := by
  exact CallableCoercionExpressionMeaning.reflects functions extension definitions registered faithful observations runtimeViews
    uninitialized missing receipt.toOutput emitted steps chain entry rawMeaning completed

end Meaning

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Box { Box(Bool) }", "enum Final { Final(Box) }", "enum Broken { Broken(Box) }",
    "trait Marker<T> {}", "impl Marker<Word> {}", "impl Marker<Bool> {}", "impl Marker<Box> {}",
    "trait Witness<T> {}", "impl Witness<Word> {}", "impl Witness<Bool> {}", "impl Witness<Box> {}",
    "trait Coerce<From, To> where From: Marker { function coerce(value: From) returns (To) where From: Witness; }",
    "impl Coerce<Word, Bool> where Word: Marker { function coerce(value: Word) returns (Bool) where Word: Witness { let saved: Word = value; if (value == 0) { let firstGap: Bool; return firstGap; } return value == 1; } }",
    "impl Coerce<Bool, Box> where Bool: Marker { function coerce(value: Bool) returns (Box) where Bool: Witness { let m: mapping(Bool => Word); let touched = m[value]; if (value) { return Box(value); } let secondGap: Box; return secondGap; } }",
    "impl Coerce<Box, Final> where Box: Marker { function coerce(value: Box) returns (Final) where Box: Witness { let reached: Word = 31; return Final(value); } }",
    "impl Coerce<Box, Broken> where Box: Marker { function coerce(value: Box) returns (Broken) where Box: Witness { let reached: Word = 37; let lastGap: Broken; return lastGap; } }",
    "function identity(value: Word) returns (Word) { let rawEffect: Word = 19; return value; }",
    "function rawFail() returns (Word) { let rawEffect: Word = 23; let rawGap: Word; return rawGap; }",
    "function direct(value: Word) returns (Final) where Word: Marker, Bool: Marker, Box: Marker { let result: Final = identity(value); return result; }",
    "function emptySelected(value: Word) returns (Word) where Word: Marker { return identity(value); }",
    "function bypass(value: Word) returns (Word) { return identity(value); }",
    "function path(value: Word) returns (Final) where Word: Marker, Word: Marker, Bool: Marker, Box: Marker { let result: Final = value + 0; return result; }",
    "function late(value: Word) returns (Broken) where Word: Marker, Bool: Marker, Box: Marker { let result: Broken = value + 0; return result; }",
    "function early() returns (Final) where Word: Marker, Bool: Marker, Box: Marker { let result: Final = rawFail(); return result; }",
    "function empty(value: Word) returns (Word) { return value; }"
  ]}] }

private def word (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def cells (state : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) (label : String) : IO Unit :=
  SourceCompilerFeatureSupport.require (reprStr (state.heap.map fun cell => (cell.type, cell.value)) == reprStr expected)
    s!"path {label} ordered source cells changed: {reprStr state.heap}"

/-- Inspect the real retained three-edge list and replay the actual compiler
helper against the sealed plan. This also checks each full dictionary in order. -/
private def constructorFor (program : CheckedProgram) (name : String) : IO DataConstructorInstantiation := do
  let data ← match program.signatures.dataTypes.find? (·.name == name) with
    | some data => pure data | none => throw (IO.userError s!"source path {name} missing")
  match data.constructors with
  | [constructor] => pure (DataConstructorInstantiation.mk constructor.id [] constructor.payloadTypes (.nominal data.id []))
  | _ => throw (IO.userError s!"source path {name} constructor missing")

private def audit (entry : SourceCompilerFeatureSupport.Entry) (targetName : String) :
    IO (DataConstructorInstantiation × DataConstructorInstantiation × List Resolved.LocalId) := do
  let base := entry.cached.indexed.base
  let named ← match base.functions.find? (·.signature.key == entry.key) with
    | some named => pure named | none => throw (IO.userError "source path caller missing")
  let caller := named.specialized
  let available ← SourceCompilerFeatureSupport.get "source path caller evidence"
    (SourceCompilationPlan.resolveRuntimeEvidenceEnvironment base.sourceProgram caller.key caller.assumptions)
  let constructor ← constructorFor base.sourceProgram "Box"
  let target ← constructorFor base.sourceProgram targetName
  let mut gaps : List Resolved.LocalId := []
  let mut found := false
  for item in caller.function.typedBody.nodes do
    if let .expression node := item then
      if !node.coercions.isEmpty then
        SourceCompilerFeatureSupport.require (node.coercions.length == 3) "actual coercion path lost its three edges"
        let mut goals : List TypeSystem.Ty := []
        for step in node.coercions do
          let method ← SourceCompilerFeatureSupport.get "path method"
            (SourceCompilationPlan.checkedCoercionMethod base.sourceProgram caller node available step)
          let dictionary ← SourceCompilerFeatureSupport.get "path dictionary"
            (SourceCompilationPlan.coercionMethodRuntimeEvidence base.sourceProgram caller node step method)
          let key ← SourceCompilerFeatureSupport.get "path edge"
            (SourceCompilationPlan.exactCallKey base.plan named.signature.key node.id method.specialized.key)
          let selected ← SourceCompilerFeatureSupport.get "path full selected record"
            (SourceCompilationPlan.exactSpecialization base.plan key)
          let emitted ← match base.functions.find? (·.signature.key == key) with
            | some emitted => pure emitted | none => throw (IO.userError "path native row missing")
          SourceCompilerFeatureSupport.require (selected == method.specialized && emitted.specialized == selected &&
            emitted.inputs.length == 1 && dictionary.length == 3 && dictionary[0]? == dictionary[1]? &&
            dictionary[1]? != dictionary[2]? && dictionary.map SourceCompilationPlan.runtimeEvidenceGoal == selected.assumptions &&
            method.traitPredicates.all caller.assumptions.contains)
            "path full record / ordered repeated dictionary / caller coverage changed"
          goals := goals ++ [step.source, step.target]
          let declared := (SourceCoreDataPlaces.declaredBinders selected.function.typedBody).filter
            (fun binder => binder.name == "firstGap" || binder.name == "secondGap" || binder.name == "lastGap")
          match declared with
          | [binder] => gaps := gaps ++ [binder.id]
          | [] =>
            SourceCompilerFeatureSupport.require (step.target == target.resultType && targetName == "Final")
              "only successful terminal method may lack a gap"
          | _ => throw (IO.userError "source path ambiguous method gap")
        SourceCompilerFeatureSupport.require (goals == [.word, .bool, .bool, constructor.resultType, constructor.resultType, target.resultType])
          "path raw endpoint order changed"
        let compilation : SourceCoreFunctions.Context := {
          plan := base.plan, owner := named.signature.key, globals := base.globals, administrativePrefix := 1,
          solvedRequirements := caller.function.solvedRequirements, internalReason := Word.zero }
        let indexed := entry.cached.indexed
        let representation := (SourceCoreCallableIndexedPrograms.markedRepresentation indexed.ancestry indexed.fuel indexed.layouts).atContext named.signature.key []
        let diagnostics ← match base.diagnostics with
          | some diagnostics => pure diagnostics.program
          | none => throw (IO.userError "outer diagnostics missing")
        let diagnostics := match base.callableContext with
          | some native => {diagnostics with rootTable := native.diagnostics.rootTable}
          | none => diagnostics
        let own ← match diagnostics.base.find? named.signature.key with
          | some own => pure own | none => throw (IO.userError "outer caller diagnostics missing")
        let source := caller.function.typedBody
        let scope := named.inputs.reverse.map (fun (binder, type) => (binder.id, type))
        let reasonAt := diagnostics.reasonAt named.signature.key
        let child := SourceCoreGeneralFunctions.lowerContextualExpression base.sourceProgram representation base.sourceProgram.signatures
          base.locals base.contexts own.assignments diagnostics compilation base.callableContext none none
        let policy := SourceCoreGeneralFunctions.callablePolicy base.callableContext []
        let result ← SourceCompilerFeatureSupport.get "actual outer lowerWithProjector"
          (SourceCoreEvidence.lowerWithProjector base.sourceProgram representation.expressions.projectType caller compilation child
            150 source scope node.id reasonAt policy)
        let lowered ← match result with
          | some lowered => pure lowered | none => throw (IO.userError "coerced outer delegated unexpectedly")
        let raw ← match node.form with
          | .group _ | .binary .. =>
            let ordinary ← match SourceCompilationPlan.ordinaryOwnedRequirements? node with
              | some ordinary => pure ordinary | none => throw (IO.userError "outer raw ordinary requirements absent")
            SourceCompilerFeatureSupport.get "actual sanitized delegated child"
              (child 150 (SourceCoreEvidence.withNode source (CallableCoercionExpressionCertificates.rawNode node ordinary)) scope node.id reasonAt)
          | .call callee arguments (.declaration instantiation) => do
            discard <| SourceCompilerFeatureSupport.get "actual callee metadata"
              (SourceCompilationPlan.validateDirectDeclarationCallee source node.id callee instantiation)
            let dictionary ← SourceCompilerFeatureSupport.get "actual direct dictionary"
              (SourceCompilationPlan.exactDirectCallRuntimeEvidence caller node available instantiation)
            let target ← SourceCompilerFeatureSupport.get "actual direct target"
              (SourceCompilationPlan.exactInstantiationKey base.plan instantiation)
            let key ← SourceCompilerFeatureSupport.get "actual direct edge"
              (SourceCompilationPlan.exactCallKey base.plan compilation.owner node.id target)
            let selected ← SourceCompilerFeatureSupport.get "actual direct full record"
              (SourceCompilationPlan.exactSpecialization base.plan key)
            discard <| SourceCompilerFeatureSupport.get "actual direct authentication"
              (SourceCompilationPlan.validateAuthenticatedRuntimeEvidence base.sourceProgram.signatures key selected.assumptions dictionary)
            let (signature, index) ← match base.globals.zipIdx.filter (fun row => decide (row.1.key = key)) with
              | [row] => pure row | _ => throw (IO.userError "actual direct global is not singleton")
            let loweredArgs ← SourceCompilerFeatureSupport.get "actual ordered direct children"
              (arguments.mapM (fun argument => child 150 source scope argument reasonAt))
            let packed := SourceCoreCalls.packArguments loweredArgs
            SourceCompilerFeatureSupport.require (signature.parameterType == packed.type &&
              arguments.length == selected.function.typedBody.inputs.length) "actual direct arity changed"
            pure ⟨signature.resultType, SourceCoreCalls.call signature (scope.length + compilation.administrativePrefix + index)
              packed.expression compilation.internalReason⟩
          | _ => throw (IO.userError s!"outer test unhandled raw form: {reprStr node.form}")
        let replayed ← SourceCompilerFeatureSupport.get "outer same applyCoercions suffix"
          (SourceCoreEvidence.applyCoercions base.sourceProgram representation.expressions.projectType compilation caller available
            scope node policy raw node.coercions)
        SourceCompilerFeatureSupport.require (replayed == lowered) "outer actual operand/suffix code changed"
        let outputType ← SourceCompilerFeatureSupport.get "outer result projection"
          (entry.cached.compatible.checked.catalog.project target.resultType)
        let nativeContext := scope.map (fun row => OptionalCell.referenceType row.2) ++
          .unit :: (base.globals.map SourceCoreCalls.Signature.referenceType ++ [.cell indexed.ancestry.layout.frame.type])
        SourceCompilerFeatureSupport.require (lowered.type == outputType &&
          Core.infer? nativeContext lowered.expression indexed.layouts.definitions == some (LanguageResult.resultType outputType))
          "outer actual native code/ordered globals type mismatch"
        found := true
  SourceCompilerFeatureSupport.require found "actual two-step path not reached"
  SourceCompilerFeatureSupport.require (gaps.length == (if targetName == "Final" then 2 else 3))
    "source path method fault positions changed"
  pure (constructor, target, gaps)

private def faultResume (entry : SourceCompilerFeatureSupport.Entry) (arguments : List SourceCoreExecution.Value) : IO Unit := do
  let artifact ← entry.execution.open
  let initial ← SourceCompilerFeatureSupport.boot artifact
  let finished ← SourceCompilerFeatureSupport.get "path public fault"
    (← initial.run entry.key arguments SourceCompilerFeatureSupport.executionOptions)
  let (fault, session) ← match finished with
    | .failed fault session => pure (fault, session)
    | _ => throw (IO.userError "path expected public fault")
  let expected ← SourceCompilerFeatureSupport.get "path fault snapshot" (← session.snapshot 2048)
  for budget in [0, 41, 137] do
    let started ← SourceCompilerFeatureSupport.get "path suspend"
      (← initial.run entry.key arguments {SourceCompilerFeatureSupport.executionOptions with executionFuel := budget})
    let resumed ← match started with
      | .outOfFuel checkpoint => checkpoint.resume 500000 2048
      | outcome => pure outcome
    match resumed with
    | .failed observed session =>
      let snapshot ← SourceCompilerFeatureSupport.get "path resumed snapshot" (← session.snapshot 2048)
      SourceCompilerFeatureSupport.require (observed == fault && reprStr snapshot.cells == reprStr expected.cells)
        "path failure reason or complete source store changed on resume"
    | _ => throw (IO.userError "path failure resume changed outcome")

private def auditBypass (entry : SourceCompilerFeatureSupport.Entry) : IO Unit := do
  let base := entry.cached.indexed.base
  let named ← match base.functions.find? (·.signature.key == entry.key) with
    | some named => pure named | none => throw (IO.userError "bypass caller missing")
  let compilation : SourceCoreFunctions.Context := {
    plan := base.plan, owner := named.signature.key, globals := base.globals, administrativePrefix := 1,
    solvedRequirements := named.specialized.function.solvedRequirements, internalReason := Word.zero }
  let mut count := 0
  for item in named.specialized.function.typedBody.nodes do
    if let .expression node := item then
      if let .call _ _ (.declaration _) := node.form then
        let actual := SourceCoreEvidence.lowerWithProjector base.sourceProgram SourceCoreFunctionTypes.projectType named.specialized
          compilation (fun _ _ _ id _ => .error (.missingExpression id)) 100 named.specialized.function.typedBody [] node.id (fun _ => Word.zero)
        SourceCompilerFeatureSupport.require (node.coercions.isEmpty && node.requirements.isEmpty && (match actual with | .ok none => true | _ => false))
          "empty evidence path must bypass before calling even a rejecting child"
        count := count + 1
  SourceCompilerFeatureSupport.require (count == 1) "bypass actual direct occurrence missing"

private def auditSelectedEmpty (entry : SourceCompilerFeatureSupport.Entry) : IO Unit := do
  let base := entry.cached.indexed.base
  let named ← match base.functions.find? (·.signature.key == entry.key) with
    | some named => pure named | none => throw (IO.userError "empty selected caller missing")
  let compilation : SourceCoreFunctions.Context := {
    plan := base.plan, owner := named.signature.key, globals := base.globals, administrativePrefix := 1,
    solvedRequirements := named.specialized.function.solvedRequirements, internalReason := Word.zero }
  let source := named.specialized.function.typedBody
  let scope := named.inputs.reverse.map (fun (binder, type) => (binder.id, type))
  let child : SourceCoreEvidence.Child := fun fuel source scope id reasonAt => SourceCoreBasic.lowerExpression fuel source scope id (reasonAt id)
  let mut count := 0
  for item in source.nodes do
    if let .expression node := item then
      if let .call _ arguments (.declaration instantiation) := node.form then
        let result ← SourceCompilerFeatureSupport.get "empty selected actual outer"
          (SourceCoreEvidence.lowerWithProjector base.sourceProgram SourceCoreFunctionTypes.projectType named.specialized
            compilation child 100 source scope node.id (fun _ => Word.zero))
        let lowered ← match result with
          | some lowered => pure lowered | none => throw (IO.userError "caller-owned empty suffix lost its authentication")
        let target ← SourceCompilerFeatureSupport.get "empty selected target"
          (SourceCompilationPlan.exactInstantiationKey base.plan instantiation)
        let key ← SourceCompilerFeatureSupport.get "empty selected edge"
          (SourceCompilationPlan.exactCallKey base.plan compilation.owner node.id target)
        let (signature, index) ← match base.globals.zipIdx.filter (fun row => decide (row.1.key = key)) with
          | [row] => pure row | _ => throw (IO.userError "empty selected globals changed")
        let args ← SourceCompilerFeatureSupport.get "empty selected ordered args"
          (arguments.mapM (fun id => child 100 source scope id (fun _ => Word.zero)))
        SourceCompilerFeatureSupport.require (node.coercions.isEmpty && !named.specialized.assumptions.isEmpty &&
          lowered.type == signature.resultType && lowered.expression == SourceCoreCalls.call signature
            (scope.length + compilation.administrativePrefix + index) (SourceCoreCalls.packArguments args).expression compilation.internalReason)
          "empty selected suffix changed raw call code or metadata"
        count := count + 1
  SourceCompilerFeatureSupport.require (count == 1) "empty selected direct occurrence missing"

def run : IO Unit := do
  let program ← SourceCompilerFeatureSupport.get "source paths checker" (checkProgram workspace 1024)
  let path ← SourceCompilerFeatureSupport.compileNamed program "path"
  let (box, final, pathGaps) ← audit path "Final"
  let direct ← SourceCompilerFeatureSupport.compileNamed program "direct"
  let _ ← audit direct "Final"
  let bypass ← SourceCompilerFeatureSupport.compileNamed program "bypass"
  auditBypass bypass
  let emptySelected ← SourceCompilerFeatureSupport.compileNamed program "emptySelected"
  auditSelectedEmpty emptySelected
  let late ← SourceCompilerFeatureSupport.compileNamed program "late"
  let (_, broken, lateGaps) ← audit late "Broken"
  let early ← SourceCompilerFeatureSupport.compileNamed program "early"
  let _ ← audit early "Final"
  let empty ← SourceCompilerFeatureSupport.compileNamed program "empty"
  let boxed := SourceTypedRuntime.Value.constructed box [.bool true]
  let output := SourceTypedRuntime.Value.constructed final [boxed]
  for budget in [0, 41, 137, 500000] do
    for input in [0, 1, 2] do
      for (entry, terminalFault) in [(path, false), (direct, false), (late, true)] do
        let started ← entry.audit [SourceCompilerFeatureSupport.scalar input] budget
        let finished ← SourceCompilerFeatureSupport.get "source path resume" (started.resume 500000)
        let rawPrefix := if entry.key == direct.key then [(.word, some (word input)), (.word, some (word 19))] else []
        let firstCells := [(.word, some (word input))] ++ rawPrefix ++ [(.word, some (word input)), (.word, some (word input))]
        let secondCells := [(.bool, some (.bool (input == 1))),
          (.mapping .bool .word, some (.mapping .bool .word [])), (.word, some (word 0))]
        match finished.observation with
        | .done value state =>
          SourceCompilerFeatureSupport.require (!terminalFault && input == 1 && reprStr value == reprStr output)
            "source path result changed"
          cells state (firstCells ++ secondCells ++ [(box.resultType, some boxed), (.word, some (word 31)),
            (final.resultType, some output)]) "all three methods"
        | .fault (.uninitializedLocal id) state =>
          if input == 0 then
            SourceCompilerFeatureSupport.require (some id == pathGaps[0]?) "source path first fault changed"
            cells state (firstCells ++ [(.bool, none)]) "first fault / two methods skipped"
          else if input == 2 then
            SourceCompilerFeatureSupport.require (some id == pathGaps[1]?) "source path middle fault changed"
            cells state (firstCells ++ secondCells ++ [(box.resultType, none)]) "middle fault / last method skipped"
          else
            SourceCompilerFeatureSupport.require (terminalFault && input == 1 && some id == lateGaps[2]?)
              "source path final fault changed"
            cells state (firstCells ++ secondCells ++ [(box.resultType, some boxed), (.word, some (word 37)),
              (broken.resultType, none)]) "third method fault"
        | other => throw (IO.userError s!"source path unexpected: {reprStr other}")
    let selectedStarted ← emptySelected.audit [SourceCompilerFeatureSupport.scalar 17] budget
    let selectedFinished ← SourceCompilerFeatureSupport.get "empty selected resume" (selectedStarted.resume 500000)
    match selectedFinished.observation with
    | .done value state =>
      SourceCompilerFeatureSupport.require (reprStr value == reprStr (word 17)) "empty selected result changed"
      cells state [(.word, some (word 17)), (.word, some (word 17)), (.word, some (word 19))] "empty selected actual call only"
    | other => throw (IO.userError s!"empty selected unexpected: {reprStr other}")
    let started ← early.audit [] budget
    let finished ← SourceCompilerFeatureSupport.get "source path operand resume" (started.resume 500000)
    match finished.observation with
    | .fault (.uninitializedLocal _) state => cells state [(.word, some (word 23)), (.word, none)] "operand / all three methods skipped"
    | other => throw (IO.userError s!"source path operand unexpected: {reprStr other}")
    let started ← empty.audit [SourceCompilerFeatureSupport.scalar 17] budget
    let finished ← SourceCompilerFeatureSupport.get "empty path resume" (started.resume 500000)
    match finished.observation with
    | .done value state =>
      SourceCompilerFeatureSupport.require (reprStr value == reprStr (word 17)) "empty path result changed"
      cells state [(.word, some (word 17))] "empty path"
    | other => throw (IO.userError s!"empty path unexpected: {reprStr other}")
  let emptyCaller ← match empty.cached.indexed.base.functions.find? (·.signature.key == empty.key) with
    | some named => pure named.specialized
    | none => throw (IO.userError "empty path caller missing")
  SourceCompilerFeatureSupport.require
    (emptyCaller.function.typedBody.nodes.all fun item => match item with
      | .expression node => node.coercions.isEmpty
      | _ => true) "empty path unexpectedly emitted coercions"
  emptySelected.checkResume [SourceCompilerFeatureSupport.scalar 17] (.word (Word.ofNatModulo 17)) 41
  bypass.checkResume [SourceCompilerFeatureSupport.scalar 17] (.word (Word.ofNatModulo 17)) 41
  direct.checkResume [SourceCompilerFeatureSupport.scalar 1] (.constructed final [.constructed box [.bool true]]) 41
  empty.checkResume [SourceCompilerFeatureSupport.scalar 17] (.word (Word.ofNatModulo 17)) 41
  path.checkResume [SourceCompilerFeatureSupport.scalar 1] (.constructed final [.constructed box [.bool true]]) 41
  faultResume path [.word Word.zero]
  faultResume path [.word (Word.ofNatModulo 2)]
  faultResume late [.word (Word.ofNatModulo 1)]
  faultResume early []
  IO.println "coercion expressions: actual delegated/direct acceptance, raw children/global slots, ordered suffix code, operand/first/middle/last faults, exact heaps and public resume GREEN"

end Tests.SourceCoreCallableCoercionExpressions
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableCoercionMethodBodyMeaning
/-! Actual body/parameter/hook equations and finite builtin body trees close a
fixed selected method dictionary. Reflection produces the independent source
coercion step; this does not assert uniqueness of every possible source dictionary.
The runtime fixtures retain method evidence, input allocation, effects and faults. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096
namespace Tests.SourceCoreCallableCoercionMethodBodyMeaning
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap CoreProof ReadOnly CompatiblePayload CallableAncestryPairedLookup CallableIndexedHistory
open CallableIndexedParameterCertificates CallableIndexedParameterMeaning SourceCoreCallableIndexedFrames
open CallableCoercionMethodFrame (Frame BodyOutcome)
open CallableCoercionMethodBody
open CallableNamedMetadata (environment)
open CallableCoercionMethodInstantiation (Formation bodyInstance)

/-- The real method context retains residual type variables. A trait's two
head types are not a claim about its method's runtime parameter count. -/
theorem method_context_residual (program : CheckedProgram) (method : ExecutableImplMethods.CheckedMethod) :
    (bodyInstance program method).context.residualTypeVariables = true := rfl

theorem accepted_source_frame {loaded : LoadedProgram} {program : CheckedProgram}
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
    Dynamic.OperatorMethodSelected (SourceSemantics.Program.ofChecked program) context (environment available) "Coerce" "coerce"
      (step.requirement :: step.methodRequirements) (bodyInstance program method) (environment dictionary) ∧
    CallableCoercionMethodFrame.Frame (bodyInstance program method) (CallableCoercionMethodFrame.view (bodyInstance program method) (environment dictionary) compiled.statements) :=
  CallableCoercionMethodFrame.of_compilation (CallableMethodBodyCoherence.of_loaded loadedAccepted) receipt formed range signatures ledger assumptions resolved covered materialized compiled completeRecord

variable {checked : Checked} {base : Base checked}
  (prepared : SourceCoreCallableIndexedAncestry.Prepared base)
  {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : CompatiblePayload.FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : SourceSemantics.Program) {function : Dynamic.Closure} {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {readFuel : Nat} {bindings : List Binding} {output : Ty} {policy : SourceCoreLoops.Policy}
  {fuel : Nat} {fellThrough escaped : Word} {body parameterCode : Expr}
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {allocationGlobals : Nat}
  (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
  (bodyAccepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel function.source
    (bindings.reverse.map fun binding => (binding.1.id, binding.2)) function.body output reasonAt fellThrough escaped = .ok body)
  (projection : values.checked.catalog.project function.resultType = .ok output)
  (syntaxTree : BuiltinLexicalStatements.Syntax function.source context true function.body function.resultType)
  {flow : Expr}
  (emitted : body = CompatibleStatements.finish output flow fellThrough escaped)
  (tree : BuiltinLexicalStatements.Tree layouts owner active prepared.layout.frame allocationGlobals onError
    readFuel values function.source solved reasonAt context
    (bindings.reverse.map fun binding => (binding.1.id, binding.2)) true function.body function.resultType output flow)
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
  (sourceFrame : CallableCoercionMethodFrame.Frame sourceBody function)


include bodyAccepted projection syntaxTree emitted tree parameters inputs extended acceptedPrefix definitions registered represented environments heaps initialLocals
  actualLayout canonicalReference actualReference unmapped typed caller snapshots acceptedHook extension
  contextValid unique uninitialized missing faithful functionLeaves functionTypes actualTyped sourceFrame in
theorem accepted_method_preserves {call : CallableCoercionSpine.Call} {callerEnvironment captured : Environment}
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
  obtain ⟨certificate⟩ := BuiltinNamedBody.of_tree bodyAccepted projection syntaxTree emitted tree
  exact invoke_preserves
      (prepared := prepared) (functions := functions) (extension := extension) (program := program)
      (onError := onError) (certificate := certificate) (parameters := parameters) (inputs := inputs)
      (extended := extended) (contextValid := contextValid) (unique := unique) (uninitialized := uninitialized)
      (missing := missing) (faithful := faithful) (functionLeaves := functionLeaves) (functionTypes := functionTypes)
      (acceptedPrefix := acceptedPrefix) (definitions := definitions) (registered := registered) (acceptedHook := acceptedHook)
      (represented := represented) (environments := environments) (heaps := heaps) (initialLocals := initialLocals)
      (actualLayout := actualLayout) (actualTyped := actualTyped) (canonicalReference := canonicalReference) (actualReference := actualReference)
      (unmapped := unmapped) (typed := typed) (caller := caller) (snapshots := snapshots)
      (sourceFrame := sourceFrame) sourceArgument nativeArgument entry installed trace

include bodyAccepted projection syntaxTree emitted tree parameters inputs extended acceptedPrefix definitions registered represented environments heaps initialLocals
  actualLayout canonicalReference actualReference unmapped typed caller snapshots acceptedHook extension
  contextValid unique uninitialized missing faithful functionLeaves functionTypes actualTyped sourceFrame in
theorem accepted_method_reflects {call : CallableCoercionSpine.Call} {callerEnvironment captured : Environment}
    {input : Dynamic.Value} {nativeInput : Value} {reason : Word}
    (sourceArgument : arguments = [input]) (nativeArgument : nativeArguments = [nativeInput])
    (entry : actual = nativeInput :: captured)
    (installed : Installed call code ξ callerEnvironment captured store)
    {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {step : CoercionStep}
    (selected : Dynamic.OperatorMethodSelected program sourceContext evidence "Coerce" "coerce"
      step.requirements sourceBody function.evidence)
    {value : Value} {finalStore : Store}
    (completed : CallableCoercionSpine.Invoke callerEnvironment reason call store (.inRight .word nativeInput) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      (match outcome with
      | .value output => Dynamic.CoercionStepExecutes program sourceContext evidence before step input output after
      | .fault reason => Dynamic.CoercionStepFaults program sourceContext evidence before step input reason after) ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location current currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame finalMap finalStore records := by
  obtain ⟨certificate⟩ := BuiltinNamedBody.of_tree bodyAccepted projection syntaxTree emitted tree
  obtain ⟨outcome, after, finalMap, finalWorld, sourceOutcome, rest⟩ := invoke_reflects
      (prepared := prepared) (functions := functions) (extension := extension) (program := program)
      (onError := onError) (certificate := certificate) (parameters := parameters) (inputs := inputs)
      (extended := extended) (contextValid := contextValid) (unique := unique) (uninitialized := uninitialized)
      (missing := missing) (faithful := faithful) (functionLeaves := functionLeaves) (functionTypes := functionTypes)
      (acceptedPrefix := acceptedPrefix) (definitions := definitions) (registered := registered) (acceptedHook := acceptedHook)
      (represented := represented) (environments := environments) (heaps := heaps) (initialLocals := initialLocals)
      (actualLayout := actualLayout) (actualTyped := actualTyped) (canonicalReference := canonicalReference) (actualReference := actualReference)
      (unmapped := unmapped) (typed := typed) (caller := caller) (snapshots := snapshots)
      (sourceFrame := sourceFrame) sourceArgument nativeArgument entry installed completed
  refine ⟨outcome, after, finalMap, finalWorld, ?_, rest⟩
  cases sourceOutcome with
  | value invokes => exact .method selected invokes
  | fault fails => exact .method selected fails

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Marker<T> {}", "impl Marker<Bool> {}",
    "trait Witness<T> {}", "impl Witness<Bool> {}",
    "trait Coerce<From, To> where From: Marker { function coerce(value: From) returns (To) where From: Witness; }",
    "impl Coerce<Bool, Word> where Bool: Marker { function coerce(value: Bool) returns (Word) where Bool: Witness { let m: mapping(Bool => Word); let first = m[value]; { let shadow: Word = first + 6; shadow; } if (value) { return first + 19; } let gap: Word; return gap; } }",
    "function covered(flag: Bool) returns (Word) where Bool: Marker, Bool: Marker { let converted: Word = flag; return converted; }",
    "function early() returns (Word) where Bool: Marker { let missing: Bool; let converted: Word = missing; return converted; }"
  ]}] }

private def methodAt (entry : SourceCompilerFeatureSupport.Entry) : IO ExecutableImplMethods.CheckedMethod := do
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
        return method
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
  let program ← SourceCompilerFeatureSupport.get "method body checker" (checkProgram workspace 1024)
  let entry ← SourceCompilerFeatureSupport.compileNamed program "covered"
  let method ← methodAt entry
  let gap ← match (SourceCoreDataPlaces.declaredBinders method.specialized.function.typedBody).filter (·.name == "gap") with
    | [binder] => pure binder.id | _ => throw (IO.userError "actual method gap missing")
  let early ← SourceCompilerFeatureSupport.compileNamed program "early"
  let _ ← methodAt early
  let word (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
  for budget in [0, 31, 300000] do
    for flag in [true, false] do
      let started ← entry.audit [.bool flag] budget
      let resumed ← SourceCompilerFeatureSupport.get "method native resume" (started.resume 300000)
      let priorCells : List (TypeSystem.Ty × Option SourceTypedRuntime.Value) :=
        [(.bool, some (.bool flag)), (.bool, some (.bool flag)),
         (.mapping .bool .word, some (.mapping .bool .word [])),
         (.word, some (word 0)), (.word, some (word 6))]
      match resumed.observation with
      | .done value state =>
        SourceCompilerFeatureSupport.require (flag && reprStr value == reprStr (word 19)) "method success changed"
        cells state (priorCells ++ [(.word, some (word 19))]) "returned"
      | .fault (.uninitializedLocal actual) state =>
        SourceCompilerFeatureSupport.require (!flag && actual == gap) "method body fault changed origin"
        cells state (priorCells ++ [(.word, none)]) "fault"
      | other => throw (IO.userError s!"method outcome changed: {reprStr other}")
    let started ← early.audit [] budget
    let resumed ← SourceCompilerFeatureSupport.get "method pre-call fault resume" (started.resume 300000)
    match resumed.observation with
    | .fault (.uninitializedLocal _) state => cells state [(.bool, none)] "pre-call fault"
    | other => throw (IO.userError s!"method pre-call fault changed: {reprStr other}")
  entry.checkResume [.bool true] (SourceCompilerFeatureSupport.scalar 19) 31
  publicFaultResume entry [.bool false]
  publicFaultResume early []
  IO.println "coercion method body: actual dictionary/arity, marked parameters, scoped scalar body, exact fault effects and public resume GREEN"

end Tests.SourceCoreCallableCoercionMethodBodyMeaning
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableCoercionMethodEvidenceInvariant
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
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableCoercionPathMeaning
/-! Two actual emitted methods consume concrete builtin body certificates.
Source traces use the actual selected dictionaries, without assuming dictionary
uniqueness. Native completion needs no source body premise. Runtime checks
exercise two-step paths, first and later faults, exact cells and resumed calls. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
namespace Tests.SourceCoreCallableCoercionPathMeaning
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CallableIndexedHistory SourceCoreCallableIndexedFrames
open CallableCoercionMethodEntries CallableCoercionPathMeaning
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
  {first second : MethodProfile (prepared := prepared) (values := values) (program := program) (context := context) (evidence := evidence)}
  (uninitialized : ∀ method ∈ [first, second], ∀ id location, faults (.uninitializedLocation location) (method.diagnostics.reasonAt method.named.signature.key id))
  (missing : ∀ method ∈ [first, second], ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((method.diagnostics.reasonAt method.named.signature.key id).add tag))


variable {compilerProgram : CheckedProgram} {project : SourceCoreEvidence.Projector}
  {compilation : SourceCoreFunctions.Context} {callerFunction : SourceSpecialization.SpecializedFunction}
  {available : SourceCompilationPlan.EvidenceEnvironment} {scope : SourceCoreBasic.Scope}
  {node : ExpressionNode} {policy : SourceCoreFunctions.CallablePolicy} {ξ : Renaming}
  {inputCode outputCode : SourceCoreBasic.LoweredExpr} {calls : List CallableCoercionSpine.Call}


include extension definitions registered faithful observations runtimeViews uninitialized missing in
theorem two_step_preserves
    (emitted : Emitted compilerProgram project compilation callerFunction available scope node policy ξ inputCode [first, second] outputCode calls)
    {source target : TypeSystem.Ty} (chain : Chain source inputCode.type [first, second] target outputCode.type)
    {caller : Environment} {mapping : LocationMap} {world : StoreTyping}
    {before after : Dynamic.Heap} {initialStore store : Store} {input : Dynamic.Value} {native : Value}
    (entry : Entry [first, second] ambient.definitions caller mapping world before store)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (represented : ValueRep values.checked registry functions mapping world source input native inputCode.type)
    (operand : Evaluates caller initialStore (inputCode.expression.rename ξ) (.inRight .word native) store)
    {middle : Dynamic.Heap} {converted result : Dynamic.Value}
    (firstBody : Dynamic.BodyInvokes program first.sourceBody first.function.evidence before [input] converted middle)
    (secondBody : Dynamic.BodyInvokes program second.sourceBody second.function.evidence middle [converted] result after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates caller initialStore (outputCode.expression.rename ξ) value finalStore ∧
      PathOutcome [first, second] before input (.value result) after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        target outputCode.type faults (.value result) value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry [first, second] ambient.definitions caller finalMap finalWorld after finalStore) := by
  exact emitted_preserves functions extension definitions registered faithful observations runtimeViews uninitialized missing emitted chain entry heaps represented operand (.cons firstBody (.cons secondBody .nil))

include extension definitions registered faithful observations runtimeViews uninitialized missing in
theorem two_step_reflects
    (emitted : Emitted compilerProgram project compilation callerFunction available scope node policy ξ inputCode [first, second] outputCode calls)
    {source target : TypeSystem.Ty} (chain : Chain source inputCode.type [first, second] target outputCode.type)
    {caller : Environment} {mapping : LocationMap} {world : StoreTyping}
    {before : Dynamic.Heap} {initialStore store finalStore : Store} {input : Dynamic.Value} {native value : Value}
    (entry : Entry [first, second] ambient.definitions caller mapping world before store)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (represented : ValueRep values.checked registry functions mapping world source input native inputCode.type)
    (operand : Evaluates caller initialStore (inputCode.expression.rename ξ) (.inRight .word native) store)
    (completed : Evaluates caller initialStore (outputCode.expression.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      SelectedTrace [first, second] before input outcome after ∧ PathOutcome [first, second] before input outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        target outputCode.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry [first, second] ambient.definitions caller finalMap finalWorld after finalStore) := by
  exact emitted_reflects functions extension definitions registered faithful observations runtimeViews uninitialized missing emitted chain entry heaps represented operand completed

include extension definitions registered faithful observations runtimeViews uninitialized missing in
theorem first_fault_skips_second
    (emitted : Emitted compilerProgram project compilation callerFunction available scope node policy ξ inputCode [first, second] outputCode calls)
    {source target : TypeSystem.Ty} (chain : Chain source inputCode.type [first, second] target outputCode.type)
    {caller : Environment} {mapping : LocationMap} {world : StoreTyping}
    {before after : Dynamic.Heap} {initialStore store : Store} {input : Dynamic.Value} {native : Value}
    (entry : Entry [first, second] ambient.definitions caller mapping world before store)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (represented : ValueRep values.checked registry functions mapping world source input native inputCode.type)
    (operand : Evaluates caller initialStore (inputCode.expression.rename ξ) (.inRight .word native) store)
    (fault : Dynamic.SemanticFault)
    (failed : Dynamic.BodyFaults program first.sourceBody first.function.evidence before [input] fault after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates caller initialStore (outputCode.expression.rename ξ) value finalStore ∧
      PathOutcome [first, second] before input (.fault fault) after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        target outputCode.type faults (.fault fault) value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry [first, second] ambient.definitions caller finalMap finalWorld after finalStore) := by
  exact emitted_preserves functions extension definitions registered faithful observations runtimeViews uninitialized missing emitted chain entry heaps represented operand (.fault failed)

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Box { Box(Bool) }",
    "trait Marker<T> {}", "impl Marker<Word> {}", "impl Marker<Bool> {}",
    "trait Witness<T> {}", "impl Witness<Word> {}", "impl Witness<Bool> {}",
    "trait Coerce<From, To> where From: Marker { function coerce(value: From) returns (To) where From: Witness; }",
    "impl Coerce<Word, Bool> where Word: Marker { function coerce(value: Word) returns (Bool) where Word: Witness { let saved: Word = value; if (value == 0) { let firstGap: Bool; return firstGap; } return value == 1; } }",
    "impl Coerce<Bool, Box> where Bool: Marker { function coerce(value: Bool) returns (Box) where Bool: Witness { let m: mapping(Bool => Word); let touched = m[value]; if (value) { return Box(value); } let secondGap: Box; return secondGap; } }",
    "function path(value: Word) returns (Box) where Word: Marker, Word: Marker, Bool: Marker { let result: Box = value; return result; }",
    "function early() returns (Box) where Word: Marker, Bool: Marker { let missing: Word; let result: Box = missing; return result; }"
  ]}] }

private def word (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def cells (state : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) (label : String) : IO Unit :=
  SourceCompilerFeatureSupport.require (reprStr (state.heap.map fun cell => (cell.type, cell.value)) == reprStr expected)
    s!"path {label} ordered source cells changed: {reprStr state.heap}"

/-- Inspect the real retained two-edge list and replay the actual compiler
helper against the sealed plan. This also checks each full dictionary in order. -/
private def audit (entry : SourceCompilerFeatureSupport.Entry) :
    IO (DataConstructorInstantiation × Resolved.LocalId × Resolved.LocalId) := do
  let base := entry.cached.indexed.base
  let named ← match base.functions.find? (·.signature.key == entry.key) with
    | some named => pure named | none => throw (IO.userError "path caller missing")
  let caller := named.specialized
  let available ← SourceCompilerFeatureSupport.get "path caller evidence"
    (SourceCompilationPlan.resolveRuntimeEvidenceEnvironment base.sourceProgram caller.key caller.assumptions)
  let box ← match base.sourceProgram.signatures.dataTypes.find? (·.name == "Box") with
    | some box => pure box | none => throw (IO.userError "path Box missing")
  let constructor ← match box.constructors with
    | [constructor] => pure (DataConstructorInstantiation.mk constructor.id [] constructor.payloadTypes (.nominal box.id []))
    | _ => throw (IO.userError "path Box constructor missing")
  let mut gaps : List Resolved.LocalId := []
  let mut found := false
  for item in caller.function.typedBody.nodes do
    if let .expression node := item then
      if !node.coercions.isEmpty then
        SourceCompilerFeatureSupport.require (node.coercions.length == 2) "actual coercion path lost its two edges"
        let mut goals : List TypeSystem.Ty := []
        for step in node.coercions do
          let method ← SourceCompilerFeatureSupport.get "path method"
            (SourceCompilationPlan.checkedCoercionMethod base.sourceProgram caller node available step)
          let dictionary ← SourceCompilerFeatureSupport.get "path dictionary"
            (SourceCompilationPlan.coercionMethodRuntimeEvidence base.sourceProgram caller node step method)
          let key ← SourceCompilerFeatureSupport.get "path edge"
            (SourceCompilationPlan.exactCallKey base.plan named.signature.key node.id method.specialized.key)
          let selected ← SourceCompilerFeatureSupport.get "path full selected record"
            (SourceCompilationPlan.exactSpecialization base.plan key)
          let emitted ← match base.functions.find? (·.signature.key == key) with
            | some emitted => pure emitted | none => throw (IO.userError "path native row missing")
          SourceCompilerFeatureSupport.require (selected == method.specialized && emitted.specialized == selected &&
            emitted.inputs.length == 1 && dictionary.length == 3 && dictionary[0]? == dictionary[1]? &&
            dictionary[1]? != dictionary[2]? && dictionary.map SourceCompilationPlan.runtimeEvidenceGoal == selected.assumptions &&
            method.traitPredicates.all caller.assumptions.contains)
            "path full record / ordered repeated dictionary / caller coverage changed"
          goals := goals ++ [step.source, step.target]
          let gap ← match (SourceCoreDataPlaces.declaredBinders selected.function.typedBody).filter
              (fun binder => binder.name == "firstGap" || binder.name == "secondGap") with
            | [binder] => pure binder.id | _ => throw (IO.userError "path exact gap binder missing")
          gaps := gaps ++ [gap]
        SourceCompilerFeatureSupport.require (goals == [.word, .bool, .bool, constructor.resultType])
          "path raw endpoint order changed"
        let compilation : SourceCoreFunctions.Context := {
          plan := base.plan, owner := named.signature.key, globals := base.globals, administrativePrefix := 1,
          solvedRequirements := caller.function.solvedRequirements, internalReason := Word.zero }
        let lowered ← SourceCompilerFeatureSupport.get "path actual applyCoercions"
          (SourceCoreEvidence.applyCoercions base.sourceProgram (SourceCoreCompatibleDataExpressions.projectType entry.cached.compatible.checked) compilation caller available
            [] node {} ⟨.word, LanguageResult.success (.word (Word.ofNatModulo 1))⟩ node.coercions)
        let outputType ← SourceCompilerFeatureSupport.get "path result projection"
          (entry.cached.compatible.checked.catalog.project constructor.resultType)
        SourceCompilerFeatureSupport.require (lowered.type == outputType &&
          Core.infer? (.unit :: base.globals.map SourceCoreCalls.Signature.referenceType) lowered.expression
            entry.cached.indexed.layouts.definitions == some (LanguageResult.resultType outputType))
          "path actual native code/ordered globals type mismatch"
        found := true
  SourceCompilerFeatureSupport.require found "actual two-step path not reached"
  match gaps with
  | [first, second] => pure (constructor, first, second)
  | _ => throw (IO.userError "path did not select exactly two method gaps")

private def faultResume (entry : SourceCompilerFeatureSupport.Entry) (arguments : List SourceCoreExecution.Value) : IO Unit := do
  let artifact ← entry.execution.open
  let initial ← SourceCompilerFeatureSupport.boot artifact
  let finished ← SourceCompilerFeatureSupport.get "path public fault"
    (← initial.run entry.key arguments SourceCompilerFeatureSupport.executionOptions)
  let (fault, session) ← match finished with
    | .failed fault session => pure (fault, session)
    | _ => throw (IO.userError "path expected public fault")
  let expected ← SourceCompilerFeatureSupport.get "path fault snapshot" (← session.snapshot 2048)
  for budget in [0, 41, 137] do
    let started ← SourceCompilerFeatureSupport.get "path suspend"
      (← initial.run entry.key arguments {SourceCompilerFeatureSupport.executionOptions with executionFuel := budget})
    let resumed ← match started with
      | .outOfFuel checkpoint => checkpoint.resume 500000 2048
      | outcome => pure outcome
    match resumed with
    | .failed observed session =>
      let snapshot ← SourceCompilerFeatureSupport.get "path resumed snapshot" (← session.snapshot 2048)
      SourceCompilerFeatureSupport.require (observed == fault && reprStr snapshot.cells == reprStr expected.cells)
        "path failure reason or complete source store changed on resume"
    | _ => throw (IO.userError "path failure resume changed outcome")

def run : IO Unit := do
  let program ← SourceCompilerFeatureSupport.get "path checker" (checkProgram workspace 1024)
  let path ← SourceCompilerFeatureSupport.compileNamed program "path"
  let (constructor, firstGap, secondGap) ← audit path
  let early ← SourceCompilerFeatureSupport.compileNamed program "early"
  let _ ← audit early
  let output := SourceTypedRuntime.Value.constructed constructor [.bool true]
  for budget in [0, 41, 137, 500000] do
    for input in [0, 1, 2] do
      let started ← path.audit [SourceCompilerFeatureSupport.scalar input] budget
      let finished ← SourceCompilerFeatureSupport.get "path resume" (started.resume 500000)
      let firstCells := [(.word, some (word input)), (.word, some (word input)), (.word, some (word input))]
      let secondCells := [(.bool, some (.bool (input == 1))),
        (.mapping .bool .word, some (.mapping .bool .word [])), (.word, some (word 0))]
      match finished.observation with
      | .done value state =>
        SourceCompilerFeatureSupport.require (input == 1 && reprStr value == reprStr output) "path result changed"
        cells state (firstCells ++ secondCells ++ [(constructor.resultType, some output)]) "two-step success"
      | .fault (.uninitializedLocal id) state =>
        if input == 0 then
          SourceCompilerFeatureSupport.require (id == firstGap) "first path fault changed"
          cells state (firstCells ++ [(.bool, none)]) "first method / suffix skipped"
        else
          SourceCompilerFeatureSupport.require (input == 2 && id == secondGap) "later path fault changed"
          cells state (firstCells ++ secondCells ++ [(constructor.resultType, none)]) "second method"
      | other => throw (IO.userError s!"path unexpected outcome: {reprStr other}")
    let started ← early.audit [] budget
    let finished ← SourceCompilerFeatureSupport.get "path operand fault resume" (started.resume 500000)
    match finished.observation with
    | .fault (.uninitializedLocal _) state => cells state [(.word, none)] "operand / both methods skipped"
    | other => throw (IO.userError s!"path operand unexpected outcome: {reprStr other}")
  faultResume path [.word Word.zero]
  faultResume path [.word (Word.ofNatModulo 2)]
  faultResume early []
  IO.println "coercion path: actual two steps, ordered dictionaries/full records, first/later fault stores and resume GREEN"

end Tests.SourceCoreCallableCoercionPathMeaning
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableCoercionPlanProvenance
/-! Complete carrier identity survives insertion, duplicate acceptance and a
later helper extension. Same keys with changed source, evidence or stage data
are rejected by the actual extension action. Source body semantics are separate. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreCallableCoercionPlanProvenance
open Solcore Frontend SourceInference SourceSemantics.CoreLowering SourceSpecializationWorklist
open CallableCoercionPlanProvenance

/-- Two actual public extensions retain the original complete method carrier,
even when the later action supplies a different detached root. -/
theorem later_extension {program : CheckedProgram} {before middle final : Plan}
    {method helper : SourceSpecialization.SpecializedFunction} {edge other : CallEdge} {budget nextBudget : Nat}
    (first : extendCompletePlan program before method edge budget = .ok (.complete middle))
    (second : extendCompletePlan program middle helper other nextBudget = .ok (.complete final)) :
    SourceCompilationPlan.exactSpecialization final method.key = .ok method :=
  selected_after second (complete_root first)

/-- The proof records equality of the raw checked body and ordered ledger, not
only of the method key or the native signature. -/
theorem emitted_source_and_ledger {program : CheckedProgram} {project : CallableCoercionSpine.Projector}
    {context : CallableCoercionSpine.Context} {caller : SourceSpecialization.SpecializedFunction}
    {available : CallableCoercionSpine.RuntimeEvidence} {scope : CallableCoercionSpine.Scope}
    {node : ExpressionNode} {policy : SourceCoreFunctions.CallablePolicy}
    {input output : CallableCoercionSpine.Lowered} {coercion : CoercionStep} {call : CallableCoercionSpine.Call}
    (step : CallableCoercionSpine.Step program project context caller available scope node policy input coercion output call)
    {before : Plan} {edge : CallEdge} {budget : Nat}
    (extended : extendCompletePlan program before step.method.specialized edge budget = .ok (.complete context.plan)) :
    step.specialized.function.typedBody = step.method.specialized.function.typedBody ∧
    step.specialized.function.solvedRequirements = step.method.specialized.function.solvedRequirements ∧
    step.specialized.assumptions = step.method.specialized.assumptions ∧
    step.specialized.stageAnalysis = step.method.specialized.stageAnalysis := by
  rw [step_specialized step extended]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Same-key carriers cannot pass comparison after any full-body change. -/
theorem changed_body_rejected {left right : SourceSpecialization.SpecializedFunction}
    (different : left.function.typedBody ≠ right.function.typedBody) : (left == right) = false := by
  cases same : (left == right) with
  | false => rfl
  | true => exact False.elim (different (congrArg (fun value => value.function.typedBody)
      (CallableSpecializationEquality.eq_of_beq same)))

theorem changed_stage_rejected {left right : SourceSpecialization.SpecializedFunction}
    (different : left.stageAnalysis ≠ right.stageAnalysis) : (left == right) = false := by
  cases same : (left == right) with
  | false => rfl
  | true => exact False.elim (different (congrArg (·.stageAnalysis)
      (CallableSpecializationEquality.eq_of_beq same)))

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Marker<T> {}", "impl Marker<Bool> {}",
    "trait Witness<T> {}", "impl Witness<Bool> {}",
    "trait Coerce<From, To> where From: Marker { function coerce(value: From) returns (To) where From: Witness; }",
    "function choose(flag: Bool) returns (Word) { return flag ? 17 : 4; }",
    "impl Coerce<Bool, Word> where Bool: Marker { function coerce(value: Bool) returns (Word) where Bool: Witness { let seen: Word = 2; let other: Word = 3; return choose(value); } }",
    "function converted(flag: Bool) returns (Word) where Bool: Marker { return flag; }"
  ]}] }

private def checkSelected (plan : Plan) (value : SourceSpecialization.SpecializedFunction) : IO Unit := do
  let actual ← SourceCompilerFeatureSupport.get "exact carrier" (SourceCompilationPlan.exactSpecialization plan value.key)
  SourceCompilerFeatureSupport.require (actual == value) "complete selected carrier changed"

private def audit (entry : SourceCompilerFeatureSupport.Entry) : IO Unit := do
  let base := entry.cached.indexed.base
  let mut observed := false
  for named in base.functions do
    if named.signature.key == entry.key then
      let caller := named.specialized
      let available ← SourceCompilerFeatureSupport.get "caller" (SourceCompilationPlan.resolveRuntimeEvidenceEnvironment base.sourceProgram caller.key caller.assumptions)
      for item in caller.function.typedBody.nodes do
        match item with
        | .expression node =>
          for step in node.coercions do
            let method ← SourceCompilerFeatureSupport.get "actual selected method"
              (SourceCompilationPlan.checkedCoercionMethod base.sourceProgram caller node available step)
            let root := method.specialized
            let edge : CallEdge := ⟨caller.key, node.id, root.key⟩
            let empty : Plan := ⟨[], [], [], []⟩
            let exhausted ← SourceCompilerFeatureSupport.get "zero helper budget"
              (extendCompletePlan base.sourceProgram empty root edge 0)
            match exhausted with
            | .budgetExhausted kept _ pending =>
                checkSelected kept root
                SourceCompilerFeatureSupport.require (!pending.isEmpty) "helper request was dropped"
            | .complete _ => throw (IO.userError "fixture did not reach the helper frontier")
            let outcome ← SourceCompilerFeatureSupport.get "insert detached method"
              (extendCompletePlan base.sourceProgram empty root edge 8)
            let inserted ← match outcome with
              | .complete plan => pure plan
              | _ => throw (IO.userError "helper closure exhausted")
            checkSelected inserted root
            SourceCompilerFeatureSupport.require (inserted.specializations.length == 2) "actual ordinary helper was not retained"
            let repeated ← SourceCompilerFeatureSupport.get "accept identical root"
              (extendCompletePlan base.sourceProgram inserted root edge 8)
            for old in inserted.specializations do checkSelected repeated.plan old
            SourceCompilerFeatureSupport.require (repeated.plan.specializations == inserted.specializations)
              "repeated root replaced or duplicated a carrier"
            let changedSource := {root with function := {root.function with typedBody :=
              {root.function.typedBody with owner := {root.function.typedBody.owner with declarationIndex := root.function.typedBody.owner.declarationIndex + 1}}}}
            let changedEvidence := {root with function := {root.function with solvedRequirements := root.function.solvedRequirements.reverse}}
            let changedAssumptions := {root with assumptions := root.assumptions.reverse}
            let changedStages := {root with stageAnalysis := {root.stageAnalysis with expressions := root.stageAnalysis.expressions.reverse}}
            for changed in [changedSource, changedEvidence, changedAssumptions, changedStages] do
              SourceCompilerFeatureSupport.require (changed.key == root.key && !(changed == root)) "mutation fixture did not change a non-key field"
              match extendCompletePlan base.sourceProgram inserted changed edge 8 with
              | .error (.existingSpecializationMismatch key) =>
                  SourceCompilerFeatureSupport.require (key == root.key) "wrong mismatched key"
              | _ => throw (IO.userError "same-key changed carrier was accepted")
            match extendCompletePlan base.sourceProgram {empty with specializations := [root, root]} root edge 8 with
            | .error (.duplicatePlanSpecializations key 2) =>
                SourceCompilerFeatureSupport.require (key == root.key) "wrong duplicate key"
            | _ => throw (IO.userError "duplicate root plan accepted")
            observed := true
        | _ => pure ()
  SourceCompilerFeatureSupport.require observed "coercion method not found"

def run : IO Unit := do
  let program ← SourceCompilerFeatureSupport.get "checker" (checkProgram workspace)
  let entry ← SourceCompilerFeatureSupport.compileNamed program "converted"
  audit entry
  entry.checkResume [.bool true] (SourceCompilerFeatureSupport.scalar 17) 9
  SourceCompilerFeatureSupport.require ((← entry.run [.bool false]) == SourceCompilerFeatureSupport.scalar 4) "false result changed"
  IO.println "coercion plan: insertion, duplicate carrier, helper closure, full metadata rejection and resume GREEN"

end Tests.SourceCoreCallableCoercionPlanProvenance
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableCoercionPreparation
/-! Outer preparation supplies actual method-extension witnesses, including
coercions inside appended carriers. Formal consumers retain same-fuel source
body provenance and the explicit caller-covered dictionary boundary. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCallableCoercionPreparation
open Solcore Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CallableCoercionPreparation CallableCoercionPreparationSteps

/-- No individual extension equality is assumed at the emitted body boundary. -/
theorem prepared_source_body {loaded : LoadedProgram} {program : CheckedProgram}
    (loadedAccepted : Frontend.checkLoadedProgram loaded 1024 = .ok program)
    {before : SourceSpecializationWorklist.Plan} {fuel budget : Nat}
    {project : CallableCoercionSpine.Projector} {context : CallableCoercionSpine.Context}
    (prepared : SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget program before fuel budget = .ok context.plan)
    {caller : Specialized} (member : caller ∈ context.plan.specializations)
    {node : ExpressionNode} (nodeMember : .expression node ∈ caller.function.typedBody.nodes)
    {coercion : CoercionStep} (site : coercion ∈ node.coercions ++ argumentSteps node)
    {available : CallableCoercionSpine.RuntimeEvidence}
    (resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions = .ok available)
    {scope : CallableCoercionSpine.Scope} {policy : SourceCoreFunctions.CallablePolicy}
    {input output : CallableCoercionSpine.Lowered} {call : CallableCoercionSpine.Call}
    (step : CallableCoercionSpine.Step program project context caller available scope node policy input coercion output call) :
    ∃ retained, retained ∈ program.methods ∧ retained.id = step.method.id ∧
      step.specialized.function.typedBody = StructuralSubstitution.applyTypedSource
        step.specialized.parameterSubstitution retained.checked.typedBody ∧
      step.specialized.function.solvedRequirements = retained.checked.solvedRequirements.map
        (StructuralSubstitution.applySolvedRequirement step.specialized.parameterSubstitution) := by
  rw [step_specialized prepared member nodeMember site resolved step]
  obtain ⟨receipt⟩ := CallableCoercionBodyProvenance.of_accepted (CallableMethodBodyCoherence.of_loaded loadedAccepted) step.selectedMethod
  exact ⟨receipt.retained, receipt.retainedMember, receipt.retainedId, receipt.body, receipt.ledger⟩

/-- The actual dictionary is obtained from the preparation visit. Its source
origin profile remains explicit; preparation does not imply that profile. -/
theorem prepared_dictionary {program : CheckedProgram} {before after : SourceSpecializationWorklist.Plan} {fuel budget : Nat}
    (prepared : SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget program before fuel budget = .ok after)
    {caller : Specialized} (member : caller ∈ after.specializations)
    {node : ExpressionNode} (nodeMember : .expression node ∈ caller.function.typedBody.nodes)
    {coercion : CoercionStep} (site : coercion ∈ node.coercions ++ argumentSteps node)
    {available : CallableCoercionSpine.RuntimeEvidence}
    (resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions = .ok available)
    (covered : ∀ method, SourceCompilationPlan.checkedCoercionMethod program caller node available coercion = .ok method →
      CallableCoercionEvidenceOrigins.CallerCovered caller method) :
    ∃ receipt : Visit program caller available node coercion after,
      ∃ selected : CallableCoercionMethodCertificates.Certificate program caller node available coercion receipt.method,
        Dynamic.EvidenceEnvironment.AssembledFrom (CallableNamedMetadata.environment available)
          (CallableNamedMetadata.evidence selected.primary :: selected.methodEvidence.map CallableNamedMetadata.evidence)
          receipt.method.specialized.assumptions (CallableNamedMetadata.environment receipt.dictionary) ∧
        (CallableNamedMetadata.environment receipt.dictionary).Valid program.signatures.resolutionRules ∧
        (CallableNamedMetadata.environment receipt.dictionary).map Prod.fst = receipt.method.specialized.assumptions := by
  obtain ⟨receipt⟩ := visit prepared member nodeMember site resolved
  obtain ⟨selected⟩ := CallableCoercionMethodCertificates.of_accepted receipt.selected
  exact ⟨receipt, selected, CallableCoercionEvidenceOrigins.Certificate.origins selected
    (covered _ receipt.selected) resolved receipt.materialized⟩

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Coerce<From, To> { function coerce(value: From) returns (To); }",
    "function isZero(value: Word) returns (Bool) { return value == 0; }",
    "impl Coerce<Word, Bool> { function coerce(value: Word) returns (Bool) { let flag: Bool = isZero(value); let roundtrip: Word = flag; return flag; } }",
    "impl Coerce<Bool, Word> { function coerce(value: Bool) returns (Word) { if (value) { return 7; } return 3; } }",
    "function converted(value: Word) returns (Bool) { let first: Bool = value; let second: Bool = value; return second; }",
    "function accepts(value: Bool) returns (Word) { if (value) { return 13; } return 17; }",
    "function indirect(value: Word) returns (Word) { let f: function(Bool) returns (Word) = accepts; return f(value); }"
  ]}] }

private def audit (entry : SourceCompilerFeatureSupport.Entry) (indirect : Bool) : IO Unit := do
  let base := entry.cached.indexed.base
  let program := base.sourceProgram
  let seeds ← base.plan.seedKeys.mapM fun key => do
    let root ← SourceCompilerFeatureSupport.get "seed full record" (SourceCompilationPlan.exactSpecialization base.plan key)
    pure ({declaration := root.declaration, parameterSubstitution := root.parameterSubstitution} : SourceSpecializationWorklist.Request)
  let original ← SourceCompilerFeatureSupport.get "original ordinary worklist" (SourceSpecializationWorklist.run program seeds 1024)
  let initial ← match original with
    | .complete plan => pure plan
    | _ => throw (IO.userError "ordinary fixture exceeded budget")
  let prepared ← SourceCompilerFeatureSupport.get "actual outer preparation"
    (SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget program initial 1024 1024)
  SourceCompilerFeatureSupport.require (prepared == base.plan) "prepared complete plan changed"
  SourceCompilerFeatureSupport.require (prepared.specializations.take initial.specializations.length == initial.specializations)
    "initial carrier prefix changed"
  SourceCompilerFeatureSupport.require (prepared.specializations.length > initial.specializations.length)
    "detached method closure was not exercised"
  match SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget program initial initial.specializations.length 1024 with
  | .error (.executablePlanClosureFuelExhausted _) => pure ()
  | _ => throw (IO.userError "appended carriers escaped the outer scan budget")
  match SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget program initial 1024 0 with
  | .error (.coercionMethodSpecializationBudgetExhausted ..) => pure ()
  | _ => throw (IO.userError "method helper did not consume the actual helper budget")
  let mut outputCount := 0
  let mut argumentCount := 0
  let mut appendedCount := 0
  let mut methods : List SourceSpecialization.SpecializationKey := []
  for caller in prepared.specializations do
    let available ← SourceCompilerFeatureSupport.get "actual caller resolver"
      (SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions)
    for item in caller.function.typedBody.nodes do
      match item with
      | .expression node =>
        outputCount := outputCount + node.coercions.length
        argumentCount := argumentCount + (argumentSteps node).length
        for coercion in node.coercions ++ argumentSteps node do
          let method ← SourceCompilerFeatureSupport.get "reached complete method"
            (SourceCompilationPlan.checkedCoercionMethod program caller node available coercion)
          let dictionary ← SourceCompilerFeatureSupport.get "reached actual dictionary"
            (SourceCompilationPlan.coercionMethodRuntimeEvidence program caller node coercion method)
          SourceCompilerFeatureSupport.require
            (dictionary.map SourceCompilationPlan.runtimeEvidenceGoal == method.specialized.assumptions)
            "ordered dictionary goals changed"
          let selected ← SourceCompilerFeatureSupport.get "final exact method selection"
            (SourceCompilationPlan.exactSpecialization prepared method.specialized.key)
          SourceCompilerFeatureSupport.require (selected == method.specialized) "later extension changed the full method record"
          let repeated ← SourceCompilerFeatureSupport.get "repeat actual extension"
            (SourceSpecializationWorklist.extendCompletePlan program prepared method.specialized
              ⟨caller.key, node.id, method.specialized.key⟩ 1024)
          SourceCompilerFeatureSupport.require (repeated.plan.specializations == prepared.specializations)
            "repeated root changed ordered carriers"
          if !initial.specializations.contains caller then appendedCount := appendedCount + 1
          methods := method.specialized.key :: methods
      | _ => pure ()
  SourceCompilerFeatureSupport.require (appendedCount > 0 && outputCount > 0)
    "coercion in an appended method was not inspected"
  SourceCompilerFeatureSupport.require (if indirect then argumentCount > 0 else methods.length > methods.eraseDups.length)
    "indirect argument or repeated method coverage missing"

def run : IO Unit := do
  let program ← SourceCompilerFeatureSupport.get "coercion preparation checker" (Frontend.checkProgram workspace 1024)
  let converted ← SourceCompilerFeatureSupport.compileNamed program "converted"
  audit converted false
  converted.checkResume [SourceCompilerFeatureSupport.scalar 0] (.bool true) 17
  SourceCompilerFeatureSupport.require ((← converted.run [SourceCompilerFeatureSupport.scalar 1]) == .bool false)
    "nested method result changed"
  let indirect ← SourceCompilerFeatureSupport.compileNamed program "indirect"
  audit indirect true
  indirect.checkResume [SourceCompilerFeatureSupport.scalar 0] (SourceCompilerFeatureSupport.scalar 13) 9
  SourceCompilerFeatureSupport.require ((← indirect.run [SourceCompilerFeatureSupport.scalar 2]) == SourceCompilerFeatureSupport.scalar 17)
    "indirect argument coercion changed"
  IO.println "coercion preparation: appended method/helper coverage, exact later records, indirect arguments, budgets and resume GREEN"

end Tests.SourceCoreCallableCoercionPreparation
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableCoercionRawGroups
/-! The consumers begin with actual delegated acceptance and its actual
contextual callback, then close raw meaning with a concrete builtin child.
Runtime fixtures deliberately insert retained IR groups; they do not claim the
parser or checker places a coercion on the written group's parent node. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Tests.SourceCoreCallableCoercionRawGroups
open Solcore SourceSemantics SourceSemantics.CoreLowering Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CallableIndexedHistory
open SourceCoreCallableIndexedFrames CallableCoercionMethodEntries CallableCoercionPathMeaning
open CallableCoercionExpressionCertificates CallableCoercionRawGroupCertificates

section Accepted
variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
  {values : ValuesContext} {compilerProgram : CheckedProgram}
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {source : TypedSource} {environment : Dynamic.Environment} {before : Dynamic.Heap}
  {caller : Environment} {mapping : LocationMap} {world : StoreTyping} {store : Store}
  {node : ExpressionNode} {ξ : Renaming} {operand : Lowered}

variable {raw : Workspace.RawWorkspace} {checkFuel : Nat}
  (checkedAccepted : checkProgram raw checkFuel = .ok compilerProgram)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (definitions : prepared.layouts.definitions = ambient.definitions)
  (registered : prepared.ancestry.layout.frame.Registered ambient.definitions)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  {methods : Profiles (prepared := prepared) (values := values) (program := Program.ofChecked compilerProgram)
    (context := context) (evidence := evidence)}
  (uninitialized : ∀ method ∈ methods, ∀ id location, faults (.uninitializedLocation location) (method.diagnostics.reasonAt method.named.signature.key id))
  (missing : ∀ method ∈ methods, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((method.diagnostics.reasonAt method.named.signature.key id).add tag))
  {project : Projector} {compilation : SourceCoreFunctions.Context} {callerFunction : Specialized} {available : Available}
  {scope : Scope} {id : ExpressionId} {child : SourceCoreEvidence.Child} {fuel : Nat}
  {reasonAt : ExpressionId → Word} {policy : SourceCoreFunctions.CallablePolicy} {output : Lowered}
  {calls : List CallableCoercionSpine.Call}
  (receipt : Delegated compilerProgram project callerFunction compilation child fuel source scope id reasonAt policy node output)
  (emitted : Emitted compilerProgram project compilation callerFunction receipt.available scope node policy ξ receipt.operand methods output calls)
  (steps : methods.map (·.step) = node.coercions)
  (chain : Chain node.rawType receipt.operand.type methods node.type output.type)
  (ledger : context.solvedRequirements = callerFunction.function.solvedRequirements)
  (entry : Entry methods ambient.definitions caller mapping world before store)


variable {readFuel : Nat} {inner : ExpressionId}
  (valid : CompatibleExpressionLiterals.ContextValid compilation.solvedRequirements context evidence)
  (rawUninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (rawMissing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  {administrative : Core.Context} {canonical : Environment} {actualContext : Core.Context}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world administrative scope environment canonical ambient.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical caller)
  (actualTyped : RuntimeEnvironmentHasTypes world caller actualContext ambient.definitions)


variable {representation : SourceCoreGeneralFunctions.Representation} {signatures : ProgramSignatures}
  {localsCatalog : SourceCoreLocalPolymorphism.Catalog} {parents : List SourceCoreLocalEvidence.Prepared}
  {assignments : SourceCoreAssignmentFaultSites.Table} {diagnostics : SourceCoreDataPlaceFaultSites.Program}
  {native : SourceCoreGeneralFunctions.CallableContext} {parent : Option SourceCoreLocalEvidence.Prepared}
  {skipInitializer : Option ExpressionId}
  (childEq : child = SourceCoreGeneralFunctions.lowerContextualExpression compilerProgram representation signatures localsCatalog parents
    assignments diagnostics compilation (some native) parent skipInitializer)
  (form : node.form = .group inner) (typed : ExpressionHasType source context id node.type)
  (avoids : CallableLambdaBodyReachability.Avoids source [.expression inner] [node.id])
  (syntaxTree : CompatibleExpressionBuiltins.Syntax source inner)
  (ordinary : CompatibleExpressionBuiltins.Ordinary (SourceCoreEvidence.withNode source (rawNode node [])) localsCatalog compilation.owner)
  (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
  (declarations : CompatibleExpressionReads.ScopeDeclarations (SourceCoreEvidence.withNode source (rawNode node [])) scope context)
  (sourceSignatures : context.signatures = values.checked.signatures)
  (readPolicy : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
  (lowerPolicy : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
  (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)

include checkedAccepted ledger extension definitions registered faithful observations runtimeViews uninitialized missing emitted steps chain entry valid rawUninitialized rawMissing environments heaps locals agrees actualTyped childEq form typed avoids syntaxTree ordinary closed residual declarations sourceSignatures readPolicy lowerPolicy leafPolicy in
theorem accepted_preserves
    (unique : NodeOccurrencesUnique source)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : Dynamic.ExpressionEvaluatesOutcome (Program.ofChecked compilerProgram) context evidence source environment before id outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates caller store (output.expression.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        node.type output.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry methods ambient.definitions caller finalMap finalWorld after finalStore) := by
  obtain ⟨childTree⟩ := CallableCoercionRawGroupCertificates.of_contextual receipt childEq unique form typed avoids syntaxTree
    ordinary closed residual declarations sourceSignatures readPolicy lowerPolicy leafPolicy
  exact CallableCoercionRawGroupMeaning.preserves functions checkedAccepted extension definitions registered faithful observations runtimeViews
    uninitialized missing receipt emitted steps chain ledger entry childTree valid rawUninitialized rawMissing
    environments heaps locals agrees actualTyped unique trace

include extension definitions registered faithful observations runtimeViews uninitialized missing emitted steps chain entry valid rawUninitialized rawMissing environments heaps locals agrees actualTyped childEq form typed avoids syntaxTree ordinary closed residual declarations sourceSignatures readPolicy lowerPolicy leafPolicy in
theorem accepted_reflects
    (unique : NodeOccurrencesUnique source)
    {value : Value} {finalStore : Store}
    (completed : Evaluates caller store (output.expression.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome (Program.ofChecked compilerProgram) context evidence source environment before id outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        node.type output.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry methods ambient.definitions caller finalMap finalWorld after finalStore) := by
  obtain ⟨childTree⟩ := CallableCoercionRawGroupCertificates.of_contextual receipt childEq unique form typed avoids syntaxTree
    ordinary closed residual declarations sourceSignatures readPolicy lowerPolicy leafPolicy
  exact CallableCoercionRawGroupMeaning.reflects functions extension definitions registered faithful observations runtimeViews
    uninitialized missing receipt emitted steps chain entry childTree valid rawUninitialized rawMissing
    environments heaps locals agrees actualTyped completed

end Accepted

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Box { Box(Bool) }", "enum Final { Final(Box) }", "enum Broken { Broken(Box) }",
    "trait Marker<T> {}", "impl Marker<Word> {}", "impl Marker<Bool> {}", "impl Marker<Box> {}",
    "trait Witness<T> {}", "impl Witness<Word> {}", "impl Witness<Bool> {}", "impl Witness<Box> {}",
    "trait Coerce<From, To> where From: Marker { function coerce(value: From) returns (To) where From: Witness; }",
    "impl Coerce<Word, Bool> where Word: Marker { function coerce(value: Word) returns (Bool) where Word: Witness { let saved: Word = value; if (value == 0) { let firstGap: Bool; return firstGap; } return value == 1; } }",
    "impl Coerce<Bool, Box> where Bool: Marker { function coerce(value: Bool) returns (Box) where Bool: Witness { let m: mapping(Bool => Word); let touched = m[value]; if (value) { return Box(value); } let secondGap: Box; return secondGap; } }",
    "impl Coerce<Box, Final> where Box: Marker { function coerce(value: Box) returns (Final) where Box: Witness { let reached: Word = 31; return Final(value); } }",
    "impl Coerce<Box, Broken> where Box: Marker { function coerce(value: Box) returns (Broken) where Box: Witness { let reached: Word = 37; let lastGap: Broken; return lastGap; } }",
    "function identity(value: Word) returns (Word) { let rawEffect: Word = 19; return value; }",
    "function rawFail() returns (Word) { let rawEffect: Word = 23; let rawGap: Word; return rawGap; }",
    "function direct(value: Word) returns (Final) where Word: Marker, Bool: Marker, Box: Marker { let result: Final = identity(value); return result; }",
    "function emptySelected(value: Word) returns (Word) where Word: Marker { return identity(value); }",
    "function bypass(value: Word) returns (Word) { return identity(value); }",
    "function path(value: Word) returns (Final) where Word: Marker, Word: Marker, Bool: Marker, Box: Marker { let result: Final = value + 0; return result; }",
    "function late(value: Word) returns (Broken) where Word: Marker, Bool: Marker, Box: Marker { let result: Broken = value + 0; return result; }",
    "function early() returns (Final) where Word: Marker, Bool: Marker, Box: Marker { let result: Final = rawFail(); return result; }",
    "function operand() returns (Final) where Word: Marker, Bool: Marker, Box: Marker { let missing: Word; let result: Final = missing + 0; return result; }",
    "function empty(value: Word) returns (Word) { return value; }"
  ]}] }


private def word (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def cells (state : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) (label : String) : IO Unit :=
  SourceCompilerFeatureSupport.require (reprStr (state.heap.map fun cell => (cell.type, cell.value)) == reprStr expected)
    s!"path {label} ordered source cells changed: {reprStr state.heap}"

private def constructorFor (program : CheckedProgram) (name : String) : IO DataConstructorInstantiation := do
  let data ← match program.signatures.dataTypes.find? (·.name == name) with
    | some data => pure data | none => throw (IO.userError s!"source path {name} missing")
  match data.constructors with
  | [constructor] => pure (DataConstructorInstantiation.mk constructor.id [] constructor.payloadTypes (.nominal data.id []))
  | _ => throw (IO.userError s!"source path {name} constructor missing")

private def faultResume (entry : SourceCompilerFeatureSupport.Entry) (arguments : List SourceCoreExecution.Value) : IO Unit := do
  let artifact ← entry.execution.open
  let initial ← SourceCompilerFeatureSupport.boot artifact
  let finished ← SourceCompilerFeatureSupport.get "path public fault"
    (← initial.run entry.key arguments SourceCompilerFeatureSupport.executionOptions)
  let (fault, session) ← match finished with
    | .failed fault session => pure (fault, session)
    | _ => throw (IO.userError "path expected public fault")
  let expected ← SourceCompilerFeatureSupport.get "path fault snapshot" (← session.snapshot 2048)
  for budget in [0, 41, 137] do
    let started ← SourceCompilerFeatureSupport.get "path suspend"
      (← initial.run entry.key arguments {SourceCompilerFeatureSupport.executionOptions with executionFuel := budget})
    let resumed ← match started with
      | .outOfFuel checkpoint => checkpoint.resume 500000 2048
      | outcome => pure outcome
    match resumed with
    | .failed observed session =>
      let snapshot ← SourceCompilerFeatureSupport.get "path resumed snapshot" (← session.snapshot 2048)
      SourceCompilerFeatureSupport.require (observed == fault && reprStr snapshot.cells == reprStr expected.cells)
        "path failure reason or complete source store changed on resume"
    | _ => throw (IO.userError "path failure resume changed outcome")


/-- Insert a fresh raw child below the original selected occurrence. The parent
keeps the exact requirement IDs and plan edges. This is retained IR test data,
not a claim about where inference attaches output coercions in surface groups. -/
private def auditRetainedGroup (entry : SourceCompilerFeatureSupport.Entry) : IO Unit := do
  let base := entry.cached.indexed.base
  let named ← match base.functions.find? (·.signature.key == entry.key) with
    | some named => pure named | none => throw (IO.userError "raw group caller missing")
  let caller := named.specialized
  let original := caller.function.typedBody
  let compilation : SourceCoreFunctions.Context := {
    plan := base.plan, owner := named.signature.key, globals := base.globals, administrativePrefix := 1,
    solvedRequirements := caller.function.solvedRequirements, internalReason := Word.zero }
  let indexed := entry.cached.indexed
  let representation := (SourceCoreCallableIndexedPrograms.markedRepresentation indexed.ancestry indexed.fuel indexed.layouts).atContext named.signature.key []
  let diagnostics ← match base.diagnostics with
    | some diagnostics => pure diagnostics.program | none => throw (IO.userError "raw group diagnostics missing")
  let diagnostics := match base.callableContext with
    | some native => {diagnostics with rootTable := native.diagnostics.rootTable}
    | none => diagnostics
  let own ← match diagnostics.base.find? named.signature.key with
    | some own => pure own | none => throw (IO.userError "raw group owner diagnostics missing")
  let mut localScope : Scope := []
  for binder in SourceCoreDataPlaces.declaredBinders original do
    if binder.name == "missing" then
      let native ← SourceCompilerFeatureSupport.get "raw group local type" (entry.cached.compatible.checked.catalog.project binder.scheme.body)
      localScope := (binder.id, native) :: localScope
  let scope := localScope ++ named.inputs.reverse.map (fun (binder, type) => (binder.id, type))
  let reasonAt := diagnostics.reasonAt named.signature.key
  let child := SourceCoreGeneralFunctions.lowerContextualExpression base.sourceProgram representation base.sourceProgram.signatures
    base.locals base.contexts own.assignments diagnostics compilation base.callableContext none none
  let policy := SourceCoreGeneralFunctions.callablePolicy base.callableContext []
  let mut count := 0
  for item in original.nodes do
    if let .expression node := item then
      if !node.coercions.isEmpty then
        if let .binary .. := node.form then
          let fresh : ExpressionId := ⟨⟨original.owner, 100000 + node.id.occurrence.index⟩⟩
          SourceCompilerFeatureSupport.require (original.lookupExpression? fresh |>.isNone) "raw group fresh ID collided"
          let inner := {rawNode node [] with id := fresh}
          let outer := {node with form := .group fresh}
          let source := {(SourceCoreEvidence.withNode original outer) with
            nodes := (SourceCoreEvidence.withNode original outer).nodes ++ [.expression inner]}
          SourceCompilerFeatureSupport.require (source.lookupExpression? node.id == some outer &&
            source.lookupExpression? fresh == some inner && outer.requirements == node.requirements &&
            outer.coercions == node.coercions && SourceCompilationPlan.ordinaryOwnedRequirements? outer == some [])
            "raw group lost exact retained metadata"
          let rawSource := SourceCoreEvidence.withNode source (rawNode outer [])
          let rootCode ← SourceCompilerFeatureSupport.get "actual sanitized group child" (child 150 rawSource scope outer.id reasonAt)
          let innerCode ← SourceCompilerFeatureSupport.get "actual sanitized inner subtree" (child 150 rawSource scope fresh reasonAt)
          let originalInner ← SourceCompilerFeatureSupport.get "original source inner subtree" (child 150 source scope fresh reasonAt)
          SourceCompilerFeatureSupport.require (rootCode == innerCode && innerCode == originalInner)
            "actual group/sanitizer changed child code"
          let lowered ← SourceCompilerFeatureSupport.get "actual retained group outer"
            (SourceCoreEvidence.lowerWithProjector base.sourceProgram representation.expressions.projectType caller compilation child
              150 source scope outer.id reasonAt policy)
          let prior ← SourceCompilerFeatureSupport.get "actual prior delegated outer"
            (SourceCoreEvidence.lowerWithProjector base.sourceProgram representation.expressions.projectType caller compilation child
              150 original scope node.id reasonAt policy)
          SourceCompilerFeatureSupport.require (lowered.isSome && lowered == prior)
            "retained group changed the full ordered native expression"
          let available ← SourceCompilerFeatureSupport.get "actual group evidence"
            (SourceCompilationPlan.resolveRuntimeEvidenceEnvironment base.sourceProgram caller.key caller.assumptions)
          let suffix ← SourceCompilerFeatureSupport.get "actual group suffix"
            (SourceCoreEvidence.applyCoercions base.sourceProgram representation.expressions.projectType compilation caller available scope outer policy rootCode outer.coercions)
          SourceCompilerFeatureSupport.require (lowered == some suffix) "group suffix code/order changed"
          let noneResult := SourceCoreEvidence.lowerWithProjector base.sourceProgram representation.expressions.projectType caller compilation
            (fun _ _ _ id _ => .error (.missingExpression id)) 150 rawSource scope outer.id reasonAt policy
          SourceCompilerFeatureSupport.require (match noneResult with | .ok none => true | _ => false)
            "empty group path must bypass before a rejecting child"
          count := count + 1
  SourceCompilerFeatureSupport.require (count == 1) "retained group fixture lacks one delegated occurrence"

def run : IO Unit := do
  let checked ← SourceCompilerFeatureSupport.get "raw group checked fixture" (checkProgram workspace 1024)
  for name in ["path", "late", "operand"] do
    auditRetainedGroup (← SourceCompilerFeatureSupport.compileNamed checked name)
  let operand ← SourceCompilerFeatureSupport.compileNamed checked "operand"
  for budget in [0, 41, 137, 500000] do
    let initial ← operand.audit [] budget
    let finished ← SourceCompilerFeatureSupport.get "raw group operand resume" (initial.resume 500000)
    match finished.observation with
    | .fault (.uninitializedLocal _) state =>
      SourceCompilerFeatureSupport.require
        (reprStr (state.heap.map fun cell => (cell.type, cell.value)) ==
          reprStr ([(.word, none)] : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)))
        "raw group operand fault did not skip every method allocation"
    | other => throw (IO.userError s!"raw group operand outcome changed: {reprStr other}")
  let box ← constructorFor checked "Box"
  let final ← constructorFor checked "Final"
  let broken ← constructorFor checked "Broken"
  let path ← SourceCompilerFeatureSupport.compileNamed checked "path"
  let late ← SourceCompilerFeatureSupport.compileNamed checked "late"
  let boxed := SourceTypedRuntime.Value.constructed box [.bool true]
  let output := SourceTypedRuntime.Value.constructed final [boxed]
  for budget in [0, 41, 137, 500000] do
    for input in [0, 1, 2] do
      for (entry, terminalFault) in [(path, false), (late, true)] do
        let initial ← entry.audit [SourceCompilerFeatureSupport.scalar input] budget
        let finished ← SourceCompilerFeatureSupport.get "raw group exact-artifact resume" (initial.resume 500000)
        let firstCells := [(.word, some (word input)), (.word, some (word input)), (.word, some (word input))]
        let secondCells := [(.bool, some (.bool (input == 1))),
          (.mapping .bool .word, some (.mapping .bool .word [])), (.word, some (word 0))]
        match finished.observation with
        | .done value state =>
          SourceCompilerFeatureSupport.require (!terminalFault && input == 1 && reprStr value == reprStr output)
            "retained group original artifact changed successful result"
          cells state (firstCells ++ secondCells ++ [(box.resultType, some boxed), (.word, some (word 31)),
            (final.resultType, some output)]) "all methods"
        | .fault (.uninitializedLocal binder) state =>
          let expectedName := if input == 0 then "firstGap" else if input == 2 then "secondGap" else "lastGap"
          let declarations := entry.cached.indexed.base.functions.flatMap
            (fun named => SourceCoreDataPlaces.declaredBinders named.specialized.function.typedBody)
          SourceCompilerFeatureSupport.require (declarations.any (fun declared => declared.id == binder && declared.name == expectedName))
            "retained group changed the actual first fault binder"
          if input == 0 then cells state (firstCells ++ [(.bool, none)]) "first method; suffix skipped"
          else if input == 2 then cells state (firstCells ++ secondCells ++ [(box.resultType, none)]) "middle method; suffix skipped"
          else
            SourceCompilerFeatureSupport.require (terminalFault && input == 1) "unexpected terminal method fault"
            cells state (firstCells ++ secondCells ++ [(box.resultType, some boxed), (.word, some (word 37)),
              (broken.resultType, none)]) "final method"
        | other => throw (IO.userError s!"raw group artifact outcome changed: {reprStr other}")
  path.checkResume [SourceCompilerFeatureSupport.scalar 1] (.constructed final [.constructed box [.bool true]]) 41
  faultResume path [.word Word.zero]
  faultResume path [.word (Word.ofNatModulo 2)]
  faultResume late [.word (Word.ofNatModulo 1)]
  faultResume operand []
  IO.println "raw groups: retained IR sanitizer/child/full suffix code equality, empty bypass, same-artifact ordered heaps/faults/public resume GREEN"

end Tests.SourceCoreCallableCoercionRawGroups
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableCoercionRawNamedCallAdmission
/-! The reached declaration's actual Valid witness closes ordinary raw-call
admission with unchanged caller type scopes, including residually open bodies.
The concrete formal consumers reuse catalog mutual meaning, ordered argument
Trees and actual catalog/method authority. No range proof is guessed from
admissibility, a native type, or the absence of signature predicates. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
namespace Tests.SourceCoreCallableCoercionRawNamedCallAdmission
open Solcore SourceSemantics SourceSemantics.CoreLowering Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableAncestryPairedLookup
open CallableCoercionExpressionCertificates CallableCoercionExpressionMeaning
open CallableCoercionRawNamedCallCertificates RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds

section Accepted
variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : SourceCoreCallableIndexedPrograms.Prepared checked} {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {compilerProgram : CheckedProgram}
  {headers : Inventory prepared.ancestry values ambient.definitions (Program.ofChecked compilerProgram)} {locations : Locations} {capturePrefix : Nat}
  {bodyCompilation : Header prepared.ancestry values ambient.definitions (Program.ofChecked compilerProgram) → SourceCoreFunctions.Context}
  {expressionSyntax : Header prepared.ancestry values ambient.definitions (Program.ofChecked compilerProgram) → ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  (owners : ((Program.ofChecked compilerProgram).functions.map (fun definition => definition.body.owner)).Nodup)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (missing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header ∈ headers, faults .controlEscapedFunction header.escaped)
  (prefixMatches : ∀ header ∈ headers, (bodyCompilation header).administrativePrefix = capturePrefix + 1)
  (profiles : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location}
      {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame},
      BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost →
      ProfileFor diagnosticPolicy headers header (bodyCompilation header) header.readFuel (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)


variable {compilation : SourceCoreFunctions.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {reasonAt : ExpressionId → Word} {readFuel fuel : Nat}
  (valid : CompatibleExpressionLiterals.ContextValid compilation.solvedRequirements context evidence)
  (sourceUnique : NodeOccurrencesUnique source)
  (callerUninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (callerMissing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  {project : Projector} {callerFunction : Specialized} {child : SourceCoreEvidence.Child}
  {scope : SourceCoreLocalCell.Scope} {id callee : ExpressionId} {arguments : List ExpressionId}
  {instantiation : DeclarationInstantiation} {policy : SourceCoreFunctions.CallablePolicy}
  {node : ExpressionNode} {output : Lowered}
  (receipt : Direct compilerProgram project callerFunction compilation child fuel source scope id callee arguments
    instantiation reasonAt policy node output)
  {header : Header prepared.ancestry values ambient.definitions (Program.ofChecked compilerProgram)}
  (reached : Reached receipt (headers := headers) header)
  (sourceTypes : RecursiveNamedExpressionCompilerCertificates.SourceTypes headers context)
  (sourceSignatures : context.signatures = (Program.ofChecked compilerProgram).signatures)
  (typed : ExpressionHasType source context id node.type)
  (children : DataExpressionSequence.Tree source
    (Expressions headers compilation readFuel source context compilation.solvedRequirements reasonAt)
    scope arguments (header.bindings.map (fun binder => binder.1.scheme.body)) receipt.loweredArguments)
  (nativeTypes : receipt.loweredArguments.map (·.type) = header.bindings.map Prod.snd)
  {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment} {actualContext : Core.Context}
  {before : Dynamic.Heap} {store : Store} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world administrative
    scope environment canonical ambient.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
  (installed : RecursiveNamedCatalog.Entry headers locations capturePrefix compilation.administrativePrefix
    scope mapping world before store canonical)

variable {raw : Workspace.RawWorkspace} {checkFuel : Nat}
  (checkedAccepted : checkProgram raw checkFuel = .ok compilerProgram)
  (definitions : prepared.layouts.definitions = ambient.definitions)
  (registered : prepared.ancestry.layout.frame.Registered ambient.definitions)
  {methods : CallableCoercionPathMeaning.Profiles (prepared := prepared) (values := values)
    (program := Program.ofChecked compilerProgram) (context := context) (evidence := evidence)}
  (methodUninitialized : ∀ method ∈ methods, ∀ id location,
    faults (.uninitializedLocation location) (method.diagnostics.reasonAt method.named.signature.key id))
  (methodMissing : ∀ method ∈ methods, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((method.diagnostics.reasonAt method.named.signature.key id).add tag))
  {calls : List CallableCoercionSpine.Call}
  (emitted : CallableCoercionMethodEntries.Emitted compilerProgram project compilation callerFunction receipt.available
    scope node policy ξ receipt.operand methods output calls)
  (steps : methods.map (·.step) = node.coercions)
  (chain : CallableCoercionPathMeaning.Chain node.rawType receipt.operand.type methods node.type output.type)
  (ledger : context.solvedRequirements = callerFunction.function.solvedRequirements)
  (methodEntry : CallableCoercionMethodEntries.Entry methods ambient.definitions actual mapping world before store)


include extension definitions registered faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles
  valid sourceUnique callerUninitialized callerMissing reached sourceTypes sourceSignatures typed children nativeTypes
  environments heaps locals agrees actualTyped installed methodUninitialized methodMissing emitted steps chain methodEntry checkedAccepted owners ledger in
theorem accepted_preserves
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : Dynamic.ExpressionEvaluatesOutcome (Program.ofChecked compilerProgram) context evidence source environment before id outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (output.expression.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        node.type output.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (CallableCoercionMethodEntries.Entry methods ambient.definitions actual finalMap finalWorld after finalStore) := by
  obtain ⟨certified⟩ := CallableCoercionRawNamedCallAdmission.of_tree receipt reached sourceTypes sourceUnique sourceSignatures typed children nativeTypes
  exact CallableCoercionRawNamedCallMeaning.preserves
    (functions := functions) (extension := extension) (definitions := definitions) (registered := registered)
    (faithful := faithful) (observations := observations) (runtimeViews := runtimeViews) (uninitialized := uninitialized)
    (missing := missing) (escaped := escaped) (prefixMatches := prefixMatches) (profiles := profiles)
    (valid := valid) (callerUninitialized := callerUninitialized) (callerMissing := callerMissing) (receipt := receipt)
    (certified := certified) (environments := environments) (heaps := heaps) (locals := locals)
    (agrees := agrees) (actualTyped := actualTyped) (installed := installed) (methodUninitialized := methodUninitialized)
    (methodMissing := methodMissing) (emitted := emitted) (steps := steps) (chain := chain)
    (methodEntry := methodEntry) (checkedAccepted := checkedAccepted) (owners := owners) (sourceUnique := sourceUnique)
    (ledger := ledger) trace

include extension definitions registered faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles
  valid sourceUnique callerUninitialized callerMissing reached sourceTypes sourceSignatures typed children nativeTypes
  environments heaps locals agrees actualTyped installed methodUninitialized methodMissing emitted steps chain methodEntry in
theorem accepted_reflects
    {value : Value} {finalStore : Store}
    (completed : Evaluates actual store (output.expression.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome (Program.ofChecked compilerProgram) context evidence source environment before id outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        node.type output.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (CallableCoercionMethodEntries.Entry methods ambient.definitions actual finalMap finalWorld after finalStore) := by
  obtain ⟨certified⟩ := CallableCoercionRawNamedCallAdmission.of_tree receipt reached sourceTypes sourceUnique sourceSignatures typed children nativeTypes
  exact CallableCoercionRawNamedCallMeaning.reflects
    (functions := functions) (extension := extension) (definitions := definitions) (registered := registered)
    (faithful := faithful) (observations := observations) (runtimeViews := runtimeViews) (uninitialized := uninitialized)
    (missing := missing) (escaped := escaped) (prefixMatches := prefixMatches) (profiles := profiles)
    (valid := valid) (callerUninitialized := callerUninitialized) (callerMissing := callerMissing) (receipt := receipt)
    (certified := certified) (environments := environments) (heaps := heaps) (locals := locals)
    (agrees := agrees) (actualTyped := actualTyped) (installed := installed) (methodUninitialized := methodUninitialized)
    (methodMissing := methodMissing) (emitted := emitted) (steps := steps) (chain := chain)
    (methodEntry := methodEntry) completed
end Accepted

section OpenScope
private def openContext (signatures : ProgramSignatures) : SourceSemantics.Context :=
  {SourceSemantics.Context.ofSignatures signatures with
    typeVariables := [⟨7⟩], residualTypeVariables := true}

/-- An actual instantiated header remains valid in a context with a nonempty
flexible scope and residual variables. Neither scope is rewritten to closed. -/
theorem actual_open_header {checked : CallableAncestryPairedLookup.Checked}
    {base : CallableAncestryPairedLookup.Base checked} {prepared : SourceCoreCallableIndexedAncestry.Prepared base}
    {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    {program : SourceSemantics.Program} (header : RecursiveNamedCatalog.Header prepared values ambient.definitions program) :
    SourceSemantics.DeclarationInstantiation.Valid (openContext program.signatures) header.instantiation ∧
      (openContext program.signatures).typeVariables = [⟨7⟩] ∧
      (openContext program.signatures).residualTypeVariables = true := by
  refine ⟨CallableCoercionRawNamedCallAdmission.header_valid header rfl ?_, rfl, rfl⟩
  constructor
  · exact List.nodup_nil
  · intro parameter member
    cases member
end OpenScope

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Marker<T> {}", "impl Marker<Word> {}",
    "trait Coerce<From, To> { function coerce(value: From) returns (To); }",
    "impl Coerce<Word, Bool> { function coerce(value: Word) returns (Bool) { let seen = value; if (value == 0) { let coercionGap: Bool; return coercionGap; } return value == 1; } }",
    "function choose<A, B>(left: A, right: B) returns (B) { return right; }",
    "function relay<T>(value: T) returns (T) { return value; }",
    "function fixed(value: Word) returns (Word) { return choose(true, value); }",
    "function fixedRelay(value: Word) returns (Word) { return choose(true, relay(value)); }",
    "function fixedFail() returns (Word) { let before: Word = 61; let rawGap: Word; return rawGap; }",
    "function convert(value: Word) returns (Bool) { return fixed(value); }",
    "function nested(value: Word) returns (Bool) { return fixedRelay(value); }",
    "function early() returns (Bool) { return fixedFail(); }",
    "function emptySelected(value: Word) returns (Word) where Word: Marker { return fixed(value); }"
  ]}] }
private def require := SourceCompilerFeatureSupport.require
private def word (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def cells (state : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) : IO Unit :=
  require (reprStr (state.heap.map fun cell => (cell.type, cell.value)) == reprStr expected)
    s!"open admission ordered cells changed: {reprStr state.heap}"

/-- Audit actual retained two-parameter metadata, full selected records, and
unchanged declaration contexts. The parser/checker and cached compiler run here;
these observations do not themselves manufacture a semantic Header. -/
private def inspect (entry : SourceCompilerFeatureSupport.Entry) (genericExpected : Bool) (pathExpected : Nat) : IO Unit := do
  let base := entry.cached.indexed.base
  let mut genericCount := 0
  let mut pathCount := 0
  for named in base.functions do
    let selected ← SourceCompilerFeatureSupport.get "admission complete selected record"
      (SourceCompilationPlan.exactSpecialization base.plan named.signature.key)
    require (selected == named.specialized) "admission selected record changed"
    let context := declarationContext base.sourceProgram.signatures selected.function.typedBody.owner []
      selected.assumptions selected.function.solvedRequirements
    require (context.residualTypeVariables && context.typeVariables.isEmpty && context.typeParameters.isEmpty &&
      context.solvedRequirements == selected.function.solvedRequirements && context.assumptions == selected.assumptions)
      "actual declaration context was silently closed or reordered"
    for item in selected.function.typedBody.nodes do
      if let .expression node := item then
        if let .call _ arguments (.declaration instantiation) := node.form then
          let target ← SourceCompilerFeatureSupport.get "admission target"
            (SourceCompilationPlan.exactInstantiationKey base.plan instantiation)
          let key ← SourceCompilerFeatureSupport.get "admission edge"
            (SourceCompilationPlan.exactCallKey base.plan named.signature.key node.id target)
          let callee ← SourceCompilerFeatureSupport.get "admission callee"
            (SourceCompilationPlan.exactSpecialization base.plan key)
          require (instantiation == CallableNamedCanonicalOrder.retainedInstantiation callee &&
            arguments.length == callee.function.typedBody.inputs.length)
            "admission full original instantiation/domain/order changed"
          if instantiation.parameterSubstitution.length == 2 then
            require (instantiation.parameterSubstitution.map Prod.fst == (callee.parameterSubstitution.map Prod.fst).reverse &&
              instantiation.parameterSubstitution.map Prod.fst != callee.parameterSubstitution.map Prod.fst &&
              instantiation.parameterSubstitution.map Prod.snd == [.word, .bool] && instantiation.predicates.isEmpty)
              "two-parameter retained reverse order/complete values changed"
            genericCount := genericCount + 1
          if !node.coercions.isEmpty then
            require (node.rawType == .word && node.type == .bool && node.coercions.length == 1 && callee.assumptions.isEmpty)
              "ordinary raw result/output path boundary changed"
            pathCount := pathCount + 1
  require ((genericCount > 0) == genericExpected) "actual generic ordinary callee disappeared"
  require (pathCount == pathExpected) "actual raw call output path count changed"

private def gap (entry : SourceCompilerFeatureSupport.Entry) (name : String) : IO Resolved.LocalId := do
  let binders := entry.cached.indexed.base.functions.flatMap fun named =>
    SourceCoreDataPlaces.declaredBinders named.specialized.function.typedBody
  match binders.filter (·.name == name) with
  | [binder] => pure binder.id
  | _ => throw (IO.userError s!"open admission gap {name} is not unique")

private def faultResume (entry : SourceCompilerFeatureSupport.Entry) (arguments : List SourceCoreExecution.Value) : IO Unit := do
  let artifact ← entry.execution.open
  let initial ← SourceCompilerFeatureSupport.boot artifact
  let finished ← SourceCompilerFeatureSupport.get "open admission fault"
    (← initial.run entry.key arguments SourceCompilerFeatureSupport.executionOptions)
  let (fault, session) ← match finished with
    | .failed fault session => pure (fault, session)
    | _ => throw (IO.userError "open admission expected fault")
  let expected ← SourceCompilerFeatureSupport.get "open admission fault snapshot" (← session.snapshot 2048)
  for budget in [0, 41, 137] do
    let started ← SourceCompilerFeatureSupport.get "open admission suspend"
      (← initial.run entry.key arguments {SourceCompilerFeatureSupport.executionOptions with executionFuel := budget})
    let resumed ← match started with
      | .outOfFuel checkpoint => checkpoint.resume 500000 2048
      | outcome => pure outcome
    match resumed with
    | .failed observed session =>
      let snapshot ← SourceCompilerFeatureSupport.get "open admission resumed snapshot" (← session.snapshot 2048)
      require (observed == fault && reprStr snapshot.cells == reprStr expected.cells)
        "open admission public fault/full snapshot changed on resume"
    | _ => throw (IO.userError "open admission fault resume changed outcome")

def run : IO Unit := do
  let program ← SourceCompilerFeatureSupport.get "open admission checker" (checkProgram workspace 1024)
  let convert ← SourceCompilerFeatureSupport.compileNamed program "convert"
  let nested ← SourceCompilerFeatureSupport.compileNamed program "nested"
  let early ← SourceCompilerFeatureSupport.compileNamed program "early"
  let empty ← SourceCompilerFeatureSupport.compileNamed program "emptySelected"
  inspect convert true 1
  inspect nested true 1
  inspect early false 1
  inspect empty true 0
  let convertGap ← gap convert "coercionGap"
  let nestedGap ← gap nested "coercionGap"
  let rawGap ← gap early "rawGap"
  for budget in [0, 41, 137, 500000] do
    for input in [0, 1, 2] do
      for (entry, extra, expectedGap) in [(convert, false, convertGap), (nested, true, nestedGap)] do
        let started ← entry.audit [SourceCompilerFeatureSupport.scalar input] budget
        let finished ← SourceCompilerFeatureSupport.get "open admission resume" (started.resume 500000)
        let initial := [(.word, some (word input)), (.word, some (word input))] ++
          (if extra then [(.word, some (word input))] else []) ++
          [(.bool, some (.bool true)), (.word, some (word input)), (.word, some (word input)), (.word, some (word input))]
        match finished.observation with
        | .done value state =>
          require (input != 0 && reprStr value == reprStr (SourceTypedRuntime.Value.bool (input == 1)))
            "open admission successful result changed"
          cells state initial
        | .fault (.uninitializedLocal actualGap) state =>
          require (input == 0 && actualGap == expectedGap) "open admission unexpected coercion fault"
          cells state (initial ++ [(.bool, none)])
        | other => throw (IO.userError s!"open admission unexpected result: {reprStr other}")
    let started ← early.audit [] budget
    let finished ← SourceCompilerFeatureSupport.get "open admission early resume" (started.resume 500000)
    match finished.observation with
    | .fault (.uninitializedLocal actualGap) state =>
      require (actualGap == rawGap) "open admission raw first fault changed"
      cells state [(.word, some (word 61)), (.word, none)]
    | other => throw (IO.userError s!"open admission early result: {reprStr other}")
    let started ← empty.audit [SourceCompilerFeatureSupport.scalar 17] budget
    let finished ← SourceCompilerFeatureSupport.get "open admission empty resume" (started.resume 500000)
    match finished.observation with
    | .done value state =>
      require (reprStr value == reprStr (word 17)) "open admission empty result changed"
      cells state [(.word, some (word 17)), (.word, some (word 17)), (.bool, some (.bool true)), (.word, some (word 17))]
    | other => throw (IO.userError s!"open admission empty result: {reprStr other}")
  convert.checkResume [SourceCompilerFeatureSupport.scalar 1] (.bool true) 41
  nested.checkResume [SourceCompilerFeatureSupport.scalar 2] (.bool false) 41
  empty.checkResume [SourceCompilerFeatureSupport.scalar 17] (.word (Word.ofNatModulo 17)) 41
  faultResume convert [.word Word.zero]
  faultResume nested [.word Word.zero]
  faultResume early []
  IO.println "raw named admission: actual open declaration contexts/full reversed generic metadata, raw/output/empty paths, ordered full cells and public resume GREEN"

end Tests.SourceCoreCallableCoercionRawNamedCallAdmission
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableCoercionRawNamedCallBuiltinArguments
/-! Actual builtin argument callbacks close the final raw-call argument Trees.
The concrete semantic consumers retain the original parent requirements/output
path, reached full header, actual BodyState profiles and catalog/method Entry.
The source context keeps its residual flag. Constructor ranges cover every raw
substitution entry; no raw/child/body runtime law or source pre-run is an input. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
namespace Tests.SourceCoreCallableCoercionRawNamedCallBuiltinArguments
open Solcore SourceSemantics SourceSemantics.CoreLowering Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableAncestryPairedLookup
open CallableCoercionExpressionCertificates CallableCoercionExpressionMeaning
open CallableCoercionRawNamedCallCertificates RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds

section Accepted
variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : SourceCoreCallableIndexedPrograms.Prepared checked} {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {compilerProgram : CheckedProgram}
  {headers : Inventory prepared.ancestry values ambient.definitions (Program.ofChecked compilerProgram)} {locations : Locations} {capturePrefix : Nat}
  {bodyCompilation : Header prepared.ancestry values ambient.definitions (Program.ofChecked compilerProgram) → SourceCoreFunctions.Context}
  {expressionSyntax : Header prepared.ancestry values ambient.definitions (Program.ofChecked compilerProgram) → ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  (owners : ((Program.ofChecked compilerProgram).functions.map (fun definition => definition.body.owner)).Nodup)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (missing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header ∈ headers, faults .controlEscapedFunction header.escaped)
  (prefixMatches : ∀ header ∈ headers, (bodyCompilation header).administrativePrefix = capturePrefix + 1)
  (profiles : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location}
      {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame},
      BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost →
      ProfileFor diagnosticPolicy headers header (bodyCompilation header) header.readFuel (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)


variable {compilation : SourceCoreFunctions.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {reasonAt : ExpressionId → Word} {readFuel fuel : Nat}
  (valid : CompatibleExpressionLiterals.ContextValid compilation.solvedRequirements context evidence)
  (sourceUnique : NodeOccurrencesUnique source)
  (callerUninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (callerMissing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  {project : Projector} {callerFunction : Specialized} {child : SourceCoreEvidence.Child}
  {scope : SourceCoreLocalCell.Scope} {id callee : ExpressionId} {arguments : List ExpressionId}
  {instantiation : DeclarationInstantiation} {policy : SourceCoreFunctions.CallablePolicy}
  {node : ExpressionNode} {output : Lowered}
  (receipt : Direct compilerProgram project callerFunction compilation child fuel source scope id callee arguments
    instantiation reasonAt policy node output)
  {header : Header prepared.ancestry values ambient.definitions (Program.ofChecked compilerProgram)}
  (reached : Reached receipt (headers := headers) header)
  (programTyped : ProgramWellFormed (Program.ofChecked compilerProgram))
  (nativeProjections : ∀ memberHeader, memberHeader ∈ headers →
    (memberHeader.bindings.map (fun binding => binding.1.scheme.body)).mapM values.checked.catalog.project =
      .ok (memberHeader.bindings.map Prod.snd))
  (ordinaryEvidence : ∀ memberHeader, memberHeader ∈ headers → memberHeader.function.evidence = [])
  (sourceSignatures : context.signatures = (Program.ofChecked compilerProgram).signatures)
  (nativeSignatures : context.signatures = values.checked.signatures)
  (typed : ExpressionHasType source context id node.type)
  (lexical : context.typeVariables = [])
  (constructorRanges : CompatibleExpressionInstantiationLaws.ConstructorRanges source (CompatibleExpressionBuiltins.Syntax source))
  {representation : SourceCoreGeneralFunctions.Representation} {signatures : ProgramSignatures}
  {localCatalog : SourceCoreLocalPolymorphism.Catalog} {parents : List SourceCoreLocalEvidence.Prepared}
  {assignments : SourceCoreAssignmentFaultSites.Table} {diagnostics : SourceCoreDataPlaceFaultSites.Program}
  {native : SourceCoreGeneralFunctions.CallableContext} {parent : Option SourceCoreLocalEvidence.Prepared}
  {skipInitializer : Option ExpressionId}
  (childEq : child = SourceCoreGeneralFunctions.lowerContextualExpression compilerProgram representation signatures localCatalog parents
    assignments diagnostics compilation (some native) parent skipInitializer)
  (syntaxTrees : ∀ argument, argument ∈ arguments → CompatibleExpressionBuiltins.Syntax source argument)
  (ordinary : CompatibleExpressionBuiltins.Ordinary source localCatalog compilation.owner)
  (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
  (readPolicy : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
  (lowerPolicy : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
  (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
  {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment} {actualContext : Core.Context}
  {before : Dynamic.Heap} {store : Store} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world administrative
    scope environment canonical ambient.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
  (installed : RecursiveNamedCatalog.Entry headers locations capturePrefix compilation.administrativePrefix
    scope mapping world before store canonical)

variable {raw : Workspace.RawWorkspace} {checkFuel : Nat}
  (checkedAccepted : checkProgram raw checkFuel = .ok compilerProgram)
  (definitions : prepared.layouts.definitions = ambient.definitions)
  (registered : prepared.ancestry.layout.frame.Registered ambient.definitions)
  {methods : CallableCoercionPathMeaning.Profiles (prepared := prepared) (values := values)
    (program := Program.ofChecked compilerProgram) (context := context) (evidence := evidence)}
  (methodUninitialized : ∀ method ∈ methods, ∀ id location,
    faults (.uninitializedLocation location) (method.diagnostics.reasonAt method.named.signature.key id))
  (methodMissing : ∀ method ∈ methods, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((method.diagnostics.reasonAt method.named.signature.key id).add tag))
  {calls : List CallableCoercionSpine.Call}
  (emitted : CallableCoercionMethodEntries.Emitted compilerProgram project compilation callerFunction receipt.available
    scope node policy ξ receipt.operand methods output calls)
  (steps : methods.map (·.step) = node.coercions)
  (chain : CallableCoercionPathMeaning.Chain node.rawType receipt.operand.type methods node.type output.type)
  (ledger : context.solvedRequirements = callerFunction.function.solvedRequirements)
  (methodEntry : CallableCoercionMethodEntries.Entry methods ambient.definitions actual mapping world before store)


include extension definitions registered faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles
  valid sourceUnique callerUninitialized callerMissing reached programTyped nativeProjections ordinaryEvidence sourceSignatures nativeSignatures typed lexical constructorRanges childEq syntaxTrees ordinary declarations readPolicy lowerPolicy leafPolicy
  environments heaps locals agrees actualTyped installed methodUninitialized methodMissing emitted steps chain methodEntry checkedAccepted owners ledger in
theorem accepted_preserves
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : Dynamic.ExpressionEvaluatesOutcome (Program.ofChecked compilerProgram) context evidence source environment before id outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (output.expression.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        node.type output.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (CallableCoercionMethodEntries.Entry methods ambient.definitions actual finalMap finalWorld after finalStore) := by
  obtain ⟨certified⟩ := CallableCoercionRawNamedCallBuiltinArguments.of_program receipt childEq reached programTyped nativeProjections ordinaryEvidence sourceUnique sourceSignatures nativeSignatures typed (CompatibleExpressionInstantiationLaws.ConstructorLaw.of_ranges lexical constructorRanges) syntaxTrees ordinary declarations readPolicy lowerPolicy leafPolicy
  exact CallableCoercionRawNamedCallMeaning.preserves
    (functions := functions) (extension := extension) (definitions := definitions) (registered := registered)
    (faithful := faithful) (observations := observations) (runtimeViews := runtimeViews) (uninitialized := uninitialized)
    (missing := missing) (escaped := escaped) (prefixMatches := prefixMatches) (profiles := profiles)
    (valid := valid) (callerUninitialized := callerUninitialized) (callerMissing := callerMissing) (receipt := receipt)
    (certified := certified) (environments := environments) (heaps := heaps) (locals := locals)
    (agrees := agrees) (actualTyped := actualTyped) (installed := installed) (methodUninitialized := methodUninitialized)
    (methodMissing := methodMissing) (emitted := emitted) (steps := steps) (chain := chain)
    (methodEntry := methodEntry) (checkedAccepted := checkedAccepted) (owners := owners) (sourceUnique := sourceUnique)
    (ledger := ledger) trace

include extension definitions registered faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles
  valid sourceUnique callerUninitialized callerMissing reached programTyped nativeProjections ordinaryEvidence sourceSignatures nativeSignatures typed lexical constructorRanges childEq syntaxTrees ordinary declarations readPolicy lowerPolicy leafPolicy
  environments heaps locals agrees actualTyped installed methodUninitialized methodMissing emitted steps chain methodEntry in
theorem accepted_reflects
    {value : Value} {finalStore : Store}
    (completed : Evaluates actual store (output.expression.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome (Program.ofChecked compilerProgram) context evidence source environment before id outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        node.type output.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (CallableCoercionMethodEntries.Entry methods ambient.definitions actual finalMap finalWorld after finalStore) := by
  obtain ⟨certified⟩ := CallableCoercionRawNamedCallBuiltinArguments.of_program receipt childEq reached programTyped nativeProjections ordinaryEvidence sourceUnique sourceSignatures nativeSignatures typed (CompatibleExpressionInstantiationLaws.ConstructorLaw.of_ranges lexical constructorRanges) syntaxTrees ordinary declarations readPolicy lowerPolicy leafPolicy
  exact CallableCoercionRawNamedCallMeaning.reflects
    (functions := functions) (extension := extension) (definitions := definitions) (registered := registered)
    (faithful := faithful) (observations := observations) (runtimeViews := runtimeViews) (uninitialized := uninitialized)
    (missing := missing) (escaped := escaped) (prefixMatches := prefixMatches) (profiles := profiles)
    (valid := valid) (callerUninitialized := callerUninitialized) (callerMissing := callerMissing) (receipt := receipt)
    (certified := certified) (environments := environments) (heaps := heaps) (locals := locals)
    (agrees := agrees) (actualTyped := actualTyped) (installed := installed) (methodUninitialized := methodUninitialized)
    (methodMissing := methodMissing) (emitted := emitted) (steps := steps) (chain := chain)
    (methodEntry := methodEntry) completed
end Accepted


private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Marker<T> {}", "impl Marker<Word> {}", "enum Box<T> { Box(T) }",
    "trait Coerce<From, To> { function coerce(value: From) returns (To); }",
    "impl Coerce<Word, integer> { function coerce(value: Word) returns (integer) { let seen = value; if (value == 0) { let coercionGap: integer; return coercionGap; } return wordToInteger(value); } }",
    "function choose<A, B>(unused: A, value: B) returns (B) { return value; }",
    "function relay<T>(value: T) returns (T) { return value; }",
    "function last(a: Word, b: Word, c: Word) returns (Word) { return c; }",
    "function one() returns (Word) { return 1; }",
    "function converted(value: Word) returns (integer) { return choose(integerEq(wordToInteger(value), wordToInteger(1)), wordFromInteger(wordToInteger(value))); }",
    "function lazy(value: Word) returns (integer) { let rawGap: Word; return choose(!false, value == 1 ? (value + 0) : rawGap); }",
    "function first(value: Word) returns (integer) { let firstGap: Bool; let secondGap: Word; return choose(firstGap, wordFromInteger(wordToInteger(secondGap))); }",
    "function second(value: Word) returns (integer) { let secondGap: Word; return choose(integerEq(wordToInteger(value), wordToInteger(1)), wordFromInteger(wordToInteger(secondGap))); }",
    "function paired(value: Word) returns (integer) { return choose((wordFromInteger(wordToInteger(value)), true), wordFromInteger(wordToInteger(value))); }",
    "function empty(value: Word) returns (integer) where Word: Marker { return choose(false, wordToInteger(value + 1)); }",
    "function repeated(value: Word) returns (integer) { return last(wordFromInteger(wordToInteger(value)), wordFromInteger(wordToInteger(value)), wordFromInteger(wordToInteger(value))); }",
    "function zero() returns (integer) { return one(); }",
    "function single(value: Word) returns (integer) { return relay(wordFromInteger(wordToInteger(value))); }",
    "function boxed(value: Word) returns (integer) { return choose(Box(wordToInteger(value)), wordFromInteger(wordToInteger(value))); }",
    "function indexed(m: mapping(Bool => Word), value: Word) returns (integer) { return choose(integerEq(wordToInteger(value), wordToInteger(1)), m[integerEq(wordToInteger(value), wordToInteger(1))]); }",
    "function dataFault(value: Word) returns (integer) { let payloadGap: Word; return choose(Box(wordToInteger(payloadGap)), value); }",
    "function keyFault(m: mapping(Bool => Word)) returns (integer) { let keyGap: Bool; return choose(false, m[keyGap]); }"
  ]}] }
private def require := SourceCompilerFeatureSupport.require
private def get {α ε : Type} [Repr ε] := @SourceCompilerFeatureSupport.get α ε _
private def word (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def cells (state : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) : IO Unit :=
  require (reprStr (state.heap.map fun cell => (cell.type, cell.value)) == reprStr expected)
    s!"builtin arguments ordered cells changed: {reprStr state.heap}"

private def builtinSyntax (source : TypedSource) : Nat → ExpressionId → Bool
  | 0, _ => false
  | fuel + 1, id => match source.lookupExpression? id with
    | none => false
    | some node => match node.form with
      | .literal _ | .integerLiteral _ _ | .reference _ (.builtinBoolean _) | .reference _ (.local _) => true
      | .group inner | .unary _ inner => builtinSyntax source fuel inner
      | .tuple [left, right] | .binary left _ right => builtinSyntax source fuel left && builtinSyntax source fuel right
      | .conditional condition left right => builtinSyntax source fuel condition && builtinSyntax source fuel left && builtinSyntax source fuel right
      | .call _ arguments (.builtinFunction _) | .constructor _ arguments => arguments.all (builtinSyntax source fuel)
      | .member base _ _ => builtinSyntax source fuel base
      | .index base key => builtinSyntax source fuel base && builtinSyntax source fuel key
      | _ => false

/-- Re-enter the production contextual callback at the actual final lexical
scope. Check complete selected metadata and exactly the ordered argument code;
this runtime audit does not manufacture source typing or a semantic Header. -/
private def inspect (entry : SourceCompilerFeatureSupport.Entry) (arity pathCount : Nat) : IO Unit := do
  let indexed := entry.cached.indexed
  let base := indexed.base
  let named ← match base.functions.find? (·.signature.key == entry.key) with
    | some named => pure named | none => throw (IO.userError "builtin arguments caller missing")
  let caller := named.specialized
  let source := caller.function.typedBody
  let context := declarationContext base.sourceProgram.signatures source.owner [] caller.assumptions caller.function.solvedRequirements
  require (context.residualTypeVariables && context.typeVariables.isEmpty && context.solvedRequirements == caller.function.solvedRequirements)
    "builtin arguments actual caller context changed"
  let scope ← get "builtin arguments scope" ((SourceCoreDataPlaces.declaredBinders source).reverse.mapM fun binder => do
    let type ← entry.cached.compatible.checked.catalog.project binder.scheme.body
    pure (binder.id, type))
  let compilation : SourceCoreFunctions.Context := {
    plan := base.plan, owner := named.signature.key, globals := base.globals, administrativePrefix := 1,
    solvedRequirements := caller.function.solvedRequirements, internalReason := Word.zero }
  let representation := (SourceCoreCallableIndexedPrograms.markedRepresentation indexed.ancestry indexed.fuel indexed.layouts).atContext named.signature.key []
  let diagnostics ← match base.diagnostics with
    | some diagnostics => pure diagnostics.program | none => throw (IO.userError "builtin arguments diagnostics missing")
  let diagnostics := match base.callableContext with
    | some native => {diagnostics with rootTable := native.diagnostics.rootTable} | none => diagnostics
  let own ← match diagnostics.base.find? named.signature.key with
    | some own => pure own | none => throw (IO.userError "builtin arguments own diagnostics missing")
  let child := SourceCoreGeneralFunctions.lowerContextualExpression base.sourceProgram representation base.sourceProgram.signatures
    base.locals base.contexts own.assignments diagnostics compilation base.callableContext none none
  let policy := SourceCoreGeneralFunctions.callablePolicy base.callableContext []
  let reasonAt := diagnostics.reasonAt named.signature.key
  let available ← get "builtin arguments available" (SourceCompilationPlan.resolveRuntimeEvidenceEnvironment base.sourceProgram caller.key caller.assumptions)
  let mut count := 0
  for item in source.nodes do
    if let .expression node := item then
      if let .call callee arguments (.declaration instantiation) := node.form then
        require (arguments.length == arity && arguments.all (builtinSyntax source 100) && node.coercions.length == pathCount)
          s!"builtin arguments original syntax/arity/path changed: key={reprStr entry.key}, args={reprStr arguments}, builtin={reprStr (arguments.map (builtinSyntax source 100))}, path={node.coercions.length}"
        discard <| get "builtin arguments callee" (SourceCompilationPlan.validateDirectDeclarationCallee source node.id callee instantiation)
        let target ← get "builtin arguments target" (SourceCompilationPlan.exactInstantiationKey base.plan instantiation)
        let key ← get "builtin arguments edge" (SourceCompilationPlan.exactCallKey base.plan compilation.owner node.id target)
        let selected ← get "builtin arguments record" (SourceCompilationPlan.exactSpecialization base.plan key)
        require (instantiation == CallableNamedCanonicalOrder.retainedInstantiation selected && selected.assumptions.isEmpty &&
          instantiation.parameterSubstitution.map Prod.fst == (selected.parameterSubstitution.map Prod.fst).reverse &&
          selected.function.typedBody.inputs.length == arity)
          "builtin arguments full original metadata/order changed"
        let dictionary ← get "builtin arguments dictionary" (SourceCompilationPlan.exactDirectCallRuntimeEvidence caller node available instantiation)
        require dictionary.isEmpty "builtin arguments ordinary dictionary changed"
        let (signature, index) ← match base.globals.zipIdx.filter (fun row => decide (row.1.key = key)) with
          | [row] => pure row | _ => throw (IO.userError "builtin arguments actual global not singleton")
        let codes ← get "builtin arguments ordered mapM" (arguments.mapM (fun argument => child 150 source scope argument reasonAt))
        let sourceTypes ← get "builtin arguments raw types" (selected.function.typedBody.inputs.mapM fun binder =>
          entry.cached.compatible.checked.catalog.project binder.scheme.body)
        require (codes.map (·.type) == sourceTypes && signature.parameterType == (SourceCoreCalls.packArguments codes).type)
          "builtin arguments actual native vector changed"
        let raw : SourceCoreBasic.LoweredExpr := ⟨signature.resultType, SourceCoreCalls.call signature
          (scope.length + compilation.administrativePrefix + index) (SourceCoreCalls.packArguments codes).expression compilation.internalReason⟩
        let expected ← get "builtin arguments suffix" (SourceCoreEvidence.applyCoercions base.sourceProgram representation.expressions.projectType
          compilation caller available scope node policy raw node.coercions)
        let result ← get "builtin arguments actual outer" (SourceCoreEvidence.lowerWithProjector base.sourceProgram representation.expressions.projectType
          caller compilation child 150 source scope node.id reasonAt policy)
        require (result == some expected) "builtin arguments actual parent code changed"
        let nativeContext := SourceCoreLocalCell.coreContext scope ++ named.signature.parameterType ::
          (base.globals.map SourceCoreCalls.Signature.referenceType ++ [.cell indexed.ancestry.layout.frame.type])
        require (Core.infer? nativeContext expected.expression indexed.layouts.definitions == some (LanguageResult.resultType expected.type))
          "builtin arguments actual native code is ill typed"
        count := count + 1
  require (count == 1) "builtin arguments reached direct site missing"

private def gap (entry : SourceCompilerFeatureSupport.Entry) (name : String) : IO Resolved.LocalId := do
  let binders := entry.cached.indexed.base.functions.flatMap fun named =>
    SourceCoreDataPlaces.declaredBinders named.specialized.function.typedBody
  match binders.filter (·.name == name) with
  | [binder] => pure binder.id
  | _ => throw (IO.userError s!"builtin arguments gap {name} is not unique")

private def faultResume (entry : SourceCompilerFeatureSupport.Entry) (arguments : List SourceCoreExecution.Value) : IO Unit := do
  let artifact ← entry.execution.open
  let initial ← SourceCompilerFeatureSupport.boot artifact
  let finished ← SourceCompilerFeatureSupport.get "builtin arguments fault"
    (← initial.run entry.key arguments SourceCompilerFeatureSupport.executionOptions)
  let (fault, session) ← match finished with
    | .failed fault session => pure (fault, session)
    | _ => throw (IO.userError "builtin arguments expected fault")
  let expected ← SourceCompilerFeatureSupport.get "builtin arguments fault snapshot" (← session.snapshot 2048)
  for budget in [0, 41, 137] do
    let started ← SourceCompilerFeatureSupport.get "builtin arguments suspend"
      (← initial.run entry.key arguments {SourceCompilerFeatureSupport.executionOptions with executionFuel := budget})
    let resumed ← match started with
      | .outOfFuel checkpoint => checkpoint.resume 500000 2048
      | outcome => pure outcome
    match resumed with
    | .failed observed session =>
      let snapshot ← SourceCompilerFeatureSupport.get "builtin arguments resumed snapshot" (← session.snapshot 2048)
      require (observed == fault && reprStr snapshot.cells == reprStr expected.cells)
        "builtin arguments public fault/full snapshot changed on resume"
    | _ => throw (IO.userError "builtin arguments fault resume changed outcome")


/-- Constructor and mapping-key children use the same original contextual
callback. Expected heaps retain raw constructor metadata and duplicate entries. -/
private def dataCases (program : CheckedProgram) : IO Unit := do
  let data ← SourceCompilerFeatureSupport.compileNamed program "boxed"
  let indexed ← SourceCompilerFeatureSupport.compileNamed program "indexed"
  let dataFault ← SourceCompilerFeatureSupport.compileNamed program "dataFault"
  let keyFault ← SourceCompilerFeatureSupport.compileNamed program "keyFault"
  for entry in [data, indexed, dataFault, keyFault] do inspect entry 2 1
  let named ← match data.cached.indexed.base.functions.find? (·.signature.key == data.key) with
    | some named => pure named | none => throw (IO.userError "builtin arguments data root missing")
  let constructor ← match named.specialized.function.typedBody.nodes.filterMap (fun item => match item with
    | .expression node => match node.form with | .constructor instantiation _ => some (node.type, instantiation) | _ => none
    | _ => none) with
    | [row] => pure row | _ => throw (IO.userError "builtin arguments constructor missing")
  require (constructor.2.parameterSubstitution.map Prod.snd == [.integer])
    "builtin arguments complete constructor raw range changed"
  let payloadGap ← gap dataFault "payloadGap"
  let keyGap ← gap keyFault "keyGap"
  let rawMapping : SourceTypedRuntime.Value := .mapping .bool .word
    [(.bool true, word 37), (.bool true, word 99), (.bool false, word 41)]
  let mapping : SourceCoreExecution.Value := .mapping .bool .word
    [(.bool true, .word (Word.ofNatModulo 37)), (.bool true, .word (Word.ofNatModulo 99)), (.bool false, .word (Word.ofNatModulo 41))]
  let mappingType : TypeSystem.Ty := .mapping .bool .word
  let successes : List (SourceCompilerFeatureSupport.Entry × List SourceCompilerFeatureSupport.Value × Int × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    (data, [SourceCompilerFeatureSupport.scalar 7], 7,
      [(.word, some (word 7)), (constructor.1, some (.constructed constructor.2 [.integer 7])),
        (.word, some (word 7)), (.word, some (word 7)), (.word, some (word 7))]),
    (indexed, [mapping, SourceCompilerFeatureSupport.scalar 1], 37,
      [(mappingType, some rawMapping), (.word, some (word 1)), (.bool, some (.bool true)),
        (.word, some (word 37)), (.word, some (word 37)), (.word, some (word 37))]),
    (indexed, [mapping, SourceCompilerFeatureSupport.scalar 2], 41,
      [(mappingType, some rawMapping), (.word, some (word 2)), (.bool, some (.bool false)),
        (.word, some (word 41)), (.word, some (word 41)), (.word, some (word 41))])]
  let failures : List (SourceCompilerFeatureSupport.Entry × List SourceCompilerFeatureSupport.Value × Resolved.LocalId × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    (dataFault, [SourceCompilerFeatureSupport.scalar 7], payloadGap, [(.word, some (word 7)), (.word, none)]),
    (keyFault, [mapping], keyGap, [(mappingType, some rawMapping), (.bool, none)])]
  for budget in [0, 41, 137, 500000] do
    for (entry, arguments, expected, expectedCells) in successes do
      let started ← entry.audit arguments budget
      let finished ← get "builtin data arguments success resume" (started.resume 500000)
      match finished.observation with
      | .done (.integer value) state =>
        require (value == expected) "builtin data arguments result changed"
        cells state expectedCells
      | other => throw (IO.userError s!"builtin data arguments success failed: {reprStr other}")
    for (entry, arguments, expectedGap, expectedCells) in failures do
      let started ← entry.audit arguments budget
      let finished ← get "builtin data arguments fault resume" (started.resume 500000)
      match finished.observation with
      | .fault (.uninitializedLocal actualGap) state =>
        require (actualGap == expectedGap) "builtin data arguments first fault changed"
        cells state expectedCells
      | other => throw (IO.userError s!"builtin data arguments fault changed: {reprStr other}")
  for (entry, arguments, expected, _) in successes do entry.checkResume arguments (.integer expected) 41
  for (entry, arguments, _, _) in failures do faultResume entry arguments


def run : IO Unit := do
  let program ← get "builtin arguments checker" (checkProgram workspace 1024)
  let converted ← SourceCompilerFeatureSupport.compileNamed program "converted"
  let lazy ← SourceCompilerFeatureSupport.compileNamed program "lazy"
  let first ← SourceCompilerFeatureSupport.compileNamed program "first"
  let second ← SourceCompilerFeatureSupport.compileNamed program "second"
  let paired ← SourceCompilerFeatureSupport.compileNamed program "paired"
  let empty ← SourceCompilerFeatureSupport.compileNamed program "empty"
  let repeated ← SourceCompilerFeatureSupport.compileNamed program "repeated"
  let zero ← SourceCompilerFeatureSupport.compileNamed program "zero"
  let single ← SourceCompilerFeatureSupport.compileNamed program "single"
  for entry in [converted, lazy, first, second, paired] do inspect entry 2 1
  inspect empty 2 0
  inspect repeated 3 1
  inspect zero 0 1
  inspect single 1 1
  let coercionGap ← gap converted "coercionGap"
  let rawGap ← gap lazy "rawGap"
  let firstGap ← gap first "firstGap"
  let secondGap ← gap second "secondGap"
  let successes : List (SourceCompilerFeatureSupport.Entry × List SourceCompilerFeatureSupport.Value × SourceTypedRuntime.Value × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    (converted, [SourceCompilerFeatureSupport.scalar 1], .integer 1, [(.word, some (word 1)), (.bool, some (.bool true)), (.word, some (word 1)), (.word, some (word 1)), (.word, some (word 1))]),
    (converted, [SourceCompilerFeatureSupport.scalar 2], .integer 2, [(.word, some (word 2)), (.bool, some (.bool false)), (.word, some (word 2)), (.word, some (word 2)), (.word, some (word 2))]),
    (lazy, [SourceCompilerFeatureSupport.scalar 1], .integer 1, [(.word, some (word 1)), (.word, none), (.bool, some (.bool true)), (.word, some (word 1)), (.word, some (word 1)), (.word, some (word 1))]),
    (paired, [SourceCompilerFeatureSupport.scalar 2], .integer 2, [(.word, some (word 2)), (.product .word .bool, some (.product (word 2) (.bool true))), (.word, some (word 2)), (.word, some (word 2)), (.word, some (word 2))]),
    (empty, [SourceCompilerFeatureSupport.scalar 17], .integer 18, [(.word, some (word 17)), (.bool, some (.bool false)), (.integer, some (.integer 18))]),
    (repeated, [SourceCompilerFeatureSupport.scalar 1], .integer 1, [(.word, some (word 1)), (.word, some (word 1)), (.word, some (word 1)), (.word, some (word 1)), (.word, some (word 1)), (.word, some (word 1))]),
    (zero, [], .integer 1, [(.word, some (word 1)), (.word, some (word 1))]),
    (single, [SourceCompilerFeatureSupport.scalar 1], .integer 1, [(.word, some (word 1)), (.word, some (word 1)), (.word, some (word 1)), (.word, some (word 1))])]
  let failures : List (SourceCompilerFeatureSupport.Entry × Nat × Resolved.LocalId × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    (converted, 0, coercionGap, [(.word, some (word 0)), (.bool, some (.bool false)), (.word, some (word 0)), (.word, some (word 0)), (.word, some (word 0)), (.integer, none)]),
    (lazy, 2, rawGap, [(.word, some (word 2)), (.word, none)]),
    (first, 1, firstGap, [(.word, some (word 1)), (.bool, none), (.word, none)]),
    (second, 1, secondGap, [(.word, some (word 1)), (.word, none)])]
  for budget in [0, 41, 137, 500000] do
    for (entry, arguments, expected, expectedCells) in successes do
      let started ← entry.audit arguments budget
      let finished ← get "builtin arguments success resume" (started.resume 500000)
      match finished.observation with
      | .done value state =>
        require (reprStr value == reprStr expected) "builtin arguments result changed"
        cells state expectedCells
      | other => throw (IO.userError s!"builtin arguments success failed: {reprStr other}")
    for (entry, input, expectedGap, expectedCells) in failures do
      let started ← entry.audit [SourceCompilerFeatureSupport.scalar input] budget
      let finished ← get "builtin arguments failure resume" (started.resume 500000)
      match finished.observation with
      | .fault (.uninitializedLocal actualGap) state =>
        require (actualGap == expectedGap) "builtin arguments first fault changed"
        cells state expectedCells
      | other => throw (IO.userError s!"builtin arguments fault changed: {reprStr other}")
  converted.checkResume [SourceCompilerFeatureSupport.scalar 1] (.integer 1) 41
  lazy.checkResume [SourceCompilerFeatureSupport.scalar 1] (.integer 1) 41
  empty.checkResume [SourceCompilerFeatureSupport.scalar 17] (.integer 18) 41
  repeated.checkResume [SourceCompilerFeatureSupport.scalar 1] (.integer 1) 41
  zero.checkResume [] (.integer 1) 41
  for (entry, input, _, _) in failures do faultResume entry [.word (Word.ofNatModulo input)]
  dataCases program
  IO.println "builtin raw named arguments: actual ordered callbacks/full metadata, empty/single/packed arguments, lazy and first/later faults, complete heaps/public resume GREEN"

end Tests.SourceCoreCallableCoercionRawNamedCallBuiltinArguments
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableCoercionRawNamedCallScalarArguments
/-! Actual scalar argument callbacks close the final raw-call argument Trees.
The concrete semantic consumers retain the original parent requirements/output
path, reached full header, actual BodyState profiles and catalog/method Entry.
No raw/child/body runtime law or pre-run of the source is an input. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
namespace Tests.SourceCoreCallableCoercionRawNamedCallScalarArguments
open Solcore SourceSemantics SourceSemantics.CoreLowering Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableAncestryPairedLookup
open CallableCoercionExpressionCertificates CallableCoercionExpressionMeaning
open CallableCoercionRawNamedCallCertificates RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds

section Accepted
variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : SourceCoreCallableIndexedPrograms.Prepared checked} {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {compilerProgram : CheckedProgram}
  {headers : Inventory prepared.ancestry values ambient.definitions (Program.ofChecked compilerProgram)} {locations : Locations} {capturePrefix : Nat}
  {bodyCompilation : Header prepared.ancestry values ambient.definitions (Program.ofChecked compilerProgram) → SourceCoreFunctions.Context}
  {expressionSyntax : Header prepared.ancestry values ambient.definitions (Program.ofChecked compilerProgram) → ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  (owners : ((Program.ofChecked compilerProgram).functions.map (fun definition => definition.body.owner)).Nodup)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (missing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header ∈ headers, faults .controlEscapedFunction header.escaped)
  (prefixMatches : ∀ header ∈ headers, (bodyCompilation header).administrativePrefix = capturePrefix + 1)
  (profiles : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location}
      {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame},
      BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost →
      ProfileFor diagnosticPolicy headers header (bodyCompilation header) header.readFuel (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)


variable {compilation : SourceCoreFunctions.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {reasonAt : ExpressionId → Word} {readFuel fuel : Nat}
  (valid : CompatibleExpressionLiterals.ContextValid compilation.solvedRequirements context evidence)
  (sourceUnique : NodeOccurrencesUnique source)
  (callerUninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (callerMissing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  {project : Projector} {callerFunction : Specialized} {child : SourceCoreEvidence.Child}
  {scope : SourceCoreLocalCell.Scope} {id callee : ExpressionId} {arguments : List ExpressionId}
  {instantiation : DeclarationInstantiation} {policy : SourceCoreFunctions.CallablePolicy}
  {node : ExpressionNode} {output : Lowered}
  (receipt : Direct compilerProgram project callerFunction compilation child fuel source scope id callee arguments
    instantiation reasonAt policy node output)
  {header : Header prepared.ancestry values ambient.definitions (Program.ofChecked compilerProgram)}
  (reached : Reached receipt (headers := headers) header)
  (sourceTypes : RecursiveNamedExpressionCompilerCertificates.SourceTypes headers context)
  (sourceSignatures : context.signatures = (Program.ofChecked compilerProgram).signatures)
  (typed : ExpressionHasType source context id node.type)
  {representation : SourceCoreGeneralFunctions.Representation} {signatures : ProgramSignatures}
  {localCatalog : SourceCoreLocalPolymorphism.Catalog} {parents : List SourceCoreLocalEvidence.Prepared}
  {assignments : SourceCoreAssignmentFaultSites.Table} {diagnostics : SourceCoreDataPlaceFaultSites.Program}
  {native : Option SourceCoreGeneralFunctions.CallableContext} {parent : Option SourceCoreLocalEvidence.Prepared}
  {skipInitializer : Option ExpressionId}
  (childEq : child = SourceCoreGeneralFunctions.lowerContextualExpression compilerProgram representation signatures localCatalog parents
    assignments diagnostics compilation native parent skipInitializer)
  (syntaxTrees : ∀ argument, argument ∈ arguments → CompatibleExpressionConditionals.Syntax source argument)
  (ordinary : CompatibleExpressionConditionals.Ordinary source localCatalog compilation.owner)
  (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
  (readPolicy : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
  (lowerPolicy : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
  (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
  {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment} {actualContext : Core.Context}
  {before : Dynamic.Heap} {store : Store} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world administrative
    scope environment canonical ambient.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
  (installed : RecursiveNamedCatalog.Entry headers locations capturePrefix compilation.administrativePrefix
    scope mapping world before store canonical)

variable {raw : Workspace.RawWorkspace} {checkFuel : Nat}
  (checkedAccepted : checkProgram raw checkFuel = .ok compilerProgram)
  (definitions : prepared.layouts.definitions = ambient.definitions)
  (registered : prepared.ancestry.layout.frame.Registered ambient.definitions)
  {methods : CallableCoercionPathMeaning.Profiles (prepared := prepared) (values := values)
    (program := Program.ofChecked compilerProgram) (context := context) (evidence := evidence)}
  (methodUninitialized : ∀ method ∈ methods, ∀ id location,
    faults (.uninitializedLocation location) (method.diagnostics.reasonAt method.named.signature.key id))
  (methodMissing : ∀ method ∈ methods, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((method.diagnostics.reasonAt method.named.signature.key id).add tag))
  {calls : List CallableCoercionSpine.Call}
  (emitted : CallableCoercionMethodEntries.Emitted compilerProgram project compilation callerFunction receipt.available
    scope node policy ξ receipt.operand methods output calls)
  (steps : methods.map (·.step) = node.coercions)
  (chain : CallableCoercionPathMeaning.Chain node.rawType receipt.operand.type methods node.type output.type)
  (ledger : context.solvedRequirements = callerFunction.function.solvedRequirements)
  (methodEntry : CallableCoercionMethodEntries.Entry methods ambient.definitions actual mapping world before store)


include extension definitions registered faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles
  valid sourceUnique callerUninitialized callerMissing reached sourceTypes sourceSignatures typed childEq syntaxTrees ordinary declarations readPolicy lowerPolicy leafPolicy
  environments heaps locals agrees actualTyped installed methodUninitialized methodMissing emitted steps chain methodEntry checkedAccepted owners ledger in
theorem accepted_preserves
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : Dynamic.ExpressionEvaluatesOutcome (Program.ofChecked compilerProgram) context evidence source environment before id outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (output.expression.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        node.type output.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (CallableCoercionMethodEntries.Entry methods ambient.definitions actual finalMap finalWorld after finalStore) := by
  obtain ⟨certified⟩ := CallableCoercionRawNamedCallScalarArguments.of_contextual receipt childEq reached sourceTypes sourceUnique sourceSignatures typed syntaxTrees ordinary declarations readPolicy lowerPolicy leafPolicy
  exact CallableCoercionRawNamedCallMeaning.preserves
    (functions := functions) (extension := extension) (definitions := definitions) (registered := registered)
    (faithful := faithful) (observations := observations) (runtimeViews := runtimeViews) (uninitialized := uninitialized)
    (missing := missing) (escaped := escaped) (prefixMatches := prefixMatches) (profiles := profiles)
    (valid := valid) (callerUninitialized := callerUninitialized) (callerMissing := callerMissing) (receipt := receipt)
    (certified := certified) (environments := environments) (heaps := heaps) (locals := locals)
    (agrees := agrees) (actualTyped := actualTyped) (installed := installed) (methodUninitialized := methodUninitialized)
    (methodMissing := methodMissing) (emitted := emitted) (steps := steps) (chain := chain)
    (methodEntry := methodEntry) (checkedAccepted := checkedAccepted) (owners := owners) (sourceUnique := sourceUnique)
    (ledger := ledger) trace

include extension definitions registered faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles
  valid sourceUnique callerUninitialized callerMissing reached sourceTypes sourceSignatures typed childEq syntaxTrees ordinary declarations readPolicy lowerPolicy leafPolicy
  environments heaps locals agrees actualTyped installed methodUninitialized methodMissing emitted steps chain methodEntry in
theorem accepted_reflects
    {value : Value} {finalStore : Store}
    (completed : Evaluates actual store (output.expression.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome (Program.ofChecked compilerProgram) context evidence source environment before id outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        node.type output.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (CallableCoercionMethodEntries.Entry methods ambient.definitions actual finalMap finalWorld after finalStore) := by
  obtain ⟨certified⟩ := CallableCoercionRawNamedCallScalarArguments.of_contextual receipt childEq reached sourceTypes sourceUnique sourceSignatures typed syntaxTrees ordinary declarations readPolicy lowerPolicy leafPolicy
  exact CallableCoercionRawNamedCallMeaning.reflects
    (functions := functions) (extension := extension) (definitions := definitions) (registered := registered)
    (faithful := faithful) (observations := observations) (runtimeViews := runtimeViews) (uninitialized := uninitialized)
    (missing := missing) (escaped := escaped) (prefixMatches := prefixMatches) (profiles := profiles)
    (valid := valid) (callerUninitialized := callerUninitialized) (callerMissing := callerMissing) (receipt := receipt)
    (certified := certified) (environments := environments) (heaps := heaps) (locals := locals)
    (agrees := agrees) (actualTyped := actualTyped) (installed := installed) (methodUninitialized := methodUninitialized)
    (methodMissing := methodMissing) (emitted := emitted) (steps := steps) (chain := chain)
    (methodEntry := methodEntry) completed
end Accepted


private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Marker<T> {}", "impl Marker<Word> {}",
    "trait Coerce<From, To> { function coerce(value: From) returns (To); }",
    "impl Coerce<Word, Bool> { function coerce(value: Word) returns (Bool) { let seen = value; if (value == 0) { let coercionGap: Bool; return coercionGap; } return value == 1; } }",
    "function choose<A, B>(unused: A, value: B) returns (B) { return value; }",
    "function relay<T>(value: T) returns (T) { return value; }",
    "function last(a: Word, b: Word, c: Word) returns (Word) { return c; }",
    "function one() returns (Word) { return 1; }",
    "function converted(value: Word) returns (Bool) { return choose((value == 1), (value + 0)); }",
    "function lazy(value: Word) returns (Bool) { let rawGap: Word; return choose(!false, value == 1 ? (value + 0) : rawGap); }",
    "function first(value: Word) returns (Bool) { let firstGap: Bool; let secondGap: Word; return choose(firstGap, secondGap); }",
    "function second(value: Word) returns (Bool) { let secondGap: Word; return choose(value == 1, secondGap); }",
    "function paired(value: Word) returns (Bool) { return choose((value, true), value); }",
    "function empty(value: Word) returns (Word) where Word: Marker { return choose(false, value + 1); }",
    "function repeated(value: Word) returns (Bool) { return last(value, value, value); }",
    "function zero() returns (Bool) { return one(); }",
    "function single(value: Word) returns (Bool) { return relay(value); }"
  ]}] }
private def require := SourceCompilerFeatureSupport.require
private def get {α ε : Type} [Repr ε] := @SourceCompilerFeatureSupport.get α ε _
private def word (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def cells (state : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) : IO Unit :=
  require (reprStr (state.heap.map fun cell => (cell.type, cell.value)) == reprStr expected)
    s!"scalar arguments ordered cells changed: {reprStr state.heap}"

private def scalarSyntax (source : TypedSource) : Nat → ExpressionId → Bool
  | 0, _ => false
  | fuel + 1, id => match source.lookupExpression? id with
    | none => false
    | some node => match node.form with
      | .literal _ | .integerLiteral _ _ | .reference _ (.builtinBoolean _) | .reference _ (.local _) => true
      | .group inner | .unary _ inner => scalarSyntax source fuel inner
      | .tuple [left, right] | .binary left _ right => scalarSyntax source fuel left && scalarSyntax source fuel right
      | .conditional condition left right => scalarSyntax source fuel condition && scalarSyntax source fuel left && scalarSyntax source fuel right
      | _ => false

/-- Re-enter the production contextual callback at the actual final lexical
scope. Check complete selected metadata and exactly the ordered argument code;
this runtime audit does not manufacture source typing or a semantic Header. -/
private def inspect (entry : SourceCompilerFeatureSupport.Entry) (arity pathCount : Nat) : IO Unit := do
  let indexed := entry.cached.indexed
  let base := indexed.base
  let named ← match base.functions.find? (·.signature.key == entry.key) with
    | some named => pure named | none => throw (IO.userError "scalar arguments caller missing")
  let caller := named.specialized
  let source := caller.function.typedBody
  let context := declarationContext base.sourceProgram.signatures source.owner [] caller.assumptions caller.function.solvedRequirements
  require (context.residualTypeVariables && context.typeVariables.isEmpty && context.solvedRequirements == caller.function.solvedRequirements)
    "scalar arguments actual caller context changed"
  let scope ← get "scalar arguments scope" ((SourceCoreDataPlaces.declaredBinders source).reverse.mapM fun binder => do
    let type ← entry.cached.compatible.checked.catalog.project binder.scheme.body
    pure (binder.id, type))
  let compilation : SourceCoreFunctions.Context := {
    plan := base.plan, owner := named.signature.key, globals := base.globals, administrativePrefix := 1,
    solvedRequirements := caller.function.solvedRequirements, internalReason := Word.zero }
  let representation := (SourceCoreCallableIndexedPrograms.markedRepresentation indexed.ancestry indexed.fuel indexed.layouts).atContext named.signature.key []
  let diagnostics ← match base.diagnostics with
    | some diagnostics => pure diagnostics.program | none => throw (IO.userError "scalar arguments diagnostics missing")
  let diagnostics := match base.callableContext with
    | some native => {diagnostics with rootTable := native.diagnostics.rootTable} | none => diagnostics
  let own ← match diagnostics.base.find? named.signature.key with
    | some own => pure own | none => throw (IO.userError "scalar arguments own diagnostics missing")
  let child := SourceCoreGeneralFunctions.lowerContextualExpression base.sourceProgram representation base.sourceProgram.signatures
    base.locals base.contexts own.assignments diagnostics compilation base.callableContext none none
  let policy := SourceCoreGeneralFunctions.callablePolicy base.callableContext []
  let reasonAt := diagnostics.reasonAt named.signature.key
  let available ← get "scalar arguments available" (SourceCompilationPlan.resolveRuntimeEvidenceEnvironment base.sourceProgram caller.key caller.assumptions)
  let mut count := 0
  for item in source.nodes do
    if let .expression node := item then
      if let .call callee arguments (.declaration instantiation) := node.form then
        require (arguments.length == arity && arguments.all (scalarSyntax source 100) && node.coercions.length == pathCount)
          s!"scalar arguments original syntax/arity/path changed: key={reprStr entry.key}, args={reprStr arguments}, scalar={reprStr (arguments.map (scalarSyntax source 100))}, path={node.coercions.length}"
        discard <| get "scalar arguments callee" (SourceCompilationPlan.validateDirectDeclarationCallee source node.id callee instantiation)
        let target ← get "scalar arguments target" (SourceCompilationPlan.exactInstantiationKey base.plan instantiation)
        let key ← get "scalar arguments edge" (SourceCompilationPlan.exactCallKey base.plan compilation.owner node.id target)
        let selected ← get "scalar arguments record" (SourceCompilationPlan.exactSpecialization base.plan key)
        require (instantiation == CallableNamedCanonicalOrder.retainedInstantiation selected && selected.assumptions.isEmpty &&
          instantiation.parameterSubstitution.map Prod.fst == (selected.parameterSubstitution.map Prod.fst).reverse &&
          selected.function.typedBody.inputs.length == arity)
          "scalar arguments full original metadata/order changed"
        let dictionary ← get "scalar arguments dictionary" (SourceCompilationPlan.exactDirectCallRuntimeEvidence caller node available instantiation)
        require dictionary.isEmpty "scalar arguments ordinary dictionary changed"
        let (signature, index) ← match base.globals.zipIdx.filter (fun row => decide (row.1.key = key)) with
          | [row] => pure row | _ => throw (IO.userError "scalar arguments actual global not singleton")
        let codes ← get "scalar arguments ordered mapM" (arguments.mapM (fun argument => child 150 source scope argument reasonAt))
        let sourceTypes ← get "scalar arguments raw types" (selected.function.typedBody.inputs.mapM fun binder =>
          entry.cached.compatible.checked.catalog.project binder.scheme.body)
        require (codes.map (·.type) == sourceTypes && signature.parameterType == (SourceCoreCalls.packArguments codes).type)
          "scalar arguments actual native vector changed"
        let raw : SourceCoreBasic.LoweredExpr := ⟨signature.resultType, SourceCoreCalls.call signature
          (scope.length + compilation.administrativePrefix + index) (SourceCoreCalls.packArguments codes).expression compilation.internalReason⟩
        let expected ← get "scalar arguments suffix" (SourceCoreEvidence.applyCoercions base.sourceProgram representation.expressions.projectType
          compilation caller available scope node policy raw node.coercions)
        let result ← get "scalar arguments actual outer" (SourceCoreEvidence.lowerWithProjector base.sourceProgram representation.expressions.projectType
          caller compilation child 150 source scope node.id reasonAt policy)
        require (result == some expected) "scalar arguments actual parent code changed"
        let nativeContext := SourceCoreLocalCell.coreContext scope ++ named.signature.parameterType ::
          (base.globals.map SourceCoreCalls.Signature.referenceType ++ [.cell indexed.ancestry.layout.frame.type])
        require (Core.infer? nativeContext expected.expression indexed.layouts.definitions == some (LanguageResult.resultType expected.type))
          "scalar arguments actual native code is ill typed"
        count := count + 1
  require (count == 1) "scalar arguments reached direct site missing"

private def gap (entry : SourceCompilerFeatureSupport.Entry) (name : String) : IO Resolved.LocalId := do
  let binders := entry.cached.indexed.base.functions.flatMap fun named =>
    SourceCoreDataPlaces.declaredBinders named.specialized.function.typedBody
  match binders.filter (·.name == name) with
  | [binder] => pure binder.id
  | _ => throw (IO.userError s!"scalar arguments gap {name} is not unique")

private def faultResume (entry : SourceCompilerFeatureSupport.Entry) (arguments : List SourceCoreExecution.Value) : IO Unit := do
  let artifact ← entry.execution.open
  let initial ← SourceCompilerFeatureSupport.boot artifact
  let finished ← SourceCompilerFeatureSupport.get "scalar arguments fault"
    (← initial.run entry.key arguments SourceCompilerFeatureSupport.executionOptions)
  let (fault, session) ← match finished with
    | .failed fault session => pure (fault, session)
    | _ => throw (IO.userError "scalar arguments expected fault")
  let expected ← SourceCompilerFeatureSupport.get "scalar arguments fault snapshot" (← session.snapshot 2048)
  for budget in [0, 41, 137] do
    let started ← SourceCompilerFeatureSupport.get "scalar arguments suspend"
      (← initial.run entry.key arguments {SourceCompilerFeatureSupport.executionOptions with executionFuel := budget})
    let resumed ← match started with
      | .outOfFuel checkpoint => checkpoint.resume 500000 2048
      | outcome => pure outcome
    match resumed with
    | .failed observed session =>
      let snapshot ← SourceCompilerFeatureSupport.get "scalar arguments resumed snapshot" (← session.snapshot 2048)
      require (observed == fault && reprStr snapshot.cells == reprStr expected.cells)
        "scalar arguments public fault/full snapshot changed on resume"
    | _ => throw (IO.userError "scalar arguments fault resume changed outcome")


def run : IO Unit := do
  let program ← get "scalar arguments checker" (checkProgram workspace 1024)
  let converted ← SourceCompilerFeatureSupport.compileNamed program "converted"
  let lazy ← SourceCompilerFeatureSupport.compileNamed program "lazy"
  let first ← SourceCompilerFeatureSupport.compileNamed program "first"
  let second ← SourceCompilerFeatureSupport.compileNamed program "second"
  let paired ← SourceCompilerFeatureSupport.compileNamed program "paired"
  let empty ← SourceCompilerFeatureSupport.compileNamed program "empty"
  let repeated ← SourceCompilerFeatureSupport.compileNamed program "repeated"
  let zero ← SourceCompilerFeatureSupport.compileNamed program "zero"
  let single ← SourceCompilerFeatureSupport.compileNamed program "single"
  for entry in [converted, lazy, first, second, paired] do inspect entry 2 1
  inspect empty 2 0
  inspect repeated 3 1
  inspect zero 0 1
  inspect single 1 1
  let coercionGap ← gap converted "coercionGap"
  let rawGap ← gap lazy "rawGap"
  let firstGap ← gap first "firstGap"
  let secondGap ← gap second "secondGap"
  let successes : List (SourceCompilerFeatureSupport.Entry × List SourceCompilerFeatureSupport.Value × SourceTypedRuntime.Value × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    (converted, [SourceCompilerFeatureSupport.scalar 1], .bool true, [(.word, some (word 1)), (.bool, some (.bool true)), (.word, some (word 1)), (.word, some (word 1)), (.word, some (word 1))]),
    (converted, [SourceCompilerFeatureSupport.scalar 2], .bool false, [(.word, some (word 2)), (.bool, some (.bool false)), (.word, some (word 2)), (.word, some (word 2)), (.word, some (word 2))]),
    (lazy, [SourceCompilerFeatureSupport.scalar 1], .bool true, [(.word, some (word 1)), (.word, none), (.bool, some (.bool true)), (.word, some (word 1)), (.word, some (word 1)), (.word, some (word 1))]),
    (paired, [SourceCompilerFeatureSupport.scalar 2], .bool false, [(.word, some (word 2)), (.product .word .bool, some (.product (word 2) (.bool true))), (.word, some (word 2)), (.word, some (word 2)), (.word, some (word 2))]),
    (empty, [SourceCompilerFeatureSupport.scalar 17], word 18, [(.word, some (word 17)), (.bool, some (.bool false)), (.word, some (word 18))]),
    (repeated, [SourceCompilerFeatureSupport.scalar 1], .bool true, [(.word, some (word 1)), (.word, some (word 1)), (.word, some (word 1)), (.word, some (word 1)), (.word, some (word 1)), (.word, some (word 1))]),
    (zero, [], .bool true, [(.word, some (word 1)), (.word, some (word 1))]),
    (single, [SourceCompilerFeatureSupport.scalar 1], .bool true, [(.word, some (word 1)), (.word, some (word 1)), (.word, some (word 1)), (.word, some (word 1))])]
  let failures : List (SourceCompilerFeatureSupport.Entry × Nat × Resolved.LocalId × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    (converted, 0, coercionGap, [(.word, some (word 0)), (.bool, some (.bool false)), (.word, some (word 0)), (.word, some (word 0)), (.word, some (word 0)), (.bool, none)]),
    (lazy, 2, rawGap, [(.word, some (word 2)), (.word, none)]),
    (first, 1, firstGap, [(.word, some (word 1)), (.bool, none), (.word, none)]),
    (second, 1, secondGap, [(.word, some (word 1)), (.word, none)])]
  for budget in [0, 41, 137, 500000] do
    for (entry, arguments, expected, expectedCells) in successes do
      let started ← entry.audit arguments budget
      let finished ← get "scalar arguments success resume" (started.resume 500000)
      match finished.observation with
      | .done value state =>
        require (reprStr value == reprStr expected) "scalar arguments result changed"
        cells state expectedCells
      | other => throw (IO.userError s!"scalar arguments success failed: {reprStr other}")
    for (entry, input, expectedGap, expectedCells) in failures do
      let started ← entry.audit [SourceCompilerFeatureSupport.scalar input] budget
      let finished ← get "scalar arguments failure resume" (started.resume 500000)
      match finished.observation with
      | .fault (.uninitializedLocal actualGap) state =>
        require (actualGap == expectedGap) "scalar arguments first fault changed"
        cells state expectedCells
      | other => throw (IO.userError s!"scalar arguments fault changed: {reprStr other}")
  converted.checkResume [SourceCompilerFeatureSupport.scalar 1] (.bool true) 41
  lazy.checkResume [SourceCompilerFeatureSupport.scalar 1] (.bool true) 41
  empty.checkResume [SourceCompilerFeatureSupport.scalar 17] (.word (Word.ofNatModulo 18)) 41
  repeated.checkResume [SourceCompilerFeatureSupport.scalar 1] (.bool true) 41
  zero.checkResume [] (.bool true) 41
  for (entry, input, _, _) in failures do faultResume entry [.word (Word.ofNatModulo input)]
  IO.println "scalar raw named arguments: actual ordered callbacks/full metadata, empty/single/packed arguments, lazy and first/later faults, complete heaps/public resume GREEN"

end Tests.SourceCoreCallableCoercionRawNamedCallScalarArguments
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableCoercionRawNamedCalls
/-! Actual outer ordinary calls use the reached full header and original-source
ordered argument Trees. The formal consumers close argument/body runtime laws
through catalog mutual induction. Initial authority and static profiles remain
explicit; no coverage of all coercion-method globals is claimed. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
namespace Tests.SourceCoreCallableCoercionRawNamedCalls
open Solcore SourceSemantics SourceSemantics.CoreLowering Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableAncestryPairedLookup
open CallableCoercionExpressionCertificates CallableCoercionExpressionMeaning
open CallableCoercionRawNamedCallCertificates RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds

section Accepted
variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : SourceCoreCallableIndexedPrograms.Prepared checked} {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {compilerProgram : CheckedProgram}
  {headers : Inventory prepared.ancestry values ambient.definitions (Program.ofChecked compilerProgram)} {locations : Locations} {capturePrefix : Nat}
  {bodyCompilation : Header prepared.ancestry values ambient.definitions (Program.ofChecked compilerProgram) → SourceCoreFunctions.Context}
  {expressionSyntax : Header prepared.ancestry values ambient.definitions (Program.ofChecked compilerProgram) → ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  (owners : ((Program.ofChecked compilerProgram).functions.map (fun definition => definition.body.owner)).Nodup)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (missing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header ∈ headers, faults .controlEscapedFunction header.escaped)
  (prefixMatches : ∀ header ∈ headers, (bodyCompilation header).administrativePrefix = capturePrefix + 1)
  (profiles : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location}
      {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame},
      BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost →
      ProfileFor diagnosticPolicy headers header (bodyCompilation header) header.readFuel (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)


variable {compilation : SourceCoreFunctions.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {reasonAt : ExpressionId → Word} {readFuel fuel : Nat}
  (valid : CompatibleExpressionLiterals.ContextValid compilation.solvedRequirements context evidence)
  (sourceUnique : NodeOccurrencesUnique source)
  (callerUninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (callerMissing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  {project : Projector} {callerFunction : Specialized} {child : SourceCoreEvidence.Child}
  {scope : SourceCoreLocalCell.Scope} {id callee : ExpressionId} {arguments : List ExpressionId}
  {instantiation : DeclarationInstantiation} {policy : SourceCoreFunctions.CallablePolicy}
  {node : ExpressionNode} {output : Lowered}
  (receipt : Direct compilerProgram project callerFunction compilation child fuel source scope id callee arguments
    instantiation reasonAt policy node output)
  {header : Header prepared.ancestry values ambient.definitions (Program.ofChecked compilerProgram)}
  (reached : Reached receipt (headers := headers) header)
  (sourceTypes : RecursiveNamedExpressionCompilerCertificates.SourceTypes headers context)
  (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
  (typed : ExpressionHasType source context id node.type)
  (children : DataExpressionSequence.Tree source
    (Expressions headers compilation readFuel source context compilation.solvedRequirements reasonAt)
    scope arguments (header.bindings.map (fun binder => binder.1.scheme.body)) receipt.loweredArguments)
  (nativeTypes : receipt.loweredArguments.map (·.type) = header.bindings.map Prod.snd)
  {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment} {actualContext : Core.Context}
  {before : Dynamic.Heap} {store : Store} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world administrative
    scope environment canonical ambient.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
  (installed : RecursiveNamedCatalog.Entry headers locations capturePrefix compilation.administrativePrefix
    scope mapping world before store canonical)

variable {raw : Workspace.RawWorkspace} {checkFuel : Nat}
  (checkedAccepted : checkProgram raw checkFuel = .ok compilerProgram)
  (definitions : prepared.layouts.definitions = ambient.definitions)
  (registered : prepared.ancestry.layout.frame.Registered ambient.definitions)
  {methods : CallableCoercionPathMeaning.Profiles (prepared := prepared) (values := values)
    (program := Program.ofChecked compilerProgram) (context := context) (evidence := evidence)}
  (methodUninitialized : ∀ method ∈ methods, ∀ id location,
    faults (.uninitializedLocation location) (method.diagnostics.reasonAt method.named.signature.key id))
  (methodMissing : ∀ method ∈ methods, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((method.diagnostics.reasonAt method.named.signature.key id).add tag))
  {calls : List CallableCoercionSpine.Call}
  (emitted : CallableCoercionMethodEntries.Emitted compilerProgram project compilation callerFunction receipt.available
    scope node policy ξ receipt.operand methods output calls)
  (steps : methods.map (·.step) = node.coercions)
  (chain : CallableCoercionPathMeaning.Chain node.rawType receipt.operand.type methods node.type output.type)
  (ledger : context.solvedRequirements = callerFunction.function.solvedRequirements)
  (methodEntry : CallableCoercionMethodEntries.Entry methods ambient.definitions actual mapping world before store)


include extension definitions registered faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles
  valid sourceUnique callerUninitialized callerMissing reached sourceTypes closed residual typed children nativeTypes
  environments heaps locals agrees actualTyped installed methodUninitialized methodMissing emitted steps chain methodEntry checkedAccepted owners ledger in
theorem accepted_preserves
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : Dynamic.ExpressionEvaluatesOutcome (Program.ofChecked compilerProgram) context evidence source environment before id outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (output.expression.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        node.type output.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (CallableCoercionMethodEntries.Entry methods ambient.definitions actual finalMap finalWorld after finalStore) := by
  obtain ⟨certified⟩ := CallableCoercionRawNamedCallCertificates.of_tree receipt reached sourceTypes sourceUnique closed residual typed children nativeTypes
  exact CallableCoercionRawNamedCallMeaning.preserves
    (functions := functions) (extension := extension) (definitions := definitions) (registered := registered)
    (faithful := faithful) (observations := observations) (runtimeViews := runtimeViews) (uninitialized := uninitialized)
    (missing := missing) (escaped := escaped) (prefixMatches := prefixMatches) (profiles := profiles)
    (valid := valid) (callerUninitialized := callerUninitialized) (callerMissing := callerMissing) (receipt := receipt)
    (certified := certified) (environments := environments) (heaps := heaps) (locals := locals)
    (agrees := agrees) (actualTyped := actualTyped) (installed := installed) (methodUninitialized := methodUninitialized)
    (methodMissing := methodMissing) (emitted := emitted) (steps := steps) (chain := chain)
    (methodEntry := methodEntry) (checkedAccepted := checkedAccepted) (owners := owners) (sourceUnique := sourceUnique)
    (ledger := ledger) trace

include extension definitions registered faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles
  valid sourceUnique callerUninitialized callerMissing reached sourceTypes closed residual typed children nativeTypes
  environments heaps locals agrees actualTyped installed methodUninitialized methodMissing emitted steps chain methodEntry in
theorem accepted_reflects
    {value : Value} {finalStore : Store}
    (completed : Evaluates actual store (output.expression.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome (Program.ofChecked compilerProgram) context evidence source environment before id outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        node.type output.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (CallableCoercionMethodEntries.Entry methods ambient.definitions actual finalMap finalWorld after finalStore) := by
  obtain ⟨certified⟩ := CallableCoercionRawNamedCallCertificates.of_tree receipt reached sourceTypes sourceUnique closed residual typed children nativeTypes
  exact CallableCoercionRawNamedCallMeaning.reflects
    (functions := functions) (extension := extension) (definitions := definitions) (registered := registered)
    (faithful := faithful) (observations := observations) (runtimeViews := runtimeViews) (uninitialized := uninitialized)
    (missing := missing) (escaped := escaped) (prefixMatches := prefixMatches) (profiles := profiles)
    (valid := valid) (callerUninitialized := callerUninitialized) (callerMissing := callerMissing) (receipt := receipt)
    (certified := certified) (environments := environments) (heaps := heaps) (locals := locals)
    (agrees := agrees) (actualTyped := actualTyped) (installed := installed) (methodUninitialized := methodUninitialized)
    (methodMissing := methodMissing) (emitted := emitted) (steps := steps) (chain := chain)
    (methodEntry := methodEntry) completed
end Accepted

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Box { Box(Bool) }", "enum Final { Final(Box) }", "enum Broken { Broken(Box) }",
    "trait Marker<T> {}", "impl Marker<Word> {}", "impl Marker<Bool> {}", "impl Marker<Box> {}",
    "trait Witness<T> {}", "impl Witness<Word> {}", "impl Witness<Bool> {}", "impl Witness<Box> {}",
    "trait Coerce<From, To> where From: Marker { function coerce(value: From) returns (To) where From: Witness; }",
    "impl Coerce<Word, Bool> where Word: Marker { function coerce(value: Word) returns (Bool) where Word: Witness { let saved: Word = value; if (value == 0) { let firstGap: Bool; return firstGap; } return value == 1; } }",
    "impl Coerce<Bool, Box> where Bool: Marker { function coerce(value: Bool) returns (Box) where Bool: Witness { let m: mapping(Bool => Word); let touched = m[value]; if (value) { return Box(value); } let secondGap: Box; return secondGap; } }",
    "impl Coerce<Box, Final> where Box: Marker { function coerce(value: Box) returns (Final) where Box: Witness { let reached: Word = 31; return Final(value); } }",
    "impl Coerce<Box, Broken> where Box: Marker { function coerce(value: Box) returns (Broken) where Box: Witness { let reached: Word = 37; let lastGap: Broken; return lastGap; } }",
    "function identity(value: Word) returns (Word) { let rawEffect: Word = 19; return value; }",
    "function rawFail() returns (Word) { let rawEffect: Word = 23; let rawGap: Word; return rawGap; }",
    "function first(value: Word) returns (Word) { let firstEffect: Word = 41; return value; }",
    "function second(value: Word) returns (Word) { let secondEffect: Word = 43; return value; }",
    "function combine(left: Word, right: Word) returns (Word) { let bodyEffect: Word = 47; return right; }",
    "function failBody(left: Word, right: Word) returns (Word) { let bodyEffect: Word = 53; let bodyGap: Word; return bodyGap; }",
    "function recurse(value: Word, depth: Word) returns (Word) { if (depth == 0) { return value; } return recurse(value, depth - 1); }",
    "function direct(value: Word) returns (Final) where Word: Marker, Bool: Marker, Box: Marker { let result: Final = combine(first(7), second(value)); return result; }",
    "function late(value: Word) returns (Broken) where Word: Marker, Bool: Marker, Box: Marker { let result: Broken = combine(first(7), second(value)); return result; }",
    "function recursive(value: Word) returns (Final) where Word: Marker, Bool: Marker, Box: Marker { let result: Final = recurse(value, 2); return result; }",
    "function early() returns (Final) where Word: Marker, Bool: Marker, Box: Marker { let result: Final = combine(rawFail(), second(1)); return result; }",
    "function secondFault() returns (Final) where Word: Marker, Bool: Marker, Box: Marker { let result: Final = combine(first(7), rawFail()); return result; }",
    "function bodyFault() returns (Final) where Word: Marker, Bool: Marker, Box: Marker { let result: Final = failBody(first(7), second(1)); return result; }",
    "function emptySelected(value: Word) returns (Word) where Word: Marker { return identity(value); }",
    "function bypass(value: Word) returns (Word) { return identity(value); }"
  ]}] }

private def word (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def cells (state : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) (label : String) : IO Unit :=
  SourceCompilerFeatureSupport.require (reprStr (state.heap.map fun cell => (cell.type, cell.value)) == reprStr expected)
    s!"path {label} ordered source cells changed: {reprStr state.heap}"

/-- Inspect the real retained constructors used by the three output edges. -/
private def constructorFor (program : CheckedProgram) (name : String) : IO DataConstructorInstantiation := do
  let data ← match program.signatures.dataTypes.find? (·.name == name) with
    | some data => pure data | none => throw (IO.userError s!"source path {name} missing")
  match data.constructors with
  | [constructor] => pure (DataConstructorInstantiation.mk constructor.id [] constructor.payloadTypes (.nominal data.id []))
  | _ => throw (IO.userError s!"source path {name} constructor missing")

private def audit (entry : SourceCompilerFeatureSupport.Entry) (targetName : String) :
    IO (DataConstructorInstantiation × DataConstructorInstantiation × List Resolved.LocalId) := do
  let base := entry.cached.indexed.base
  let named ← match base.functions.find? (·.signature.key == entry.key) with
    | some named => pure named | none => throw (IO.userError "source path caller missing")
  let caller := named.specialized
  let available ← SourceCompilerFeatureSupport.get "source path caller evidence"
    (SourceCompilationPlan.resolveRuntimeEvidenceEnvironment base.sourceProgram caller.key caller.assumptions)
  let constructor ← constructorFor base.sourceProgram "Box"
  let target ← constructorFor base.sourceProgram targetName
  let mut gaps : List Resolved.LocalId := []
  let mut found := false
  for item in caller.function.typedBody.nodes do
    if let .expression node := item then
      if !node.coercions.isEmpty then
        SourceCompilerFeatureSupport.require (node.coercions.length == 3) "actual coercion path lost its three edges"
        let mut goals : List TypeSystem.Ty := []
        for step in node.coercions do
          let method ← SourceCompilerFeatureSupport.get "path method"
            (SourceCompilationPlan.checkedCoercionMethod base.sourceProgram caller node available step)
          let dictionary ← SourceCompilerFeatureSupport.get "path dictionary"
            (SourceCompilationPlan.coercionMethodRuntimeEvidence base.sourceProgram caller node step method)
          let key ← SourceCompilerFeatureSupport.get "path edge"
            (SourceCompilationPlan.exactCallKey base.plan named.signature.key node.id method.specialized.key)
          let selected ← SourceCompilerFeatureSupport.get "path full selected record"
            (SourceCompilationPlan.exactSpecialization base.plan key)
          let emitted ← match base.functions.find? (·.signature.key == key) with
            | some emitted => pure emitted | none => throw (IO.userError "path native row missing")
          SourceCompilerFeatureSupport.require (selected == method.specialized && emitted.specialized == selected &&
            emitted.inputs.length == 1 && dictionary.length == 3 && dictionary[0]? == dictionary[1]? &&
            dictionary[1]? != dictionary[2]? && dictionary.map SourceCompilationPlan.runtimeEvidenceGoal == selected.assumptions &&
            method.traitPredicates.all caller.assumptions.contains)
            "path full record / ordered repeated dictionary / caller coverage changed"
          goals := goals ++ [step.source, step.target]
          let declared := (SourceCoreDataPlaces.declaredBinders selected.function.typedBody).filter
            (fun binder => binder.name == "firstGap" || binder.name == "secondGap" || binder.name == "lastGap")
          match declared with
          | [binder] => gaps := gaps ++ [binder.id]
          | [] =>
            SourceCompilerFeatureSupport.require (step.target == target.resultType && targetName == "Final")
              "only successful terminal method may lack a gap"
          | _ => throw (IO.userError "source path ambiguous method gap")
        SourceCompilerFeatureSupport.require (goals == [.word, .bool, .bool, constructor.resultType, constructor.resultType, target.resultType])
          "path raw endpoint order changed"
        let compilation : SourceCoreFunctions.Context := {
          plan := base.plan, owner := named.signature.key, globals := base.globals, administrativePrefix := 1,
          solvedRequirements := caller.function.solvedRequirements, internalReason := Word.zero }
        let indexed := entry.cached.indexed
        let representation := (SourceCoreCallableIndexedPrograms.markedRepresentation indexed.ancestry indexed.fuel indexed.layouts).atContext named.signature.key []
        let diagnostics ← match base.diagnostics with
          | some diagnostics => pure diagnostics.program
          | none => throw (IO.userError "outer diagnostics missing")
        let diagnostics := match base.callableContext with
          | some native => {diagnostics with rootTable := native.diagnostics.rootTable}
          | none => diagnostics
        let own ← match diagnostics.base.find? named.signature.key with
          | some own => pure own | none => throw (IO.userError "outer caller diagnostics missing")
        let source := caller.function.typedBody
        let scope := named.inputs.reverse.map (fun (binder, type) => (binder.id, type))
        let reasonAt := diagnostics.reasonAt named.signature.key
        let child := SourceCoreGeneralFunctions.lowerContextualExpression base.sourceProgram representation base.sourceProgram.signatures
          base.locals base.contexts own.assignments diagnostics compilation base.callableContext none none
        let policy := SourceCoreGeneralFunctions.callablePolicy base.callableContext []
        let result ← SourceCompilerFeatureSupport.get "actual outer lowerWithProjector"
          (SourceCoreEvidence.lowerWithProjector base.sourceProgram representation.expressions.projectType caller compilation child
            150 source scope node.id reasonAt policy)
        let lowered ← match result with
          | some lowered => pure lowered | none => throw (IO.userError "coerced outer delegated unexpectedly")
        let raw ← match node.form with
          | .call callee arguments (.declaration instantiation) => do
            discard <| SourceCompilerFeatureSupport.get "actual callee metadata"
              (SourceCompilationPlan.validateDirectDeclarationCallee source node.id callee instantiation)
            let dictionary ← SourceCompilerFeatureSupport.get "actual direct dictionary"
              (SourceCompilationPlan.exactDirectCallRuntimeEvidence caller node available instantiation)
            let target ← SourceCompilerFeatureSupport.get "actual direct target"
              (SourceCompilationPlan.exactInstantiationKey base.plan instantiation)
            let key ← SourceCompilerFeatureSupport.get "actual direct edge"
              (SourceCompilationPlan.exactCallKey base.plan compilation.owner node.id target)
            let selected ← SourceCompilerFeatureSupport.get "actual direct full record"
              (SourceCompilationPlan.exactSpecialization base.plan key)
            discard <| SourceCompilerFeatureSupport.get "actual direct authentication"
              (SourceCompilationPlan.validateAuthenticatedRuntimeEvidence base.sourceProgram.signatures key selected.assumptions dictionary)
            let (signature, index) ← match base.globals.zipIdx.filter (fun row => decide (row.1.key = key)) with
              | [row] => pure row | _ => throw (IO.userError "actual direct global is not singleton")
            let native ← match base.functions.filter (·.signature.key == key) with
              | [native] => pure native | _ => throw (IO.userError "ordinary reached header is not singleton")
            SourceCompilerFeatureSupport.require (native.specialized == selected && native.signature == signature &&
              selected.assumptions.isEmpty && dictionary.isEmpty && arguments.length == 2)
              "reached ordinary full record/signature/empty dictionary/two arguments changed"
            let loweredArgs ← SourceCompilerFeatureSupport.get "actual ordered direct children"
              (arguments.mapM (fun argument => child 150 source scope argument reasonAt))
            let packed := SourceCoreCalls.packArguments loweredArgs
            SourceCompilerFeatureSupport.require (signature.parameterType == packed.type &&
              arguments.length == selected.function.typedBody.inputs.length) "actual direct arity changed"
            pure ⟨signature.resultType, SourceCoreCalls.call signature (scope.length + compilation.administrativePrefix + index)
              packed.expression compilation.internalReason⟩
          | _ => throw (IO.userError s!"outer test unhandled raw form: {reprStr node.form}")
        let replayed ← SourceCompilerFeatureSupport.get "outer same applyCoercions suffix"
          (SourceCoreEvidence.applyCoercions base.sourceProgram representation.expressions.projectType compilation caller available
            scope node policy raw node.coercions)
        SourceCompilerFeatureSupport.require (replayed == lowered) "outer actual operand/suffix code changed"
        let outputType ← SourceCompilerFeatureSupport.get "outer result projection"
          (entry.cached.compatible.checked.catalog.project target.resultType)
        let nativeContext := scope.map (fun row => OptionalCell.referenceType row.2) ++
          .unit :: (base.globals.map SourceCoreCalls.Signature.referenceType ++ [.cell indexed.ancestry.layout.frame.type])
        SourceCompilerFeatureSupport.require (lowered.type == outputType &&
          Core.infer? nativeContext lowered.expression indexed.layouts.definitions == some (LanguageResult.resultType outputType))
          "outer actual native code/ordered globals type mismatch"
        found := true
  SourceCompilerFeatureSupport.require found "actual three-step path not reached"
  SourceCompilerFeatureSupport.require (gaps.length == (if targetName == "Final" then 2 else 3))
    "source path method fault positions changed"
  pure (constructor, target, gaps)

private def faultResume (entry : SourceCompilerFeatureSupport.Entry) (arguments : List SourceCoreExecution.Value) : IO Unit := do
  let artifact ← entry.execution.open
  let initial ← SourceCompilerFeatureSupport.boot artifact
  let finished ← SourceCompilerFeatureSupport.get "path public fault"
    (← initial.run entry.key arguments SourceCompilerFeatureSupport.executionOptions)
  let (fault, session) ← match finished with
    | .failed fault session => pure (fault, session)
    | _ => throw (IO.userError "path expected public fault")
  let expected ← SourceCompilerFeatureSupport.get "path fault snapshot" (← session.snapshot 2048)
  for budget in [0, 41, 137] do
    let started ← SourceCompilerFeatureSupport.get "path suspend"
      (← initial.run entry.key arguments {SourceCompilerFeatureSupport.executionOptions with executionFuel := budget})
    let resumed ← match started with
      | .outOfFuel checkpoint => checkpoint.resume 500000 2048
      | outcome => pure outcome
    match resumed with
    | .failed observed session =>
      let snapshot ← SourceCompilerFeatureSupport.get "path resumed snapshot" (← session.snapshot 2048)
      SourceCompilerFeatureSupport.require (observed == fault && reprStr snapshot.cells == reprStr expected.cells)
        "path failure reason or complete source store changed on resume"
    | _ => throw (IO.userError "path failure resume changed outcome")

private def auditBypass (entry : SourceCompilerFeatureSupport.Entry) : IO Unit := do
  let base := entry.cached.indexed.base
  let named ← match base.functions.find? (·.signature.key == entry.key) with
    | some named => pure named | none => throw (IO.userError "bypass caller missing")
  let compilation : SourceCoreFunctions.Context := {
    plan := base.plan, owner := named.signature.key, globals := base.globals, administrativePrefix := 1,
    solvedRequirements := named.specialized.function.solvedRequirements, internalReason := Word.zero }
  let mut count := 0
  for item in named.specialized.function.typedBody.nodes do
    if let .expression node := item then
      if let .call _ _ (.declaration _) := node.form then
        let actual := SourceCoreEvidence.lowerWithProjector base.sourceProgram SourceCoreFunctionTypes.projectType named.specialized
          compilation (fun _ _ _ id _ => .error (.missingExpression id)) 100 named.specialized.function.typedBody [] node.id (fun _ => Word.zero)
        SourceCompilerFeatureSupport.require (node.coercions.isEmpty && node.requirements.isEmpty && (match actual with | .ok none => true | _ => false))
          "empty evidence path must bypass before calling even a rejecting child"
        count := count + 1
  SourceCompilerFeatureSupport.require (count == 1) "bypass actual direct occurrence missing"

private def auditSelectedEmpty (entry : SourceCompilerFeatureSupport.Entry) : IO Unit := do
  let base := entry.cached.indexed.base
  let named ← match base.functions.find? (·.signature.key == entry.key) with
    | some named => pure named | none => throw (IO.userError "empty selected caller missing")
  let compilation : SourceCoreFunctions.Context := {
    plan := base.plan, owner := named.signature.key, globals := base.globals, administrativePrefix := 1,
    solvedRequirements := named.specialized.function.solvedRequirements, internalReason := Word.zero }
  let source := named.specialized.function.typedBody
  let scope := named.inputs.reverse.map (fun (binder, type) => (binder.id, type))
  let child : SourceCoreEvidence.Child := fun fuel source scope id reasonAt => SourceCoreBasic.lowerExpression fuel source scope id (reasonAt id)
  let mut count := 0
  for item in source.nodes do
    if let .expression node := item then
      if let .call _ arguments (.declaration instantiation) := node.form then
        let result ← SourceCompilerFeatureSupport.get "empty selected actual outer"
          (SourceCoreEvidence.lowerWithProjector base.sourceProgram SourceCoreFunctionTypes.projectType named.specialized
            compilation child 100 source scope node.id (fun _ => Word.zero))
        let lowered ← match result with
          | some lowered => pure lowered | none => throw (IO.userError "caller-owned empty suffix lost its authentication")
        let target ← SourceCompilerFeatureSupport.get "empty selected target"
          (SourceCompilationPlan.exactInstantiationKey base.plan instantiation)
        let key ← SourceCompilerFeatureSupport.get "empty selected edge"
          (SourceCompilationPlan.exactCallKey base.plan compilation.owner node.id target)
        let (signature, index) ← match base.globals.zipIdx.filter (fun row => decide (row.1.key = key)) with
          | [row] => pure row | _ => throw (IO.userError "empty selected globals changed")
        let args ← SourceCompilerFeatureSupport.get "empty selected ordered args"
          (arguments.mapM (fun id => child 100 source scope id (fun _ => Word.zero)))
        SourceCompilerFeatureSupport.require (node.coercions.isEmpty && !named.specialized.assumptions.isEmpty &&
          lowered.type == signature.resultType && lowered.expression == SourceCoreCalls.call signature
            (scope.length + compilation.administrativePrefix + index) (SourceCoreCalls.packArguments args).expression compilation.internalReason)
          "empty selected suffix changed raw call code or metadata"
        count := count + 1
  SourceCompilerFeatureSupport.require (count == 1) "empty selected direct occurrence missing"

private def gap (entry : SourceCompilerFeatureSupport.Entry) (name : String) : IO Resolved.LocalId := do
  let binders := entry.cached.indexed.base.functions.flatMap fun named =>
    SourceCoreDataPlaces.declaredBinders named.specialized.function.typedBody
  match binders.filter (·.name == name) with
  | [binder] => pure binder.id
  | _ => throw (IO.userError s!"raw named gap {name} was not unique")

def run : IO Unit := do
  let program ← SourceCompilerFeatureSupport.get "raw named checker" (checkProgram workspace 1024)
  let direct ← SourceCompilerFeatureSupport.compileNamed program "direct"
  let (box, final, pathGaps) ← audit direct "Final"
  let late ← SourceCompilerFeatureSupport.compileNamed program "late"
  let (_, broken, lateGaps) ← audit late "Broken"
  let recursive ← SourceCompilerFeatureSupport.compileNamed program "recursive"
  let _ ← audit recursive "Final"
  let early ← SourceCompilerFeatureSupport.compileNamed program "early"
  let _ ← audit early "Final"
  let secondFault ← SourceCompilerFeatureSupport.compileNamed program "secondFault"
  let _ ← audit secondFault "Final"
  let bodyFault ← SourceCompilerFeatureSupport.compileNamed program "bodyFault"
  let _ ← audit bodyFault "Final"
  let earlyGap ← gap early "rawGap"
  let secondGap ← gap secondFault "rawGap"
  let bodyGap ← gap bodyFault "bodyGap"
  let emptySelected ← SourceCompilerFeatureSupport.compileNamed program "emptySelected"
  auditSelectedEmpty emptySelected
  let bypass ← SourceCompilerFeatureSupport.compileNamed program "bypass"
  auditBypass bypass
  let boxed := SourceTypedRuntime.Value.constructed box [.bool true]
  let output := SourceTypedRuntime.Value.constructed final [boxed]
  for budget in [0, 41, 137, 500000] do
    for input in [0, 1, 2] do
      for (entry, terminalFault, recursiveCall) in [(direct, false, false), (late, true, false), (recursive, false, true)] do
        let started ← entry.audit [SourceCompilerFeatureSupport.scalar input] budget
        let finished ← SourceCompilerFeatureSupport.get "raw named resume" (started.resume 500000)
        let rawPrefix := if recursiveCall then
          [(.word, some (word input)), (.word, some (word 2)),
           (.word, some (word input)), (.word, some (word 1)),
           (.word, some (word input)), (.word, some (word 0))]
          else [(.word, some (word 7)), (.word, some (word 41)),
            (.word, some (word input)), (.word, some (word 43)),
            (.word, some (word 7)), (.word, some (word input)), (.word, some (word 47))]
        let firstCells := [(.word, some (word input))] ++ rawPrefix ++ [(.word, some (word input)), (.word, some (word input))]
        let secondCells := [(.bool, some (.bool (input == 1))),
          (.mapping .bool .word, some (.mapping .bool .word [])), (.word, some (word 0))]
        match finished.observation with
        | .done value state =>
          SourceCompilerFeatureSupport.require (!terminalFault && input == 1 && reprStr value == reprStr output)
            "raw named result changed"
          cells state (firstCells ++ secondCells ++ [(box.resultType, some boxed), (.word, some (word 31)),
            (final.resultType, some output)]) "ordered args/body/all methods"
        | .fault (.uninitializedLocal id) state =>
          if input == 0 then
            SourceCompilerFeatureSupport.require (some id == pathGaps[0]?) "raw named first path fault changed"
            cells state (firstCells ++ [(.bool, none)]) "first method / two skipped"
          else if input == 2 then
            SourceCompilerFeatureSupport.require (some id == pathGaps[1]?) "raw named middle path fault changed"
            cells state (firstCells ++ secondCells ++ [(box.resultType, none)]) "middle method / final skipped"
          else
            SourceCompilerFeatureSupport.require (terminalFault && input == 1 && some id == lateGaps[2]?)
              "raw named final path fault changed"
            cells state (firstCells ++ secondCells ++ [(box.resultType, some boxed), (.word, some (word 37)),
              (broken.resultType, none)]) "final method"
        | other => throw (IO.userError s!"raw named unexpected: {reprStr other}")
    for (entry, expectedGap, expectedCells) in [
      (early, earlyGap, [(.word, some (word 23)), (.word, none)]),
      (secondFault, secondGap, [(.word, some (word 7)), (.word, some (word 41)), (.word, some (word 23)), (.word, none)]),
      (bodyFault, bodyGap, [(.word, some (word 7)), (.word, some (word 41)), (.word, some (word 1)), (.word, some (word 43)),
        (.word, some (word 7)), (.word, some (word 1)), (.word, some (word 53)), (.word, none)])] do
      let started ← entry.audit [] budget
      let finished ← SourceCompilerFeatureSupport.get "raw named prefix resume" (started.resume 500000)
      match finished.observation with
      | .fault (.uninitializedLocal actualGap) state =>
        SourceCompilerFeatureSupport.require (actualGap == expectedGap) "raw named first failure binder changed"
        cells state expectedCells "raw failure / all path skipped"
      | other => throw (IO.userError s!"raw named prefix unexpected: {reprStr other}")
    for entry in [emptySelected, bypass] do
      let started ← entry.audit [SourceCompilerFeatureSupport.scalar 17] budget
      let finished ← SourceCompilerFeatureSupport.get "raw named empty suffix resume" (started.resume 500000)
      match finished.observation with
      | .done value state =>
        SourceCompilerFeatureSupport.require (reprStr value == reprStr (word 17)) "empty named result changed"
        cells state [(.word, some (word 17)), (.word, some (word 17)), (.word, some (word 19))] "empty suffix"
      | other => throw (IO.userError s!"raw named empty suffix unexpected: {reprStr other}")
  emptySelected.checkResume [SourceCompilerFeatureSupport.scalar 17] (.word (Word.ofNatModulo 17)) 41
  bypass.checkResume [SourceCompilerFeatureSupport.scalar 17] (.word (Word.ofNatModulo 17)) 41
  direct.checkResume [SourceCompilerFeatureSupport.scalar 1] (.constructed final [.constructed box [.bool true]]) 41
  recursive.checkResume [SourceCompilerFeatureSupport.scalar 1] (.constructed final [.constructed box [.bool true]]) 41
  faultResume direct [.word Word.zero]
  faultResume direct [.word (Word.ofNatModulo 2)]
  faultResume late [.word (Word.ofNatModulo 1)]
  faultResume early []
  faultResume secondFault []
  faultResume bodyFault []
  IO.println "raw named coercions: actual full ordinary selection/ordered arguments, nested and recursive bodies, empty/first/middle/last paths, argument/body faults, exact heaps and public resume GREEN"

end Tests.SourceCoreCallableCoercionRawNamedCalls
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableCoercionSelectedInvocation
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
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableCoercionSourcePaths
/-! Arbitrary independent source paths consume the actual emitted list, without
selected-dictionary annotations. Runtime tests retain three actual method edges,
ordered repeated evidence, all failure prefixes and exact resumed stores. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
set_option autoImplicit false
namespace Tests.SourceCoreCallableCoercionSourcePaths
open Solcore SourceSemantics SourceSemantics.CoreLowering Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CallableIndexedHistory
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

variable {inputCode outputCode : SourceCoreBasic.LoweredExpr}

include checkedAccepted ledger extension definitions registered faithful observations runtimeViews uninitialized missing in
/-- The actual emitted expression, after a successful operand, preserves the
independent source path. The operand is outside this path-only theorem. -/
theorem independent_success
    (emitted : Emitted compilerProgram project compilation callerFunction available scope node policy ξ inputCode methods outputCode calls)
    {source target : TypeSystem.Ty} (chain : Chain source inputCode.type methods target outputCode.type)
    {caller : Environment} {mapping : LocationMap} {world : StoreTyping}
    {before after : Dynamic.Heap} {initialStore store : Store} {input : Dynamic.Value} {native : Value}
    (entry : Entry methods ambient.definitions caller mapping world before store)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (represented : ValueRep values.checked registry functions mapping world source input native inputCode.type)
    (operand : Evaluates caller initialStore (inputCode.expression.rename ξ) (.inRight .word native) store)
    {sourceResult : Dynamic.Value}
    (trace : Dynamic.CoercionPathExecutes (Program.ofChecked compilerProgram) context evidence before (methods.map (·.step)) input sourceResult after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates caller initialStore (outputCode.expression.rename ξ) value finalStore ∧
      PathOutcome methods before input (.value sourceResult) after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        target outputCode.type faults (.value sourceResult) value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry methods ambient.definitions caller finalMap finalWorld after finalStore) := by
  exact CallableCoercionSourcePathMeaning.emitted_preserves checkedAccepted ledger functions extension definitions registered
    faithful observations runtimeViews uninitialized missing emitted chain entry heaps represented operand trace

include checkedAccepted ledger extension definitions registered faithful observations runtimeViews uninitialized missing in
/-- The actual emitted expression, after a successful operand, preserves the
independent source path. The operand is outside this path-only theorem. -/
theorem independent_fault
    (emitted : Emitted compilerProgram project compilation callerFunction available scope node policy ξ inputCode methods outputCode calls)
    {source target : TypeSystem.Ty} (chain : Chain source inputCode.type methods target outputCode.type)
    {caller : Environment} {mapping : LocationMap} {world : StoreTyping}
    {before after : Dynamic.Heap} {initialStore store : Store} {input : Dynamic.Value} {native : Value}
    (entry : Entry methods ambient.definitions caller mapping world before store)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (represented : ValueRep values.checked registry functions mapping world source input native inputCode.type)
    (operand : Evaluates caller initialStore (inputCode.expression.rename ξ) (.inRight .word native) store)
    {fault : Dynamic.SemanticFault}
    (trace : Dynamic.CoercionPathFaults (Program.ofChecked compilerProgram) context evidence before (methods.map (·.step)) input fault after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates caller initialStore (outputCode.expression.rename ξ) value finalStore ∧
      PathOutcome methods before input (.fault fault) after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        target outputCode.type faults (.fault fault) value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry methods ambient.definitions caller finalMap finalWorld after finalStore) := by
  exact CallableCoercionSourcePathMeaning.emitted_preserves checkedAccepted ledger functions extension definitions registered
    faithful observations runtimeViews uninitialized missing emitted chain entry heaps represented operand trace

include extension definitions registered faithful observations runtimeViews uninitialized missing in
/-- Completion of the actual renamed emitted code yields the independent source
path at the real dictionaries. The known operand trace fixes its reached state
by evaluation determinism; saved captures are never renamed. -/
theorem completed_reflects
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
  exact CallableCoercionSourcePathMeaning.emitted_reflects functions extension definitions registered faithful observations runtimeViews
    uninitialized missing emitted chain entry heaps represented operand completed

/-- Repeated IDs need only their actual singleton row, never list Nodup or a
validity/uniqueness assertion for unrelated ledger rows. -/
theorem repeated_requirement_safe {compiler : CheckedProgram} {caller : SourceSpecialization.SpecializedFunction}
    {node : ExpressionNode} {available : SourceCompilationPlan.EvidenceEnvironment} {context : SourceSemantics.Context}
    {id : RequirementId} {goal : ProgramPredicate} {raw : TypedTraitResolution.Evidence}
    {callerEvidence result : Dynamic.EvidenceEnvironment} {goals : List ProgramPredicate} {failed : RequirementId}
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (accepted : SourceCompilationPlan.exactRuntimeRequirementEvidence compiler caller node available id goal = .ok raw)
    (produces : Dynamic.RequirementsProduceEnvironment context callerEvidence [id, id] goals result)
    (fault : Dynamic.RequirementListFaults context callerEvidence [id, id] failed) : False := by
  apply CallableCoercionRequirementSafety.excludes_list_fault ?_ produces fault
  intro key member
  have same : key = id := by simpa using member
  subst key
  exact CallableCoercionSelectionIdentity.primary_unique ledger accepted

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Box { Box(Bool) }", "enum Final { Final(Box) }", "enum Broken { Broken(Box) }",
    "trait Marker<T> {}", "impl Marker<Word> {}", "impl Marker<Bool> {}", "impl Marker<Box> {}",
    "trait Witness<T> {}", "impl Witness<Word> {}", "impl Witness<Bool> {}", "impl Witness<Box> {}",
    "trait Coerce<From, To> where From: Marker { function coerce(value: From) returns (To) where From: Witness; }",
    "impl Coerce<Word, Bool> where Word: Marker { function coerce(value: Word) returns (Bool) where Word: Witness { let saved: Word = value; if (value == 0) { let firstGap: Bool; return firstGap; } return value == 1; } }",
    "impl Coerce<Bool, Box> where Bool: Marker { function coerce(value: Bool) returns (Box) where Bool: Witness { let m: mapping(Bool => Word); let touched = m[value]; if (value) { return Box(value); } let secondGap: Box; return secondGap; } }",
    "impl Coerce<Box, Final> where Box: Marker { function coerce(value: Box) returns (Final) where Box: Witness { let reached: Word = 31; return Final(value); } }",
    "impl Coerce<Box, Broken> where Box: Marker { function coerce(value: Box) returns (Broken) where Box: Witness { let reached: Word = 37; let lastGap: Broken; return lastGap; } }",
    "function path(value: Word) returns (Final) where Word: Marker, Word: Marker, Bool: Marker, Box: Marker { let result: Final = value; return result; }",
    "function late(value: Word) returns (Broken) where Word: Marker, Bool: Marker, Box: Marker { let result: Broken = value; return result; }",
    "function early() returns (Final) where Word: Marker, Bool: Marker, Box: Marker { let missing: Word; let result: Final = missing; return result; }",
    "function empty(value: Word) returns (Word) { return value; }"
  ]}] }

private def word (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def cells (state : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) (label : String) : IO Unit :=
  SourceCompilerFeatureSupport.require (reprStr (state.heap.map fun cell => (cell.type, cell.value)) == reprStr expected)
    s!"path {label} ordered source cells changed: {reprStr state.heap}"

/-- Inspect the real retained three-edge list and replay the actual compiler
helper against the sealed plan. This also checks each full dictionary in order. -/
private def constructorFor (program : CheckedProgram) (name : String) : IO DataConstructorInstantiation := do
  let data ← match program.signatures.dataTypes.find? (·.name == name) with
    | some data => pure data | none => throw (IO.userError s!"source path {name} missing")
  match data.constructors with
  | [constructor] => pure (DataConstructorInstantiation.mk constructor.id [] constructor.payloadTypes (.nominal data.id []))
  | _ => throw (IO.userError s!"source path {name} constructor missing")

private def audit (entry : SourceCompilerFeatureSupport.Entry) (targetName : String) :
    IO (DataConstructorInstantiation × DataConstructorInstantiation × List Resolved.LocalId) := do
  let base := entry.cached.indexed.base
  let named ← match base.functions.find? (·.signature.key == entry.key) with
    | some named => pure named | none => throw (IO.userError "source path caller missing")
  let caller := named.specialized
  let available ← SourceCompilerFeatureSupport.get "source path caller evidence"
    (SourceCompilationPlan.resolveRuntimeEvidenceEnvironment base.sourceProgram caller.key caller.assumptions)
  let constructor ← constructorFor base.sourceProgram "Box"
  let target ← constructorFor base.sourceProgram targetName
  let mut gaps : List Resolved.LocalId := []
  let mut found := false
  for item in caller.function.typedBody.nodes do
    if let .expression node := item then
      if !node.coercions.isEmpty then
        SourceCompilerFeatureSupport.require (node.coercions.length == 3) "actual coercion path lost its three edges"
        let mut goals : List TypeSystem.Ty := []
        for step in node.coercions do
          let method ← SourceCompilerFeatureSupport.get "path method"
            (SourceCompilationPlan.checkedCoercionMethod base.sourceProgram caller node available step)
          let dictionary ← SourceCompilerFeatureSupport.get "path dictionary"
            (SourceCompilationPlan.coercionMethodRuntimeEvidence base.sourceProgram caller node step method)
          let key ← SourceCompilerFeatureSupport.get "path edge"
            (SourceCompilationPlan.exactCallKey base.plan named.signature.key node.id method.specialized.key)
          let selected ← SourceCompilerFeatureSupport.get "path full selected record"
            (SourceCompilationPlan.exactSpecialization base.plan key)
          let emitted ← match base.functions.find? (·.signature.key == key) with
            | some emitted => pure emitted | none => throw (IO.userError "path native row missing")
          SourceCompilerFeatureSupport.require (selected == method.specialized && emitted.specialized == selected &&
            emitted.inputs.length == 1 && dictionary.length == 3 && dictionary[0]? == dictionary[1]? &&
            dictionary[1]? != dictionary[2]? && dictionary.map SourceCompilationPlan.runtimeEvidenceGoal == selected.assumptions &&
            method.traitPredicates.all caller.assumptions.contains)
            "path full record / ordered repeated dictionary / caller coverage changed"
          goals := goals ++ [step.source, step.target]
          let declared := (SourceCoreDataPlaces.declaredBinders selected.function.typedBody).filter
            (fun binder => binder.name == "firstGap" || binder.name == "secondGap" || binder.name == "lastGap")
          match declared with
          | [binder] => gaps := gaps ++ [binder.id]
          | [] =>
            SourceCompilerFeatureSupport.require (step.target == target.resultType && targetName == "Final")
              "only successful terminal method may lack a gap"
          | _ => throw (IO.userError "source path ambiguous method gap")
        SourceCompilerFeatureSupport.require (goals == [.word, .bool, .bool, constructor.resultType, constructor.resultType, target.resultType])
          "path raw endpoint order changed"
        let compilation : SourceCoreFunctions.Context := {
          plan := base.plan, owner := named.signature.key, globals := base.globals, administrativePrefix := 1,
          solvedRequirements := caller.function.solvedRequirements, internalReason := Word.zero }
        let lowered ← SourceCompilerFeatureSupport.get "path actual applyCoercions"
          (SourceCoreEvidence.applyCoercions base.sourceProgram (SourceCoreCompatibleDataExpressions.projectType entry.cached.compatible.checked) compilation caller available
            [] node {} ⟨.word, LanguageResult.success (.word (Word.ofNatModulo 1))⟩ node.coercions)
        let outputType ← SourceCompilerFeatureSupport.get "path result projection"
          (entry.cached.compatible.checked.catalog.project target.resultType)
        SourceCompilerFeatureSupport.require (lowered.type == outputType &&
          Core.infer? (.unit :: base.globals.map SourceCoreCalls.Signature.referenceType) lowered.expression
            entry.cached.indexed.layouts.definitions == some (LanguageResult.resultType outputType))
          "path actual native code/ordered globals type mismatch"
        found := true
  SourceCompilerFeatureSupport.require found "actual two-step path not reached"
  SourceCompilerFeatureSupport.require (gaps.length == (if targetName == "Final" then 2 else 3))
    "source path method fault positions changed"
  pure (constructor, target, gaps)

private def faultResume (entry : SourceCompilerFeatureSupport.Entry) (arguments : List SourceCoreExecution.Value) : IO Unit := do
  let artifact ← entry.execution.open
  let initial ← SourceCompilerFeatureSupport.boot artifact
  let finished ← SourceCompilerFeatureSupport.get "path public fault"
    (← initial.run entry.key arguments SourceCompilerFeatureSupport.executionOptions)
  let (fault, session) ← match finished with
    | .failed fault session => pure (fault, session)
    | _ => throw (IO.userError "path expected public fault")
  let expected ← SourceCompilerFeatureSupport.get "path fault snapshot" (← session.snapshot 2048)
  for budget in [0, 41, 137] do
    let started ← SourceCompilerFeatureSupport.get "path suspend"
      (← initial.run entry.key arguments {SourceCompilerFeatureSupport.executionOptions with executionFuel := budget})
    let resumed ← match started with
      | .outOfFuel checkpoint => checkpoint.resume 500000 2048
      | outcome => pure outcome
    match resumed with
    | .failed observed session =>
      let snapshot ← SourceCompilerFeatureSupport.get "path resumed snapshot" (← session.snapshot 2048)
      SourceCompilerFeatureSupport.require (observed == fault && reprStr snapshot.cells == reprStr expected.cells)
        "path failure reason or complete source store changed on resume"
    | _ => throw (IO.userError "path failure resume changed outcome")

def run : IO Unit := do
  let program ← SourceCompilerFeatureSupport.get "source paths checker" (checkProgram workspace 1024)
  let path ← SourceCompilerFeatureSupport.compileNamed program "path"
  let (box, final, pathGaps) ← audit path "Final"
  let late ← SourceCompilerFeatureSupport.compileNamed program "late"
  let (_, broken, lateGaps) ← audit late "Broken"
  let early ← SourceCompilerFeatureSupport.compileNamed program "early"
  let _ ← audit early "Final"
  let empty ← SourceCompilerFeatureSupport.compileNamed program "empty"
  let boxed := SourceTypedRuntime.Value.constructed box [.bool true]
  let output := SourceTypedRuntime.Value.constructed final [boxed]
  for budget in [0, 41, 137, 500000] do
    for input in [0, 1, 2] do
      for (entry, terminalFault) in [(path, false), (late, true)] do
        let started ← entry.audit [SourceCompilerFeatureSupport.scalar input] budget
        let finished ← SourceCompilerFeatureSupport.get "source path resume" (started.resume 500000)
        let firstCells := [(.word, some (word input)), (.word, some (word input)), (.word, some (word input))]
        let secondCells := [(.bool, some (.bool (input == 1))),
          (.mapping .bool .word, some (.mapping .bool .word [])), (.word, some (word 0))]
        match finished.observation with
        | .done value state =>
          SourceCompilerFeatureSupport.require (!terminalFault && input == 1 && reprStr value == reprStr output)
            "source path result changed"
          cells state (firstCells ++ secondCells ++ [(box.resultType, some boxed), (.word, some (word 31)),
            (final.resultType, some output)]) "all three methods"
        | .fault (.uninitializedLocal id) state =>
          if input == 0 then
            SourceCompilerFeatureSupport.require (some id == pathGaps[0]?) "source path first fault changed"
            cells state (firstCells ++ [(.bool, none)]) "first fault / two methods skipped"
          else if input == 2 then
            SourceCompilerFeatureSupport.require (some id == pathGaps[1]?) "source path middle fault changed"
            cells state (firstCells ++ secondCells ++ [(box.resultType, none)]) "middle fault / last method skipped"
          else
            SourceCompilerFeatureSupport.require (terminalFault && input == 1 && some id == lateGaps[2]?)
              "source path final fault changed"
            cells state (firstCells ++ secondCells ++ [(box.resultType, some boxed), (.word, some (word 37)),
              (broken.resultType, none)]) "third method fault"
        | other => throw (IO.userError s!"source path unexpected: {reprStr other}")
    let started ← early.audit [] budget
    let finished ← SourceCompilerFeatureSupport.get "source path operand resume" (started.resume 500000)
    match finished.observation with
    | .fault (.uninitializedLocal _) state => cells state [(.word, none)] "operand / all three methods skipped"
    | other => throw (IO.userError s!"source path operand unexpected: {reprStr other}")
    let started ← empty.audit [SourceCompilerFeatureSupport.scalar 17] budget
    let finished ← SourceCompilerFeatureSupport.get "empty path resume" (started.resume 500000)
    match finished.observation with
    | .done value state =>
      SourceCompilerFeatureSupport.require (reprStr value == reprStr (word 17)) "empty path result changed"
      cells state [(.word, some (word 17))] "empty path"
    | other => throw (IO.userError s!"empty path unexpected: {reprStr other}")
  let emptyCaller ← match empty.cached.indexed.base.functions.find? (·.signature.key == empty.key) with
    | some named => pure named.specialized
    | none => throw (IO.userError "empty path caller missing")
  SourceCompilerFeatureSupport.require
    (emptyCaller.function.typedBody.nodes.all fun item => match item with
      | .expression node => node.coercions.isEmpty
      | _ => true) "empty path unexpectedly emitted coercions"
  empty.checkResume [SourceCompilerFeatureSupport.scalar 17] (.word (Word.ofNatModulo 17)) 41
  path.checkResume [SourceCompilerFeatureSupport.scalar 1] (.constructed final [.constructed box [.bool true]]) 41
  faultResume path [.word Word.zero]
  faultResume path [.word (Word.ofNatModulo 2)]
  faultResume late [.word (Word.ofNatModulo 1)]
  faultResume early []
  IO.println "source coercion paths: arbitrary source selectors, actual ordered three-edge records/dictionaries, first/middle/last faults, exact heaps and public resume GREEN"

end Tests.SourceCoreCallableCoercionSourcePaths
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableCoercionSourceSelection
/-! Actual method selection supplies the independent source judgment and exact
ordered dictionary. Runtime checks exercise the same accepted compiler paths;
source body invocation and installed closure history are separate obligations. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
namespace Tests.SourceCoreCallableCoercionSourceSelection
open Solcore Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering TypeSystem
open CallableNamedMetadata (environment)
open CallableCoercionMethodInstantiation (Formation bodyInstance)
open CallableCoercionSourceSelection

/-- Only source formation, caller alignment and the actual three compiler
receipts are inputs. No source-selection/dictionary/body-meaning law is assumed. -/
theorem accepted_source_selection {loaded : LoadedProgram} {program : CheckedProgram}
    (loadedAccepted : Frontend.checkLoadedProgram loaded 1024 = .ok program)
    {caller : SourceSpecialization.SpecializedFunction} {node : ExpressionNode}
    {available dictionary : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    {step : CoercionStep} {method : ExecutableImplMethods.CheckedMethod} {context : SourceSemantics.Context}
    (accepted : SourceCompilationPlan.checkedCoercionMethod program caller node available step = .ok method)
    (formed : ∀ receipt : Certificate program caller node available step method,
      Formation receipt.selected.implementation receipt.selected.declaration)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (SourceSemantics.Context.ofSignatures program.signatures) method.specialized.parameterSubstitution)
    (signatures : context.signatures = program.signatures)
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (assumptions : ∀ goal, goal ∈ caller.assumptions → goal ∈ context.assumptions)
    (resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions = .ok available)
    (covered : CallableCoercionEvidenceOrigins.CallerCovered caller method)
    (materialized : SourceCompilationPlan.coercionMethodRuntimeEvidence program caller node step method = .ok dictionary) :
    Dynamic.OperatorMethodSelected (Program.ofChecked program) context (environment available) "Coerce" "coerce"
      (step.requirement :: step.methodRequirements) (bodyInstance program method) (environment dictionary) := by
  obtain ⟨receipt⟩ := of_accepted accepted
  exact receipt.selects (CallableMethodBodyCoherence.of_loaded loadedAccepted) (formed receipt) range signatures ledger assumptions resolved covered materialized

/-- A reached authentic primary row is enough even when unrelated ledger rows
are not valid. The actual materializer is not replaced with an invented map. -/
theorem reached_requirement {program : CheckedProgram} {caller : SourceSpecialization.SpecializedFunction}
    {node : ExpressionNode} {available : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    {id : RequirementId} {goal : ProgramPredicate} {raw : TypedTraitResolution.Evidence} {context : SourceSemantics.Context}
    (signatures : context.signatures = program.signatures)
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (assumptions : ∀ goal, goal ∈ caller.assumptions → goal ∈ context.assumptions)
    (resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions = .ok available)
    (accepted : SourceCompilationPlan.exactRuntimeRequirementEvidence program caller node available id goal = .ok raw)
    (valid : EvidenceValid [] program.signatures.resolutionRules goal (CallableNamedMetadata.evidence raw)) :
    Dynamic.RequirementProducesEvidence context (environment available) id goal (CallableNamedMetadata.evidence raw) ∧
      SourceCompilationPlan.materializeCallEvidence caller node.id available [id] [goal] = .ok [raw] :=
  ⟨requirement_produces signatures ledger assumptions resolved accepted valid, requirement_materialized accepted⟩

/-- The collector may visit the reverse order of the declaration. Its actual
first-match lookup at either parameter still agrees, without list equality. -/
theorem reversed_collector (first second : TypeParameterId) (different : first ≠ second) :
    let supplied : TypeSystem.ParameterSubstitution := [(first, .word), (second, .bool)]
    ([second, first].map fun key => (key, (supplied.lookup? key).getD (.parameter key))) ≠ supplied ∧
    (TypeSystem.ParameterSubstitution.lookup?
      ([second, first].map fun key => (key, (supplied.lookup? key).getD (.parameter key))) first).getD (.parameter first) = .word ∧
    (TypeSystem.ParameterSubstitution.lookup?
      ([second, first].map fun key => (key, (supplied.lookup? key).getD (.parameter key))) second).getD (.parameter second) = .bool := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro same
    have keys := congrArg (List.map Prod.fst) same
    simp only [List.map_cons, List.map_nil] at keys
    exact different (List.cons.inj keys).1.symm
  · rw [CallableCoercionMethodInstantiation.collected_lookup _ _ (by simp)]
    simp [TypeSystem.ParameterSubstitution.lookup?]
  · rw [CallableCoercionMethodInstantiation.collected_lookup _ _ (by simp)]
    simp [TypeSystem.ParameterSubstitution.lookup?, different]

/-- Groundness is weaker than source type formation: a missing nominal entry
is concrete to specialization but has no well-formed source range. -/
theorem ground_is_not_range (owner : Resolved.DeclarationId) (parameter : TypeParameterId) :
    SourceSpecialization.firstNonConcrete (.constructor (.declaration owner)) = none ∧
      ¬ SourceSemantics.ParameterSubstitution.RangeWellFormed
        (SourceSemantics.Context.ofSignatures ⟨[], [], [], [], [], []⟩) [(parameter, .constructor (.declaration owner))] := by
  refine ⟨rfl, ?_⟩
  intro valid
  have scopeProof := (valid parameter (.constructor (.declaration owner)) (by simp)).typeWellScoped
  generalize typeEq : Ty.constructor (TypeConstructorId.declaration owner) = type at scopeProof
  cases scopeProof <;> simp_all [SourceSemantics.Context.ofSignatures]

private def reorderedWorkspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Coerce<From, To> { function coerce(value: From) returns (To); }",
    "impl<B, A> Coerce<(A, B), Bool> { function coerce(value: (A, B)) returns (Bool) { let visited: Word = 7; return true; } }",
    "function converted(left: Word, right: Bool) returns (Bool) { let value: (Word, Bool) = (left, right); return value; }"
  ]}] }

private def coveredWorkspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Marker<T> {}", "impl Marker<Bool> {}",
    "trait Witness<T> {}", "impl Witness<Bool> {}",
    "trait Coerce<From, To> where From: Marker { function coerce(value: From) returns (To) where From: Witness; }",
    "impl Coerce<Bool, Word> where Bool: Marker { function coerce(value: Bool) returns (Word) where Bool: Witness { return value ? 17 : 4; } }",
    "function covered(flag: Bool) returns (Word) where Bool: Marker, Bool: Marker { return flag; }",
    "function uncovered(flag: Bool) returns (Word) { return flag; }"
  ]}] }

private def audit (entry : SourceCompilerFeatureSupport.Entry) (reordered expectedCovered : Bool) : IO Unit := do
  let base := entry.cached.indexed.base
  let program := base.sourceProgram
  let mut observed := false
  for named in base.functions do
    if named.signature.key == entry.key then
      let caller := named.specialized
      let available ← SourceCompilerFeatureSupport.get "caller resolver32"
        (SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions)
      for item in caller.function.typedBody.nodes do
        match item with
        | .expression node =>
          for step in node.coercions do
            let method ← SourceCompilerFeatureSupport.get "coercion selector"
              (SourceCompilationPlan.checkedCoercionMethod program caller node available step)
            let dictionary ← SourceCompilerFeatureSupport.get "method dictionary"
              (SourceCompilationPlan.coercionMethodRuntimeEvidence program caller node step method)
            let implementation ← match program.signatures.implementations.filter (·.id == method.id.implementation) with
              | [value] => pure value | _ => throw (IO.userError "implementation singleton missing")
            let declaration ← match implementation.methods.filter (·.id == method.id) with
              | [value] => pure value | _ => throw (IO.userError "method singleton missing")
            let trait ← match program.signatures.trait? declaration.traitMethod.trait with
              | some value => pure value | _ => throw (IO.userError "trait missing")
            let retained ← match program.methods.filter (·.id == method.id) with
              | [value] => pure value | _ => throw (IO.userError "retained method missing")
            let primaryRow ← match caller.function.solvedRequirements.filter (·.id == step.requirement) with
              | [value] => pure value | _ => throw (IO.userError "primary singleton missing")
            let matched ← match TypedTraitResolution.matchImplHeadWithParameters? implementation.parameters
                implementation.implRule primaryRow.predicate with
              | some value => pure value | _ => throw (IO.userError "actual head match missing")
            let substitution := method.specialized.parameterSubstitution
            let collector := TypedTraitResolution.ruleParameters implementation.implRule
            SourceCompilerFeatureSupport.require
              (substitution.map Prod.fst == implementation.parameters &&
                ProgramPredicate.applyParameters substitution implementation.head == primaryRow.predicate)
              "source-order head instantiation changed"
            for parameter in implementation.parameters do
              SourceCompilerFeatureSupport.require (substitution.lookup? parameter == matched.parameterSubstitution.lookup? parameter)
                "collector and canonical lookup differ"
            if reordered then
              SourceCompilerFeatureSupport.require (collector == implementation.parameters.reverse && collector != implementation.parameters &&
                substitution.map Prod.snd == [.bool, .word]) "two-parameter order fixture became trivial"
            SourceCompilerFeatureSupport.require
              (method.methodPredicates == declaration.wherePredicates.map (ProgramPredicate.applyParameters substitution) &&
                method.specialized.assumptions == (implementation.methodAssumptions trait declaration).map (ProgramPredicate.applyParameters substitution) &&
                dictionary.map SourceCompilationPlan.runtimeEvidenceGoal == method.specialized.assumptions)
              "source requirements or ordered dictionary changed"
            let covered := method.traitPredicates.all caller.assumptions.contains
            SourceCompilerFeatureSupport.require (covered == expectedCovered) "caller coverage profile changed"
            let headers ← SourceCompilerFeatureSupport.get "header resolver32"
              (SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program method.specialized.key method.traitPredicates)
            SourceCompilerFeatureSupport.require
              (dictionary == headers ++ method.implementationPremises ++ method.methodPremises)
              "actual dictionary lost an ordered component"
            if covered then
              for fresh in headers do
                let found := available.find? fun raw => SourceCompilationPlan.runtimeEvidenceGoal raw == SourceCompilationPlan.runtimeEvidenceGoal fresh
                SourceCompilerFeatureSupport.require (found == some fresh) "caller first match differs from fresh full evidence"
            if !reordered then
              SourceCompilerFeatureSupport.require (dictionary.length == 3 &&
                dictionary[0]? == dictionary[1]? && dictionary[1]? != dictionary[2]?) "duplicate/header/method order not exercised"
            let emitted ← SourceCompilerFeatureSupport.get "actual selected full carrier"
              (SourceCompilationPlan.exactSpecialization base.plan method.specialized.key)
            SourceCompilerFeatureSupport.require (emitted == method.specialized &&
              emitted.function.typedBody == StructuralSubstitution.applyTypedSource substitution retained.checked.typedBody &&
              emitted.function.solvedRequirements == retained.checked.solvedRequirements.map
                (StructuralSubstitution.applySolvedRequirement substitution) &&
              emitted.function.typedBody.owner == implementation.id)
              "selected source body/owner/ordered ledger changed"
            observed := true
        | _ => pure ()
  SourceCompilerFeatureSupport.require observed "actual coercion site was not reached"

def run : IO Unit := do
  let reordered ← SourceCompilerFeatureSupport.get "two-parameter checker" (checkProgram reorderedWorkspace 1024)
  let entry ← SourceCompilerFeatureSupport.compileNamed reordered "converted"
  audit entry true true
  entry.checkResume [SourceCompilerFeatureSupport.scalar 8, .bool false] (.bool true) 7
  let covered ← SourceCompilerFeatureSupport.get "dictionary checker" (checkProgram coveredWorkspace 1024)
  for name in ["covered", "uncovered"] do
    let entry ← SourceCompilerFeatureSupport.compileNamed covered name
    audit entry false (name == "covered")
    entry.checkResume [.bool true] (SourceCompilerFeatureSupport.scalar 17) 7
    SourceCompilerFeatureSupport.require ((← entry.run [.bool false]) == SourceCompilerFeatureSupport.scalar 4)
      "source selection fixture false result changed"
  IO.println "coercion source selection: collector/declaration order, retained body, full dictionaries, duplicate goals and covered/uncovered profiles GREEN"

end Tests.SourceCoreCallableCoercionSourceSelection
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableCoercionSpine
/-! Actual helper acceptance supplies ordered static receipts. Native tests
observe saved captures, early failure, duplicate calls and hidden caller slots.
The public source fixture exercises coercion effects and failure/resumption;
source method selection/body correspondence remains a separate obligation. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreCallableCoercionSpine
open Solcore Core Frontend SourceInference SourceSemantics.CoreLowering
open CallableCoercionSpine

/-- One real helper action supplies every selector, dictionary and code receipt,
and completed native execution supplies every actual saved-body trace. -/
theorem accepted_completed {program : CheckedProgram} {project : Projector} {context : CallableCoercionSpine.Context}
    {caller : Specialized} {available : RuntimeEvidence} {scope : Scope} {node : ExpressionNode}
    {policy : SourceCoreFunctions.CallablePolicy} {input output : Lowered} {steps : List CoercionStep}
    (accepted : SourceCoreEvidence.applyCoercions program project context caller available scope node policy input steps = .ok output)
    (ξ : Renaming) {environment : Environment} {before after : Store} {value : Value} :
    ∃ calls, Spine program project context caller available scope node policy input steps output calls ∧
      calls.length = steps.length ∧
      (Evaluates environment before (output.expression.rename ξ) value after ↔
        ∃ initial middle, Evaluates environment before (input.expression.rename ξ) initial middle ∧
          Runs environment context.internalReason middle initial (calls.map (Call.rename ξ)) value after) := by
  obtain ⟨calls, receipt⟩ := of_accepted accepted
  exact ⟨calls, receipt, receipt.length, receipt.renamed_completed_iff ξ⟩

theorem accepted_initial_failure {program : CheckedProgram} {project : Projector} {context : CallableCoercionSpine.Context}
    {caller : Specialized} {available : RuntimeEvidence} {scope : Scope} {node : ExpressionNode}
    {policy : SourceCoreFunctions.CallablePolicy} {input output : Lowered} {steps : List CoercionStep}
    (accepted : SourceCoreEvidence.applyCoercions program project context caller available scope node policy input steps = .ok output)
    {environment : Environment} {before reached after : Store} {reason : Word} {value : Value}
    (failed : Evaluates environment before input.expression (.inLeft input.type (.word reason)) reached)
    (completed : Evaluates environment before output.expression value after) :
    value = .inLeft output.type (.word reason) ∧ after = reached := by
  obtain ⟨_, receipt⟩ := of_accepted accepted
  exact evaluation_deterministic completed (receipt.input_failure failed)

private def writingBody (reason : Word) : Expr :=
  .letE (.storeCell (.var 1) (.word (Word.ofNatModulo 7))) (.inLeft .word (.word reason))
private def capturedClosure (reason : Word) : Value :=
  .closure .unit (LanguageResult.resultType .word) (writingBody reason) [.cellRef .word 0]
private def initialStore (reason : Word) : Store := [.word Word.zero, .inRight .unit (capturedClosure reason)]
private def finalStore (reason : Word) : Store := [.word (Word.ofNatModulo 7), .inRight .unit (capturedClosure reason)]
private def cellType : Ty := OptionalCell.cellType (.function .unit (LanguageResult.resultType .word))
private def firstCall (key : Key) (index : Nat) : Call := ⟨⟨key, .unit, .word⟩, index⟩
private def lastCall (key : Key) : Call := ⟨⟨key, .word, .bool⟩, 400⟩

/-- The first actual saved body writes through its captured cell and fails.
The nonexistent second global is never read; the returned store retains exactly
that first write and the same saved capture. -/
theorem captured_failure_skips_suffix (key : Key) (reason : Word)
    {environment : Environment} {index : Nat}
    (reference : environment[index]? = some (.cellRef cellType 1)) :
    Evaluates environment (initialStore reason)
      (emit Word.zero (LanguageResult.success .unit) [firstCall key index, lastCall key])
      (.inLeft .bool (.word reason)) (finalStore reason) := by
  apply emit_evaluates_iff.mpr
  refine ⟨_, _, .inRight .unit, .cons (.applied reference rfl ?_) (.cons (Invoke.skipped (tag := .word)) .nil)⟩
  exact .letE (.storeCell (.var rfl) rfl .word (by simp [initialStore, finalStore, Store.write?])) (.inLeft .word)

/-- Moving the caller slot past two temporaries leaves the saved body and
capture unchanged; this is evaluation of the real renamed helper syntax. -/
theorem hidden_slots_same_capture (key : Key) (reason : Word) :
    Evaluates [.integer 3, .bool false, .cellRef cellType 1] (initialStore reason)
      ((emit Word.zero (LanguageResult.success .unit) [firstCall key 0, lastCall key]).rename (fun index => index + 2))
      (.inLeft .bool (.word reason)) (finalStore reason) := by
  rw [emit_rename]
  apply emit_evaluates_iff.mpr
  refine ⟨_, _, .inRight .unit, .cons (.applied rfl rfl ?_) (.cons (Invoke.skipped (tag := .word)) .nil)⟩
  exact .letE (.storeCell (.var rfl) rfl .word (by simp [initialStore, finalStore, Store.write?])) (.inLeft .word)

/-- Two identical selected slots are still two calls. Their saved bodies both
allocate, so the native trace records two distinct heap extensions. -/
theorem duplicate_call_order (key : Key) :
    let signature : SourceCoreCalls.Signature := ⟨key, .unit, .unit⟩
    let body : Expr := .letE (.newCell .word (.word Word.zero)) (LanguageResult.success .unit)
    let closure : Value := .closure .unit (LanguageResult.resultType .unit) body []
    Evaluates [.cellRef (OptionalCell.cellType signature.functionType) 0] [.inRight .unit closure]
      (emit Word.zero (LanguageResult.success .unit) [⟨signature, 0⟩, ⟨signature, 0⟩])
      (.inRight .word .unit) [.inRight .unit closure, .word Word.zero, .word Word.zero] := by
  dsimp only
  apply emit_evaluates_iff.mpr
  refine ⟨_, _, .inRight .unit, .cons (middle := [.inRight .unit (.closure .unit (LanguageResult.resultType .unit) (.letE (.newCell .word (.word Word.zero)) (LanguageResult.success .unit)) []), .word Word.zero]) (result := .inRight .word .unit) (.applied rfl rfl ?_) (.cons (.applied rfl rfl ?_) .nil)⟩
  · exact .letE (.newCell .word) (.inRight .unit)
  · exact .letE (.newCell .word) (.inRight .unit)

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Coerce<From, To> { function coerce(value: From) returns (To); }",
    "impl Coerce<Bool, Word> { function coerce(value: Bool) returns (Word) { let table: mapping(Word => Word); table[0] = 7; if (value) { table[0] += 2; return table[0]; } let absent: Word; return absent; } }",
    "function converted(flag: Bool) returns (Word) { return flag; }",
    "function failed() returns (Word) { let result: Word = false; let skipped: mapping(Word => Word); skipped[8] = 90; return result; }",
    "function captured() returns (function() returns (Word)) { let result: Word = true; return lam() { return result; }; }"
  ]}] }

/-- Re-enter the actual compiler helper on reached checked coercion lists. Its
input is a literal of the actual raw projected type; method selection and the
ordered runtime dictionaries still come from the sealed prepared plan. -/
private def audit (entry : SourceCompilerFeatureSupport.Entry) : IO Nat := do
  let base := entry.cached.indexed.base
  let mut reached := 0
  for named in base.functions do
    let context : SourceCoreFunctions.Context := {
      plan := base.plan, owner := named.signature.key, globals := base.globals,
      administrativePrefix := 1, solvedRequirements := named.specialized.function.solvedRequirements,
      internalReason := Word.zero }
    let available ← SourceCompilerFeatureSupport.get "coercion caller evidence"
      (SourceCompilationPlan.resolveRuntimeEvidenceEnvironment base.sourceProgram named.signature.key named.specialized.assumptions)
    for item in named.specialized.function.typedBody.nodes do
      match item with
      | .expression node =>
        if !node.coercions.isEmpty then
          let inputType ← SourceCompilerFeatureSupport.get "coercion raw input projection"
            (SourceCoreFunctionTypes.projectType (.occurrence node.id.occurrence) node.rawType)
          let input : Expr ← match inputType with
            | .bool => pure (.bool true)
            | .word => pure (.word Word.zero)
            | .integer => pure (.integer 0)
            | _ => throw (IO.userError "unexpected coercion fixture raw type")
          let lowered ← SourceCompilerFeatureSupport.get "actual ordered coercion helper"
            (SourceCoreEvidence.applyCoercions base.sourceProgram SourceCoreFunctionTypes.projectType context named.specialized available
              [] node {} ⟨inputType, LanguageResult.success input⟩ node.coercions)
          let outputType ← SourceCompilerFeatureSupport.get "coercion final projection"
            (SourceCoreFunctionTypes.projectType (.occurrence node.id.occurrence) node.type)
          let nativeContext := .unit :: base.globals.map SourceCoreCalls.Signature.referenceType
          SourceCompilerFeatureSupport.require (lowered.type == outputType &&
            Core.infer? nativeContext lowered.expression entry.cached.indexed.layouts.definitions == some (LanguageResult.resultType outputType))
              "coercion helper lost exact input/output or ordered global slots"
          reached := reached + 1
      | _ => pure ()
  pure reached

private def faultResume (entry : SourceCompilerFeatureSupport.Entry) : IO Unit := do
  let baseline ← entry.invoke []
  let (reason, session) ← match baseline.outcome with
    | .failed reason session => pure (reason, session)
    | _ => throw (IO.userError "coercion body failure disappeared")
  let snapshot ← SourceCompilerFeatureSupport.get "coercion fault snapshot" (← session.snapshot 2048)
  entry.checkCells [] [
    (.bool, some (.bool false)),
    (.mapping .word .word, some (.mapping .word .word
      [(SourceCompilerFeatureSupport.scalar 0, SourceCompilerFeatureSupport.scalar 7)])),
    (.word, none)]
  for spent in [0, 13, 67] do
    let started ← SourceCompilerFeatureSupport.get "coercion fault suspend"
      (← baseline.initial.run baseline.key [] {SourceCompilerFeatureSupport.executionOptions with executionFuel := spent})
    let resumed ← match started with
      | .outOfFuel checkpoint => checkpoint.resume 300000 2048
      | done => pure done
    match resumed with
    | .failed actual session =>
      let observed ← SourceCompilerFeatureSupport.get "coercion fault resumed snapshot" (← session.snapshot 2048)
      SourceCompilerFeatureSupport.require (actual == reason && reprStr observed.cells == reprStr snapshot.cells)
        "coercion failed store or reason changed on resume"
    | _ => throw (IO.userError "coercion failure resume changed outcome")

def run : IO Unit := do
  let program ← SourceCompilerFeatureSupport.get "coercion spine checker" (checkProgram workspace)
  let converted ← SourceCompilerFeatureSupport.compileNamed program "converted"
  SourceCompilerFeatureSupport.require ((← audit converted) > 0) "actual coercion helper not reached"
  converted.checkResume [.bool true] (SourceCompilerFeatureSupport.scalar 9) 11
  let failed ← SourceCompilerFeatureSupport.compileNamed program "failed"
  SourceCompilerFeatureSupport.require ((← audit failed) > 0) "failed coercion helper not reached"
  faultResume failed
  let captured ← SourceCompilerFeatureSupport.compileNamed program "captured"
  let created ← captured.invoke []
  let completed ← match created.outcome with
    | .succeeded completion => pure completion
    | _ => throw (IO.userError "coercion/capture fixture failed")
  let handle ← match completed.value with
    | .function handle => pure handle
    | _ => throw (IO.userError "coercion capture handle missing")
  let invoked ← SourceCompilerFeatureSupport.get "captured coercion result"
    (← completed.session.invokePacked handle .unit SourceCompilerFeatureSupport.executionOptions)
  match invoked with
  | .succeeded completion =>
    SourceCompilerFeatureSupport.require (completion.value == SourceCompilerFeatureSupport.scalar 9)
      "captured coerced cell changed"
  | _ => throw (IO.userError "captured coerced cell invocation failed")
  IO.println "coercion spine: actual helper, ordered calls, failure store, captures and resume GREEN"

end Tests.SourceCoreCallableCoercionSpine
end

section
-- leanmerge: from Solcore.Test.SourceCoreCoercionPublicOrdinarySupport
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCoercionPublic
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)

variable {fixture : CompiledFixture}
  {inputs : List (Input fixture.recipe.compiled)} (rows : Inventory inputs)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (methods : CallableIndexedOwnedPreparedStagedClosedCoercionSelection.Catalog fixture.recipe.compiled)

local notation "actualRegistry" => RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)
local notation "faults" => CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics

/- The actual finite Source checker supplies the complete metadata and body
syntax for use. Only authentic Header/source alignment is transported here. -/
include rows receiver methods in
theorem ActualHeader.use_admitted_support (observed : ObservedProgram fixture)
    (actual : ActualHeader fixture observed.useRow.row)
    {bodyRegistry : SourceCoreRawMetadata.Registry} :
    Nonempty (Σ body : CallableIndexedOwnedPreparedStagedNamedBodies.Body actual.header,
      CallableIndexedOwnedPreparedStagedPhysicalNamedBodySupport.Support
        (headers := headers rows) (bodyRegistry := bodyRegistry)
        (stages := actualRegistry) (semanticFaults := faults) actual.header body) := by
  have indexEq := (observed.useRow.prepared_slot actual.prepared).2
  have selected : fixture.recipe.compiled.indexed.base.functions[observed.useRow.index]? =
      some actual.prepared.named := indexEq ▸ actual.prepared.selected
  have namedEq : actual.prepared.named = observed.useRow.named :=
    Option.some.inj (selected.symm.trans observed.useRow.cached)
  have bodyEq : actual.header.function.body = [observed.useShape.body.statement.id] := by
    rw [actual.aligned.function]
    change actual.prepared.compilation.statements = [observed.useShape.body.statement.id]
    have accepted := actual.prepared.compilation.roots
    change (actual.prepared.named.specialized.function.typedBody.roots.mapM _) = _ at accepted
    rw [actual.prepared.same, observed.useShape.body.roots] at accepted
    exact (Except.ok.inj accepted).symm
  have resultEq : actual.header.function.resultType = .word := by
    rw [actual.header.agreement.result, actual.aligned.named, actual.prepared.same]
    exact observed.useResultType
  have admission : CallableIndexedOwnedPreparedNamedScopedAdmission.Admission actual.prepared actual.header [] := by
    change CallableIndexedOwnedPreparedNamedScopedAdmission.SourceAdmission fixture.recipe.compiled
      actual.prepared.named actual.header.function.source actual.header.function.body actual.header.function.resultType []
    rw [namedEq, actual.source, bodyEq, resultEq]
    exact observed.useAdmission
  obtain ⟨loaded, checked⟩ := fixture.loaded
  have checked := CallableMethodBodyCoherence.of_loaded checked
  exact CallableIndexedOwnedPreparedNamedCatalogAdmission.of_empty_actual rows actual.prepared actual.aligned admission
    fixture.recipePrepared actual.diagnostic receiver fixture.source_wellFormed checked
    (by rw [fixture.sameProgram]; exact CallableCoercionSelectionIdentity.Catalog.of_checked fixture.checked)
    (.generic ⟨methods.formed, methods.assumptions⟩) observed.makeRow.entryMember (actualStagePrepared fixture)

/- The actual compiler body receipt supplies keep statement structure. -/
include rows receiver methods in
theorem ActualHeader.keep_admitted_support (observed : ObservedProgram fixture)
    (actual : ActualHeader fixture observed.keepRow.row)
    {bodyRegistry : SourceCoreRawMetadata.Registry} :
    Nonempty (Σ body : CallableIndexedOwnedPreparedStagedNamedBodies.Body actual.header,
      CallableIndexedOwnedPreparedStagedPhysicalNamedBodySupport.Support
        (headers := headers rows) (bodyRegistry := bodyRegistry)
        (stages := actualRegistry) (semanticFaults := faults) actual.header body) := by
  exact actual.keep_compiler_support rows receiver
    (.generic ⟨methods.formed, methods.assumptions⟩) observed

end Tests.SourceCoreCoercionPublic
end
