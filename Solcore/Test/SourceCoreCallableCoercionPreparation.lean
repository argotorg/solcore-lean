import Solcore.SourceSemantics.CoreLowering.CallableCoercionPreparation
import Solcore.SourceSemantics.CoreLowering.CallableCoercionBodyProvenance
import Solcore.SourceSemantics.CoreLowering.CallableCoercionEvidenceOrigins
import Solcore.Test.SourceCompilerFeatureSupport

/-! Outer preparation supplies actual method-extension witnesses, including
coercions inside appended carriers. Formal consumers retain same-fuel source
body provenance and the explicit caller-covered dictionary boundary. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
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
  obtain ⟨receipt⟩ := CallableCoercionBodyProvenance.of_accepted loadedAccepted step.selectedMethod
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
