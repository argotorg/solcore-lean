import Solcore.SourceSemantics.CoreLowering.CallableCoercionEvidenceOrigins
import Solcore.Test.SourceCompilerFeatureSupport

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
