import Solcore.SourceSemantics.CoreLowering.CallableCallEvidence
import Solcore.Test.SourceCompilerFeatureSupport

/-! Actual ordered materialization, including repeated IDs/goals, is related
to independent source evidence. Rejected selection and forged implementation
fixtures distinguish successful metadata checks from semantic validity. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreCallableCallEvidence
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CallableNamedMetadata (evidence environment)
open CallableEvidenceEnvironment CallableCallEvidence

/-- Resolve and materialize actual dictionaries, then identify any independently
produced dictionary. No source production or caller-validity premise is used
to construct the first conjunct. -/
theorem actual_call_dictionary {program : CheckedProgram} {caller : SourceSpecialization.SpecializedFunction}
    {occurrence : ExpressionId} {available result : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    {ids : List RequirementId} {predicates : List ProgramPredicate} {context : SourceSemantics.Context}
    (signatures : context.signatures = program.signatures)
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (retained : SolvedRequirementsValid context caller.function.solvedRequirements)
    (resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions = .ok available)
    (accepted : SourceCompilationPlan.materializeCallEvidence caller occurrence available ids predicates = .ok result) :
    Dynamic.RequirementsProduceEnvironment context (environment available) ids predicates (environment result) ∧
      ∀ semantic, Dynamic.RequirementsProduceEnvironment context (environment available) ids predicates semantic →
        semantic = environment result :=
  ⟨produces_of_resolved signatures ledger retained resolved accepted, fun _ produced => agrees ledger accepted produced⟩

private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def goal : ProgramPredicate := ProgramSignatures.builtinIntWordRule.head
private def raw : TypedTraitResolution.Evidence := .byImpl goal (.builtin .intWord) []
private def alternate : TypedTraitResolution.Evidence := .byImpl goal (.builtin .intInteger) []
private def concrete : SolvedRequirement := ⟨⟨0⟩, goal, .implementation raw⟩
private def assumed : SolvedRequirement := ⟨⟨1⟩, goal, .assumption goal⟩
private def unrelated : SolvedRequirement := ⟨⟨2⟩, goal, .implementation raw⟩
private def rows : List SolvedRequirement := [concrete, assumed, unrelated, unrelated]
private def context : SourceSemantics.Context := {
  signatures, locals := [], assumptions := [goal], solvedRequirements := rows }
private def callerWith (seed : SourceSpecialization.SpecializedFunction) (ledger : List SolvedRequirement) :=
  { seed with function := { seed.function with solvedRequirements := ledger } }

private theorem raw_valid : EvidenceValid [] signatures.resolutionRules goal (evidence raw) := by
  simp only [raw, CallableNamedMetadata.evidence, List.map_nil]
  apply EvidenceValid.implementation (rule := ProgramSignatures.builtinIntWordRule)
    (by simp [signatures, ProgramSignatures.resolutionRules, ProgramSignatures.builtinResolutionRules]) rfl
    (TraitResolutionSoundness.matchImplHead?_sound (by decide)) .nil

private theorem rows_valid : SolvedRequirementsValid context rows := by
  intro row member
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact .intro (.intro (.implementation (CallableNamedMetadata.evidence_represents raw))
      (raw_valid.weakenAssumptions (by simp)))
  · exact .intro (.intro (.assumption goal) (.assumption (by simp [context, assumed])))
  all_goals exact .intro (.intro (.implementation (CallableNamedMetadata.evidence_represents raw))
    (raw_valid.weakenAssumptions (by simp)))

private theorem available_valid : (environment [raw, alternate]).Valid signatures.resolutionRules := by
  intro selected output found
  cases found with
  | head => exact raw_valid
  | tail different found =>
    cases found with
    | head => exact (different rfl).elim
    | tail _ found => cases found

/-- First match preserves the first entire tree despite equal later goals. The
requested spine repeats an ID; unrelated duplicate ledger IDs are untouched. -/
theorem ordered_mixed (seed : SourceSpecialization.SpecializedFunction) (occurrence : ExpressionId) :
    SourceCompilationPlan.materializeCallEvidence (callerWith seed rows) occurrence [raw, alternate]
      [⟨1⟩, ⟨0⟩, ⟨1⟩] [goal, goal, goal] = .ok [raw, raw, raw] ∧
    Dynamic.RequirementsProduceEnvironment context (environment [raw, alternate])
      [⟨1⟩, ⟨0⟩, ⟨1⟩] [goal, goal, goal] (environment [raw, raw, raw]) := by
  have accepted : SourceCompilationPlan.materializeCallEvidence (callerWith seed rows) occurrence [raw, alternate]
      [⟨1⟩, ⟨0⟩, ⟨1⟩] [goal, goal, goal] = .ok [raw, raw, raw] := rfl
  exact ⟨accepted, produces rfl rows_valid available_valid accepted⟩

theorem actual_duplicate_rejected (seed : SourceSpecialization.SpecializedFunction) (occurrence : ExpressionId) :
    SourceCompilationPlan.materializeCallEvidence (callerWith seed [concrete, concrete]) occurrence []
      [⟨0⟩] [goal] = .error (.duplicateSolvedRequirements seed.key occurrence ⟨0⟩ 2) := rfl

theorem absent_assumption_rejected (seed : SourceSpecialization.SpecializedFunction) (occurrence : ExpressionId) :
    SourceCompilationPlan.materializeCallEvidence (callerWith seed [assumed]) occurrence [] [⟨1⟩] [goal] =
      .error (.missingRuntimeAssumptionEvidence seed.key occurrence ⟨1⟩ goal) := rfl

private def forged (owner : Resolved.DeclarationId) : TypedTraitResolution.Evidence := .byImpl goal (.declaration owner) []
private theorem forged_invalid (owner : Resolved.DeclarationId) :
    ¬ EvidenceValid [] signatures.resolutionRules goal (evidence (forged owner)) := by
  simp only [forged, CallableNamedMetadata.evidence, List.map_nil]
  intro valid
  cases valid with
  | implementation member identity _ _ =>
    simp only [signatures, ProgramSignatures.resolutionRules, ProgramSignatures.builtinResolutionRules,
      List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> cases identity

/-- Materialization checks goals and exact IDs, but deliberately does not
rerun implementation selection. This accepted forged tree has no independent
closed validity and therefore cannot supply a source production judgment. -/
theorem success_not_validity (seed : SourceSpecialization.SpecializedFunction) (occurrence : ExpressionId) :
    let entry : SolvedRequirement := ⟨⟨0⟩, goal, .implementation (forged seed.declaration)⟩
    SourceCompilationPlan.materializeCallEvidence (callerWith seed [entry]) occurrence [] [⟨0⟩] [goal] =
      .ok [forged seed.declaration] ∧
    ¬ Dynamic.RequirementsProduceEnvironment context [] [⟨0⟩] [goal] (environment [forged seed.declaration]) := by
  refine ⟨rfl, ?_⟩
  intro produced
  cases produced with
  | cons head _ => exact forged_invalid seed.declaration head.closed_valid

/-- No reordering or erasure of recursive premises occurs when closed trees
are passed through the materializer's implementation branch. -/
theorem deep_closed (caller : Dynamic.EvidenceEnvironment) (left right : TypedTraitResolution.Evidence) :
    Dynamic.EvidenceCloses caller
      (evidence (.byImpl goal (.builtin .intWord) [left, right]))
      (.implementation goal (.builtin .intWord) [evidence left, evidence right]) := by
  simpa only [CallableNamedMetadata.evidence, List.map_cons, List.map_nil] using
    closes_self caller (.byImpl goal (.builtin .intWord) [left, right])

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Mark<T> {}", "impl Mark<Word> {}", "enum Box<T> { Wrap(T) }",
    "impl<T> Mark<Box<T>> where T: Mark {}",
    "function keep<T>(value: T) returns (T) where T: Mark { return value; }",
    "function forward<T>(value: T) returns (T) where T: Mark { return keep(value); }",
    "function concrete(seed: Word) returns (Word) { let value = Box.Wrap(Box.Wrap(seed)); forward(value); return seed; }",
    "function failed(seed: Word) returns (Word) { forward(seed); let absent: Word; return absent; }"
  ]}] }

private def depth : TypedTraitResolution.Evidence → Nat
  | .byImpl _ _ premises => 1 + (premises.map depth).foldl Nat.max 0

private def audit (entry : SourceCompilerFeatureSupport.Entry) : IO Unit := do
  let prepared := entry.cached.indexed
  let mut assumptions := 0
  let mut concrete := 0
  let mut deepest := 0
  for named in prepared.base.functions do
    let available ← SourceCompilerFeatureSupport.get "caller evidence"
      (SourceCompilationPlan.resolveRuntimeEvidenceEnvironment prepared.base.sourceProgram named.signature.key named.specialized.assumptions)
    for node in named.specialized.function.typedBody.nodes do
      match node with
      | .expression node =>
        match node.form with
        | .call _ _ (.declaration instantiation) =>
          if node.coercions.isEmpty then
            let result ← SourceCompilerFeatureSupport.get "actual call evidence"
              (SourceCompilationPlan.materializeCallEvidence named.specialized node.id available node.requirements instantiation.predicates)
            SourceCompilerFeatureSupport.require (decide (result.map SourceCompilationPlan.runtimeEvidenceGoal = instantiation.predicates))
              "call evidence order or multiplicity changed"
            for item in result do deepest := max deepest (depth item)
            for requirement in node.requirements do
              match named.specialized.function.solvedRequirements.find? (fun row => row.id == requirement) with
              | some {evidence := .assumption _, ..} => assumptions := assumptions + 1
              | some {evidence := .implementation _, ..} => concrete := concrete + 1
              | none => throw (IO.userError "missing actual call requirement")
        | _ => pure ()
      | _ => pure ()
  SourceCompilerFeatureSupport.require (assumptions > 0 && concrete > 0 && deepest ≥ 3)
    "evidence fixture lost mixed/deep actual compiler coverage"

def run : IO Unit := do
  let program ← SourceCompilerFeatureSupport.get "call evidence checker" (checkProgram workspace)
  let entry ← SourceCompilerFeatureSupport.compileNamed program "concrete"
  audit entry
  entry.checkResume [SourceCompilerFeatureSupport.scalar 9] (SourceCompilerFeatureSupport.scalar 9) 11
  let failed ← SourceCompilerFeatureSupport.compileNamed program "failed"
  let baseline ← failed.invoke [SourceCompilerFeatureSupport.scalar 7]
  let (reason, session) ← match baseline.outcome with
    | .failed reason session => pure (reason, session)
    | _ => throw (IO.userError "qualified call did not reach expected later fault")
  let snapshot ← SourceCompilerFeatureSupport.get "evidence fault snapshot" (← session.snapshot 2048)
  for spent in [0, 13, 67] do
    let started ← SourceCompilerFeatureSupport.get "evidence fault suspend"
      (← baseline.initial.run baseline.key [SourceCompilerFeatureSupport.scalar 7]
        {SourceCompilerFeatureSupport.executionOptions with executionFuel := spent})
    let resumed ← match started with
      | .outOfFuel checkpoint => checkpoint.resume 300000 2048
      | done => pure done
    match resumed with
    | .failed actual session =>
      let observed ← SourceCompilerFeatureSupport.get "evidence fault resume snapshot" (← session.snapshot 2048)
      SourceCompilerFeatureSupport.require (actual == reason && reprStr observed.cells == reprStr snapshot.cells)
        "qualified evidence call changed failure prefix or resume"
    | _ => throw (IO.userError "qualified evidence resume changed outcome")
  IO.println "call evidence: exact ordered materialization, recursive proofs, first-match duplicates and qualified resume GREEN"

end Tests.SourceCoreCallableCallEvidence
