import Solcore.SourceSemantics.CoreLowering.CallableCallRequirementLayouts
import Solcore.Frontend.SourceCoreLocalEvidence
import Solcore.Test.SourceCompilerFeatureSupport

/-! Reached evidence validity comes from actual caller resolution, ordered
materialization and callee authentication. Unrelated invalid templates, exact
coercion placement and contextual local rebinding remain distinguishable. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreCallableAuthenticatedCallEvidence
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CallableNamedMetadata (evidence environment)

/-- Successful public direct-call selection determines both independent
production and the exact source dictionary, without whole-ledger validity. -/
theorem actual_direct_dictionary {program : CheckedProgram} {caller : SourceSpecialization.SpecializedFunction}
    {node : ExpressionNode} {instantiation : DeclarationInstantiation}
    {available actual : SourceTypedRuntime.RuntimeEvidenceEnvironment} {context : SourceSemantics.Context}
    {callee : SourceCompilationPlan.Key}
    (signatures : context.signatures = program.signatures)
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (assumptions : ∀ goal, goal ∈ caller.assumptions → goal ∈ context.assumptions)
    (unique : RequirementIdsUnique context)
    (resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions = .ok available)
    (accepted : SourceCompilationPlan.exactDirectCallRuntimeEvidence caller node available instantiation = .ok actual)
    (authenticated : SourceCompilationPlan.validateAuthenticatedRuntimeEvidence program.signatures callee instantiation.predicates actual = .ok ()) :
    Dynamic.DirectCallProducesEvidence context (environment available) node.requirements node.coercions instantiation.predicates (environment actual) ∧
      ∀ semantic, Dynamic.DirectCallProducesEvidence context (environment available) node.requirements node.coercions instantiation.predicates semantic →
        semantic = environment actual :=
  ⟨CallableCallRequirementLayouts.direct_produces signatures ledger assumptions resolved accepted authenticated,
    fun _ produced => CallableCallRequirementLayouts.direct_agrees ledger
      (CallableCallRequirementLayouts.singletons_of_unique ledger unique) accepted produced⟩

theorem actual_reference_dictionary {program : CheckedProgram} {caller : SourceSpecialization.SpecializedFunction}
    {node : ExpressionNode} {instantiation : DeclarationInstantiation}
    {available actual : SourceTypedRuntime.RuntimeEvidenceEnvironment} {context : SourceSemantics.Context}
    {callee : SourceCompilationPlan.Key}
    (signatures : context.signatures = program.signatures)
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (assumptions : ∀ goal, goal ∈ caller.assumptions → goal ∈ context.assumptions)
    (resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions = .ok available)
    (accepted : SourceCompilationPlan.exactDeclarationReferenceRuntimeEvidence caller node available instantiation = .ok actual)
    (authenticated : SourceCompilationPlan.validateAuthenticatedRuntimeEvidence program.signatures callee instantiation.predicates actual = .ok ()) :
    (∃ ids, Dynamic.OrdinaryRequirementLayout node.requirements node.coercions ids ∧
      Dynamic.RequirementsProduceEnvironment context (environment available) ids instantiation.predicates (environment actual)) ∧
    ∀ ids semantic, Dynamic.OrdinaryRequirementLayout node.requirements node.coercions ids →
      Dynamic.RequirementsProduceEnvironment context (environment available) ids instantiation.predicates semantic → semantic = environment actual :=
  ⟨CallableCallRequirementLayouts.reference_produces signatures ledger assumptions resolved accepted authenticated,
    fun _ _ layout produced => CallableCallRequirementLayouts.reference_agrees ledger accepted layout produced⟩

private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def goal : ProgramPredicate := ProgramSignatures.builtinIntWordRule.head
private def otherGoal : ProgramPredicate := ProgramSignatures.builtinIntIntegerRule.head
private def raw : TypedTraitResolution.Evidence := .byImpl goal (.builtin .intWord) []
private def validRow : SolvedRequirement := ⟨⟨0⟩, goal, .implementation raw⟩
private def invalidRow : SolvedRequirement := ⟨⟨99⟩, goal, .assumption otherGoal⟩
private def rows := [validRow, invalidRow, invalidRow]
private def context : SourceSemantics.Context := {signatures, locals := [], assumptions := [], solvedRequirements := rows}
private def callerWith (seed : SourceSpecialization.SpecializedFunction) :=
  {seed with assumptions := [], function := {seed.function with solvedRequirements := rows}}

/-- Successful real receipts prove the reached row even though the unused
ledger includes duplicated, internally misaligned assumption templates. -/
theorem reached_only (program : CheckedProgram) (seed : SourceSpecialization.SpecializedFunction) (occurrence : ExpressionId) :
    Dynamic.RequirementsProduceEnvironment context [] [⟨0⟩] [goal] (environment [raw]) ∧
      ¬ SolvedRequirementsValid context rows := by
  have produced := CallableAuthenticatedCallEvidence.produces (program := {program with signatures := signatures})
    (caller := callerWith seed) (callee := seed.key) (context := context)
    (occurrence := occurrence) (available := []) (result := [raw])
    (ids := [⟨0⟩]) (predicates := [goal]) rfl rfl (by simp [callerWith]) rfl rfl rfl
  refine ⟨produced, ?_⟩
  intro allValid
  have impossible := (allValid invalidRow (by simp [rows])).evidence_goal_eq
  cases impossible

/-- Repeated requested IDs and repeated goals keep both output positions;
caller first-match lookup does not erase the ordered result multiplicity. -/
theorem repeated_authenticated (program : CheckedProgram) (seed : SourceSpecialization.SpecializedFunction)
    (occurrence : ExpressionId) :
    let assumed : SolvedRequirement := ⟨⟨0⟩, goal, .assumption goal⟩
    let caller := {seed with assumptions := [goal, goal], function := {seed.function with solvedRequirements := [assumed, invalidRow]}}
    let context : SourceSemantics.Context := {signatures, locals := [], assumptions := [goal], solvedRequirements := [assumed, invalidRow]}
    SourceCompilationPlan.materializeCallEvidence caller occurrence [raw, raw] [⟨0⟩, ⟨0⟩] [goal, goal] = .ok [raw, raw] ∧
    Dynamic.RequirementsProduceEnvironment context (environment [raw, raw]) [⟨0⟩, ⟨0⟩] [goal, goal] (environment [raw, raw]) := by
  dsimp only
  refine ⟨rfl, ?_⟩
  exact CallableAuthenticatedCallEvidence.produces (program := {program with signatures := signatures})
    (caller := {seed with assumptions := [goal, goal], function := {seed.function with solvedRequirements := [⟨⟨0⟩, goal, .assumption goal⟩, invalidRow]}})
    (callee := seed.key) (occurrence := occurrence) rfl rfl (by simp) rfl rfl rfl

/-- Goal alignment alone cannot authenticate a different implementation tree. -/
theorem same_goal_different_selection_rejected (key : SourceCompilationPlan.Key) :
    SourceCompilationPlan.validateAuthenticatedRuntimeEvidence signatures key [goal]
      [.byImpl goal (.builtin .intInteger) []] =
      .error (.runtimeEvidenceNotSelected key 0 goal (.builtin .intInteger)) := rfl

private def step (id : Nat) : CoercionStep := {requirement := ⟨id⟩, source := .word, target := .word}
private def middleNode (seed : ExpressionNode) := {seed with requirements := [⟨10⟩, ⟨0⟩, ⟨11⟩], coercions := [step 10, step 11]}

/-- Both sides of the owned middle are retained. The compiler only materializes
ID 0, so the two coercion IDs need no callee dictionary rows. -/
theorem actual_middle (program : CheckedProgram) (seed : SourceSpecialization.SpecializedFunction)
    (node : ExpressionNode) (instantiation : DeclarationInstantiation) :
    SourceCompilationPlan.exactDirectCallRuntimeEvidence (callerWith seed) (middleNode node) []
      {instantiation with predicates := [goal]} = .ok [raw] ∧
    Dynamic.DirectCallProducesEvidence context [] (middleNode node).requirements (middleNode node).coercions [goal] (environment [raw]) := by
  have accepted : SourceCompilationPlan.exactDirectCallRuntimeEvidence (callerWith seed) (middleNode node) []
      {instantiation with predicates := [goal]} = .ok [raw] := rfl
  exact ⟨accepted, CallableCallRequirementLayouts.direct_produces (program := {program with signatures := signatures})
    (callee := seed.key) rfl rfl (by simp [callerWith]) rfl accepted rfl⟩

theorem reference_repeated_coercions (node : ExpressionNode) :
    Dynamic.OrdinaryRequirementLayout [⟨0⟩, ⟨10⟩, ⟨10⟩] [step 10, step 10] [⟨0⟩] :=
  CallableCallRequirementLayouts.ordinary_owned (node := {node with requirements := [⟨0⟩, ⟨10⟩, ⟨10⟩], coercions := [step 10, step 10]}) rfl

/-- The authenticated entrance applies to the actual local rewrite, retaining
its exact source ledger and the original caller assumptions. It does not
require template rows outside the selected call to acquire validity. -/
theorem local_rebinding_dictionary {program : CheckedProgram} {caller : SourceSpecialization.SpecializedFunction}
    {substitution : TypeSystem.Substitution} {witnesses : List SourceCoreLocalEvidence.Witness}
    {occurrence : ExpressionId} {available result : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    {ids : List RequirementId} {predicates : List ProgramPredicate} {context : SourceSemantics.Context} {callee : SourceCompilationPlan.Key}
    (signatures : context.signatures = program.signatures)
    (ledger : context.solvedRequirements = SourceCoreLocalEvidence.rewriteLedger substitution witnesses caller.function.solvedRequirements)
    (assumptions : ∀ goal, goal ∈ caller.assumptions → goal ∈ context.assumptions)
    (resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions = .ok available)
    (accepted : SourceCompilationPlan.materializeCallEvidence (SourceCoreLocalEvidence.contextualCaller caller substitution witnesses)
      occurrence available ids predicates = .ok result)
    (authenticated : SourceCompilationPlan.validateAuthenticatedRuntimeEvidence program.signatures callee predicates result = .ok ()) :
    Dynamic.RequirementsProduceEnvironment context (environment available) ids predicates (environment result) :=
  CallableAuthenticatedCallEvidence.produces (caller := SourceCoreLocalEvidence.contextualCaller caller substitution witnesses)
    signatures ledger assumptions resolved accepted authenticated

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Mark<T> {}", "impl Mark<Word> {}", "impl Mark<Bool> {}",
    "trait Coerce<From, To> { function coerce(value: From) returns (To); }",
    "impl Coerce<Bool, Word> { function coerce(value: Bool) returns (Word) { let table: mapping(Word => Word); table[0] = value ? 40 : 6; table[0] += 2; return table[0]; } }",
    "function keep<T>(value: T) returns (T) where T: Mark { return value; }",
    "function forward<T>(value: T) returns (T) where T: Mark { return keep(value); }",
    "function converted(flag: Bool) returns (Word) { return forward(flag); }",
    "function local(flag: Bool) returns (Word, Bool) { let f = lam(item) { return keep(item); }; return (f(7), f(flag)); }",
    "function failed(flag: Bool) returns (Word) { let table: mapping(Word => Word); table[0] = forward(flag); let absent: Word; return absent; }"
  ]}] }

private def audit (entry : SourceCompilerFeatureSupport.Entry) : IO Unit := do
  let prepared := entry.cached.indexed
  let mut qualified := 0
  let mut coerced := 0
  for named in prepared.base.functions do
    let available ← SourceCompilerFeatureSupport.get "caller evidence"
      (SourceCompilationPlan.resolveRuntimeEvidenceEnvironment prepared.base.sourceProgram named.signature.key named.specialized.assumptions)
    for item in named.specialized.function.typedBody.nodes do
      match item with
      | .expression node =>
        match node.form with
        | .call _ _ (.declaration instantiation) =>
          if !instantiation.predicates.isEmpty && instantiation.predicates.all (fun predicate => (TypedTraitResolution.predicateVariables predicate).isEmpty) then
            let actual ← SourceCompilerFeatureSupport.get "direct ordered evidence"
              (SourceCompilationPlan.exactDirectCallRuntimeEvidence named.specialized node available instantiation)
            discard <| SourceCompilerFeatureSupport.get "authenticate ordered evidence"
              (SourceCompilationPlan.validateAuthenticatedRuntimeEvidence prepared.base.sourceProgram.signatures named.signature.key instantiation.predicates actual)
            qualified := qualified + 1
            if !node.coercions.isEmpty then coerced := coerced + 1
        | _ => pure ()
      | _ => pure ()
  SourceCompilerFeatureSupport.require (qualified > 0 && coerced > 0) "qualified coercion-call receipt coverage disappeared"

def run : IO Unit := do
  let program ← SourceCompilerFeatureSupport.get "authenticated call checker" (checkProgram workspace)
  let converted ← SourceCompilerFeatureSupport.compileNamed program "converted"
  audit converted
  for (flag, expected) in [(true, 42), (false, 8)] do
    converted.checkResume [.bool flag] (SourceCompilerFeatureSupport.scalar expected) 9
  let localEntry ← SourceCompilerFeatureSupport.compileNamed program "local"
  localEntry.checkResume [.bool true] (.product (SourceCompilerFeatureSupport.scalar 7) (.bool true)) 17
  let failed ← SourceCompilerFeatureSupport.compileNamed program "failed"
  let baseline ← failed.invoke [.bool true]
  let (reason, session) ← match baseline.outcome with
    | .failed reason session => pure (reason, session)
    | _ => throw (IO.userError "coercion effects did not reach expected later failure")
  let snapshot ← SourceCompilerFeatureSupport.get "evidence failure snapshot" (← session.snapshot 2048)
  for spent in [0, 13, 67] do
    let started ← SourceCompilerFeatureSupport.get "evidence failure suspend"
      (← baseline.initial.run baseline.key [.bool true] {SourceCompilerFeatureSupport.executionOptions with executionFuel := spent})
    let resumed ← match started with
      | .outOfFuel checkpoint => checkpoint.resume 300000 2048
      | done => pure done
    match resumed with
    | .failed actual session =>
      let observed ← SourceCompilerFeatureSupport.get "evidence failure resume snapshot" (← session.snapshot 2048)
      SourceCompilerFeatureSupport.require (actual == reason && reprStr observed.cells == reprStr snapshot.cells)
        "coercion dictionary call changed effects, failure or resume"
    | _ => throw (IO.userError "evidence resume changed outcome")
  IO.println "authenticated call evidence: reached validity, exact middle layout, local rebinding, coercion effects and resume GREEN"

end Tests.SourceCoreCallableAuthenticatedCallEvidence
