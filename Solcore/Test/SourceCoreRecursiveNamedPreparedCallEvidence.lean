import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedCallEvidence
import Solcore.Test.SourceCoreUnifiedCorpusSupport

/-! Actual authenticated direct selection reaches nonempty prepared callee
dictionaries. Formal consumers keep independent source typing and the whole
ledger. Runtime inspection compares the actual public compiler's selected
record, raw evidence, ordered arguments and physical cache row. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedPreparedCallEvidence
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open RecursiveNamedPublicSpecializationMeaning CallableCoercionExpressionCertificates
open RecursiveNamedPreparedCallEvidence

abbrev actual_call := @RecursiveNamedPreparedCallEvidence.from_accepted
abbrev actual_retained_frame := @RecursiveNamedPreparedCallEvidence.callee_frame

section Actual
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {caller : Specialized}
  {project : Projector} {compilation : SourceCoreFunctions.Context} {child : SourceCoreEvidence.Child}
  {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {id callee : ExpressionId} {arguments : List ExpressionId}
  {instantiation : DeclarationInstantiation} {reasonAt : ExpressionId → Word}
  {policy : SourceCoreFunctions.CallablePolicy} {node : ExpressionNode} {output : Lowered}
  (receipt : Direct compiled.sourceProgram project caller compilation child fuel caller.function.typedBody scope
    id callee arguments instantiation reasonAt policy node output)
  (callerPrepared : Prepared compiled caller)
  (calleePrepared : Prepared compiled receipt.selection.specialized)

theorem actual_frame {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (SourceSemantics.Context.ofSignatures compiled.sourceProgram.signatures) caller.parameterSubstitution)
    (extended : MonoBindersExtend callerPrepared.view.source.owner callerPrepared.view.context
      callerPrepared.view.parameters types context) :
    Dynamic.DirectCallProducesEvidence context callerPrepared.view.evidence node.requirements node.coercions
      instantiation.predicates calleePrepared.view.evidence ∧
    ∀ semantic, Dynamic.DirectCallProducesEvidence context callerPrepared.view.evidence node.requirements node.coercions
      instantiation.predicates semantic → semantic = calleePrepared.view.evidence :=
  at_frame receipt callerPrepared calleePrepared wellFormed range extended

theorem actual_cache (globals : compilation.globals = compiled.indexed.base.globals) :
    receipt.native.signature = calleePrepared.named.signature ∧ receipt.native.index = calleePrepared.index ∧
      compiled.indexed.secondPass.closures[receipt.native.index]? = some calleePrepared.code := by
  obtain ⟨signature, slot⟩ := native_target receipt calleePrepared globals
  exact ⟨signature, slot, by simpa only [slot] using calleePrepared.cached⟩

theorem full_dictionaries :
    receipt.selection.available = callerPrepared.available ∧ receipt.selection.actual = calleePrepared.available :=
  ⟨caller_dictionary receipt callerPrepared, callee_dictionary receipt calleePrepared⟩

theorem retained_full_metadata
    (order : instantiation.parameterSubstitution.map Prod.fst =
      (receipt.selection.specialized.parameterSubstitution.map Prod.fst).reverse) :
    instantiation = CallableNamedCanonicalOrder.retainedInstantiation receipt.selection.specialized :=
  retained_metadata receipt order

theorem unused_rows_kept {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
    (extended : MonoBindersExtend callerPrepared.view.source.owner callerPrepared.view.context
      callerPrepared.view.parameters types context) :
    context.solvedRequirements = caller.function.solvedRequirements :=
  (RecursiveNamedPreparedCallEvidence.Prepared.context_fields callerPrepared extended).2.1
end Actual

section Boundaries

theorem same_goals_do_not_identify_trees (goal : ProgramPredicate) (first second : ProgramImplId)
    (different : first ≠ second) :
    (TraitEvidence.implementation goal first []).goal =
      (TraitEvidence.implementation goal second []).goal ∧
    TraitEvidence.implementation goal first [] ≠ .implementation goal second [] := by
  refine ⟨rfl, ?_⟩
  intro same
  exact different (TraitEvidence.implementation.inj same).2.1

theorem dictionary_keeps_order (first second : TypedTraitResolution.Evidence) :
    CallableNamedMetadata.environment [first, second, first] =
      [(SourceTypedRuntime.runtimeEvidenceGoal first, CallableNamedMetadata.evidence first),
       (SourceTypedRuntime.runtimeEvidenceGoal second, CallableNamedMetadata.evidence second),
       (SourceTypedRuntime.runtimeEvidenceGoal first, CallableNamedMetadata.evidence first)] := rfl

theorem duplicate_requirements_not_unique (context : SourceSemantics.Context) (row : SolvedRequirement) :
    ¬ RequirementIdsUnique {context with solvedRequirements := [row, row]} := by
  simp [RequirementIdsUnique]

end Boundaries

private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def word (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def content := String.intercalate "\n" [
  "trait Mark<T> {}", "trait Stamp<T> {}", "impl Mark<Word> {}", "impl Stamp<Word> {}",
  "function keep<A, B>(value: A, unused: B) returns (A) where A: Mark, A: Stamp, A: Mark { return value; }",
  "function relay<A, B>(value: A, unused: B) returns (A) where A: Stamp, A: Mark { let retained: Word = 3; return keep(value, unused); }",
  "function missing<T>(value: T) returns (T) where T: Mark { let absent: T; return absent; }",
  "function closed() returns (Word) { return relay(7, true); }",
  "function constrained(value: Word) returns (Word) where Word: Mark, Word: Stamp { return relay(value, false); }",
  "function fault() returns (Word) { return missing(9); }"
]

private def inspect (compiled : SourceCoreUnifiedCompilation.Compiled) : IO Unit := do
  let indexed := compiled.indexed
  let base := indexed.base
  let diagnostics ← match base.diagnostics with
    | some value => pure value.program | none => throw (IO.userError "prepared call diagnostics absent")
  let diagnostics := match base.callableContext with
    | some native => {diagnostics with rootTable := native.diagnostics.rootTable} | none => diagnostics
  let parents ← get "actual parent preparation" (SourceCoreStageCodebook.prepareContexts base.sourceProgram base.plan
    (base.locals.bindings.flatMap (·.instances)))
  let mut calls := 0
  let mut qualified := 0
  let mut repeated := 0
  let mut unusedRows := 0
  for named in base.functions do
    let caller := named.specialized
    let source := caller.function.typedBody
    let ledger := caller.function.solvedRequirements
    let representation := (CallableIndexedNamedGeneration.representation indexed).atContext named.signature.key []
    let compilation := CallableIndexedNamedGeneration.context indexed named
    let scope := named.inputs.reverse.map (fun binding => (binding.1.id, binding.2))
    let own ← match diagnostics.base.find? named.signature.key with
      | some own => pure own | none => throw (IO.userError "prepared caller diagnostics absent")
    let reasonAt := diagnostics.reasonAt named.signature.key
    let lower := SourceCoreGeneralFunctions.lowerContextualExpression base.sourceProgram representation base.sourceProgram.signatures
      base.locals parents own.assignments diagnostics compilation base.callableContext none none
    let callables := SourceCoreGeneralFunctions.callablePolicy base.callableContext []
    let available ← get "full prepared caller dictionary" (SourceCompilationPlan.resolveRuntimeEvidenceEnvironment base.sourceProgram caller.key caller.assumptions)
    for item in source.nodes do
      if let .expression node := item then
        if let .call callee args (.declaration instantiation) := node.form then
          let actual ← get "actual contextual direct call" (lower indexed.fuel source scope node.id reasonAt)
          let special ← get "actual authenticated some branch" (SourceCoreEvidence.lowerWithProjector base.sourceProgram
            representation.expressions.projectType caller compilation lower (indexed.fuel - 1) source scope node.id reasonAt callables)
          require (special == some actual) "authenticated branch is not actual emitted code"
          discard <| get "full actual callee metadata" (SourceCompilationPlan.validateDirectDeclarationCallee source node.id callee instantiation)
          let target ← get "actual full instantiation target" (SourceCompilationPlan.exactInstantiationKey base.plan instantiation)
          let key ← get "actual call edge" (SourceCompilationPlan.exactCallKey base.plan compilation.owner node.id target)
          let selected ← get "actual full selected specialization" (SourceCompilationPlan.exactSpecialization base.plan key)
          let produced ← get "actual complete materialization" (SourceCompilationPlan.exactDirectCallRuntimeEvidence caller node available instantiation)
          discard <| get "full actual authentication" (SourceCompilationPlan.validateAuthenticatedRuntimeEvidence base.sourceProgram.signatures key selected.assumptions produced)
          let canonical ← get "same prepared callee resolver" (SourceCompilationPlan.resolveRuntimeEvidenceEnvironment base.sourceProgram selected.key selected.assumptions)
          require (reprStr produced == reprStr canonical && !produced.isEmpty && selected.key == key)
            "actual dictionary differs from full prepared callee evidence"
          let (signature, slot) ← match base.globals.zipIdx.filter (fun row => decide (row.1.key = key)) with
            | [row] => pure row | _ => throw (IO.userError "actual global selection is not singleton")
          let calleeNamed ← match base.functions[slot]? with
            | some value => pure value | none => throw (IO.userError "actual physical callee row absent")
          require (calleeNamed.specialized == selected && calleeNamed.signature == signature &&
            reprStr instantiation == reprStr (CallableNamedCanonicalOrder.retainedInstantiation selected))
            "full callee/retained metadata/physical signature changed"
          let cached ← match indexed.secondPass.closures[slot]? with
            | some value => pure value | none => throw (IO.userError "actual cached callee absent")
          require (match cached with | .lambda .. => true | _ => false) "actual callee cache is not a closure"
          let children ← get "actual ordered arguments" (args.mapM (fun id => lower (indexed.fuel - 1) source scope id reasonAt))
          let packed := SourceCoreCalls.packArguments children
          require (node.coercions.isEmpty && actual == ⟨signature.resultType,
            SourceCoreCalls.call signature (scope.length + compilation.administrativePrefix + slot) packed.expression compilation.internalReason⟩)
            "actual direct call changed ordered arguments/code/slot"
          require (children.map (·.type) == calleeNamed.inputs.map Prod.snd && packed.type == signature.parameterType)
            "actual native argument vector changed"
          let nativeContext := SourceCoreLocalCell.coreContext scope ++ named.signature.parameterType ::
            base.globals.map (·.referenceType) ++ [.cell indexed.ancestry.layout.frame.type]
          require (Core.infer? nativeContext actual.expression indexed.layouts.definitions == some (LanguageResult.resultType actual.type))
            "actual call failed native checking"
          calls := calls + 1
          if !caller.assumptions.isEmpty then qualified := qualified + 1
          if produced.length == 3 then
            repeated := repeated + 1
            require (produced[0]? == produced[2]? && produced[0]? != produced[1]?) "repeated predicate dictionary lost original order"
            require (SourceCompilationPlan.validateAuthenticatedRuntimeEvidence base.sourceProgram.signatures key selected.assumptions produced.reverse).toOption.isSome
              "symmetric duplicate order should authenticate identically"
            let reordered ← match produced with
              | [first, second, third] => pure [second, first, third]
              | _ => throw (IO.userError "expected ordered triple")
            require (SourceCompilationPlan.validateAuthenticatedRuntimeEvidence base.sourceProgram.signatures key selected.assumptions reordered).toOption.isNone
              "same multiset authenticated in a different order"
          let unused := ledger.filter (fun row => !(node.requirements.contains row.id))
          unusedRows := unusedRows + unused.length
          require (reprStr ledger == reprStr caller.function.solvedRequirements) "unused rows removed"
          if !unused.isEmpty then
            let augmented := {caller with function := {caller.function with solvedRequirements := unused ++ ledger ++ unused}}
            let again ← get "unused full ledger additions" (SourceCompilationPlan.exactDirectCallRuntimeEvidence augmented node available instantiation)
            require (reprStr again == reprStr produced) "unreached rows changed actual reached selection"
  require (calls ≥ 4 && qualified ≥ 2 && repeated ≥ 1 && unusedRows > 0)
    s!"nonempty prepared call coverage {calls}/{qualified}/{repeated}/{unusedRows}"

private def full_result (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (arguments : List SourceTypedRuntime.Value) (fuel : Nat) : IO (SourceTypedRuntime.RunResult × String) := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel
  let final ← get "actual prepared call resume" (first.resume 300000)
  let execution ← match final.execution with
    | some execution => pure execution | none => throw (IO.userError "original native result absent")
  match execution.completion.result.native.observation with
  | .succeeded _ _ | .failed _ _ => pure ()
  | _ => throw (IO.userError "original native run unfinished")
  pure (final.observation, reprStr execution.completion.result.native.observation)

def run : IO Unit := do
  let names := ["closed", "constrained", "fault"]
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "nonempty prepared calls" content names
  inspect compiled
  for (name, arguments, expected) in [("closed", [], some (word 7)), ("constrained", [word 17], some (word 17)), ("fault", [], none)] do
    let baseline ← full_result compiled name arguments 300000
    for fuel in [0, 1, 43, 300000] do
      let actual ← full_result compiled name arguments fuel
      require (reprStr actual == reprStr baseline) "same full source/native heap changed on resume"
      match expected, actual.1 with
      | some value, .done result state =>
        require (reprStr result == reprStr value) "prepared nonempty dictionary result changed"
        require (state.heap.any (fun cell => reprStr cell.value == reprStr (some (word 3)))) "unused initializer cell lost"
      | none, .fault (.uninitializedLocal _) state =>
        require (state.heap.any (fun cell => cell.value.isNone)) "fault heap lost uninitialized cell"
      | _, _ => throw (IO.userError "prepared nonempty call outcome changed")
  IO.println "prepared call evidence: actual some branch/nonempty full dictionaries/repeated goals/retained order/unused rows/physical cache/ordered args/full native+source heaps/resume GREEN"
end Tests.SourceCoreRecursiveNamedPreparedCallEvidence
