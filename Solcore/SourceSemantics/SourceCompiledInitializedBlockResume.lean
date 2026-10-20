import Solcore.SourceSemantics.SourceCompiledStatementPrivacyResume

/-! A real initialized statement protects its newly generalized variables
through the rest of a lambda or ordinary function block. The entry state,
generalization, expected-type safety and suffix all come from actual calls. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledGeneralizedSoundness ProtectedVariables

structure InitializedBlockResume
    {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction}
    {fuel : Nat} (selected : Selected compiled row fuel)
    (inferenceContext : SourceInference.Context) (expectedReturn : Ty)
    (initial : State) (result : Detail.BlockResult) (source : Syntax.Statement) where
  actual : InitializerOccurrence selected source
  context : actual.inferenceContext = inferenceContext
  before : initial.InferenceProgress actual.entry
  continuation : actual.result.state.InferenceProgress result.state
  ready : result.state.InferenceReady
  wellFormed : result.state.RequirementsWellFormed
  bound : ∀ q ∈ actual.receipt.binding.1.scheme.quantified, q.index < result.state.inference.next
  transport : SafeTransport actual.receipt.binding.1.scheme.quantified actual.receipt.ready result.state
  resultSafe : Safe actual.receipt.binding.1.scheme.quantified result.state result.type
  expectedSafe : Safe actual.receipt.binding.1.scheme.quantified result.state expectedReturn
  live : LiveBindersSafe actual.receipt.binding.1.scheme.quantified result.state
  olderAtReady : ∀ type, type.VariablesBelow initial.inference.next →
    Safe actual.receipt.binding.1.scheme.quantified actual.receipt.ready type
  olderSafe : ∀ type, type.VariablesBelow initial.inference.next →
    Safe actual.receipt.binding.1.scheme.quantified result.state type
  newRows : ∀ requirement ∈ result.state.requirements,
    requirement ∉ actual.receipt.ready.requirements →
      PredicateSafe actual.receipt.binding.1.scheme.quantified result.state requirement.predicate

theorem initialized_block_resume
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : Selected compiled row fuel}
    {inferenceContext : SourceInference.Context} {sources : List Syntax.Statement}
    {expectedReturn : Ty} {initial : State} {result : Detail.BlockResult}
    {index : Nat} {statement : Syntax.Statement}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (scope : CheckingScope selected.toBodySelection inferenceContext)
    (ready : initial.InferenceReady) (nodesBelow : initial.NodesBelowNextOccurrence)
    (entering : ResumeEntryInvariant selected expectedReturn initial)
    (returnBelow : expectedReturn.VariablesBelow initial.inference.next)
    (retained : result.state.nodes <+: selected.body.returned.nodes)
    (extension : selected.body.finalized.substitution.SemanticallyExtends result.state.inference.substitution)
    (accepted : Detail.inferStatementsFuel childFuel inferenceContext sources expectedReturn initial = .ok result)
    (position : sources[index]? = some statement)
    {name : Syntax.Identifier} {annotation : Option Syntax.TypeExpr} {initializer : Syntax.Expr}
    (form : statement.value = .letDecl name annotation (some initializer)) :
    Nonempty (InitializedBlockResume selected inferenceContext expectedReturn initial result statement) := by
  obtain ⟨resume⟩ := selected_statement_privacy_resume checked scope ready nodesBelow entering
    returnBelow retained extension accepted position
  have formation := scope.formation checked
  have canonical := scope.functionsCanonical checked
  obtain ⟨initializerFuel,receipt,_,_⟩ := resume.toOccurrence.initialized form formation canonical
  have resultExtension := extension.trans resume.continuation.substitution_extends
  have recorded := (resume.retained.trans retained).subset receipt.recorded
  let occurrence := InitializerOccurrence.ofReceipt checked scope receipt resume.ready
    resume.entryInvariant.1 recorded resultExtension
  have afterOwner := (Detail.inferStatementFuel_preserves_owner resume.accepted).trans resume.entryInvariant.2.2
  have afterSource : TypingSourceExtends (resume.result.state.toTypedSource (bodyRoots selected.toBodySelection))
      (evidenceSource selected.toBodySelection) :=
    ⟨afterOwner.symm, resume.retained.trans retained⟩
  have afterOperational := resume.entryInvariant.1.ofInitializer receipt selected.body.resources resume.ready
    (scope.catalog checked) formation canonical (resume.retained.trans retained) afterSource resultExtension
  have binderMember : receipt.binding.1 ∈ resume.result.state.localBinders := by
    rw [receipt.result_binders]
    exact List.mem_cons_self
  have live := afterOperational.privacy _ binderMember
  have bound := afterOperational.quantifiersBelow _ binderMember
  have older : ∀ type, type.VariablesBelow resume.entry.inference.next →
      Safe receipt.binding.1.scheme.quantified resume.result.state type := by
    intro type below
    have safe := occurrence.generalized_type_safe checked scope resume.ready resume.entryInvariant.1 below
    simpa only [occurrence, InitializerOccurrence.ofReceipt, Safe, State.resolve,
      InferState.resolve, receipt.inference_eq] using safe
  have expectedSafe := older expectedReturn (returnBelow.weaken resume.before.next_le)
  have resultSafe : Safe receipt.binding.1.scheme.quantified resume.result.state resume.result.type := by
    have resultType : resume.result.type = .unit :=
      congrArg Detail.StatementResult.type receipt.completed
    rw [resultType]
    exact safe_closed _ _ (by simp [Ty.VariablesBelow, Ty.freeVariables, Ty.unit])
  have suffix := resume.resume receipt.binding.1.scheme.quantified bound live expectedSafe resultSafe older
  have properties := Detail.inferStatementsFuel_inferenceProperties ready formation canonical returnBelow accepted
  refine ⟨{
    actual := occurrence, context := rfl, before := resume.before, continuation := resume.continuation,
    ready := properties.2.1,
    wellFormed := (Detail.inferStatementsFuel_direct_progress accepted).wellFormed entering.1.requirements,
    bound := fun q present => Nat.lt_of_lt_of_le (bound q present) resume.continuation.next_le,
    transport := (SafeTransport.of_substitution_eq (congrArg InferState.substitution receipt.inference_eq)).trans suffix.1,
    resultSafe := suffix.2.1, expectedSafe := suffix.1 _ expectedSafe,
    live := suffix.2.2.1,
    olderAtReady := fun type below => occurrence.generalized_type_safe checked scope resume.ready
      resume.entryInvariant.1 (below.weaken resume.before.next_le),
    olderSafe := fun type below => suffix.1 type (older type (below.weaken resume.before.next_le)),
    newRows := ?_ }⟩
  intro requirement present fresh
  apply suffix.2.2.2 requirement present
  have same : resume.result.state.requirements = receipt.ready.requirements :=
    congrArg (fun result : Detail.StatementResult => result.state.requirements) receipt.completed
  simpa only [same, occurrence, InitializerOccurrence.ofReceipt] using fresh

end Solcore.SourceSemantics.SourceCompiledLocalFinalization
