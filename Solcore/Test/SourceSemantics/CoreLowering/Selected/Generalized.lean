import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosedInitialForward
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosedDirectForward
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosedOutputForward
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCheckedPublicSession
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCompilerStaticProfile
import Solcore.Test.SourceCoreCoercionPublicFixture
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationClosedCoercionSourceSelection
import Solcore.SourceSemantics.CoreLowering.CallableCoercionRawNamedCallAdmission
import Solcore.Test.SourceSemantics.CoreLowering.Selected.GeneralizedSource
import Solcore.Test.Frontend.Source.CompilerFeatureSupport
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedStageContracts
import Solcore.SourceSemantics.CoreLowering.CallableNamedMetadata
import Solcore.SourceSemantics.CoreLowering.CellAwareNamedProgramProfiles
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCatalog
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicRootMeaning
import Solcore.Test.SourceSemantics.Semantics
import Solcore.SourceSemantics.Dynamic.Preservation
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedSourceTyping
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionState
import Solcore.SourceSemantics.CoreLowering.CellAwarePublicInitialStart
import Solcore.SourceSemantics.CoreLowering.CellAwarePublicNamedForward
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCertifiedPublicSessionInitial
import Solcore.SourceSemantics.CoreLowering.CellAwarePublicNextStart
import Solcore.SourceSemantics.CoreLowering.CellAwareSelectedPublicSessionState
import Solcore.SourceSemantics.CoreLowering.CellAwarePublicNamedContinuation
import Solcore.SourceSemantics.CoreLowering.CellAwarePublicNamedObservedOutput
import Solcore.Test.SourceCoreSelectedLexicalFailureMeaning
import Solcore.Test.SourceCoreDirectIssuedSequence
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionIssuance
import Solcore.Test.SourceCoreSelectedLexicalSourceStart
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicSourceCallOutcomes
import Solcore.Test.SourceCoreUnifiedCorpusSupport

/-!
# Generalized selected tests

Generalized locals, coerced and captured direct calls, named builtins and ordinary stage lifts.
-/

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedCapturedDirectSource
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreSelectedCapturedDirect
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedFunctionValues (Header NamedSourceAt)

structure Shape (source : TypedSource) where
  binder : TypedBinder
  read : ExpressionNode
  inner : StatementNode
  lambda : ExpressionNode
  outer : StatementNode
  inputs : source.inputs = [binder]
  binderType : binder.scheme = .mono .word
  binderCopied : CaptureBinders.copiedBinder? source binder.id = some binder
  roots : source.roots = [.statement outer.id]
  readFound : source.lookupExpression? read.id = some read
  readForm : read.form = .reference binder.name (.local binder.id)
  readRequirements : read.requirements = []
  readCoercions : read.coercions = []
  innerFound : source.lookupStatement? inner.id = some inner
  innerForm : inner.form = .returnStmt (some read.id)
  lambdaFound : source.lookupExpression? lambda.id = some lambda
  lambdaForm : lambda.form = .lambda [] .word [inner.id]
  lambdaRequirements : lambda.requirements = []
  lambdaCoercions : lambda.coercions = []
  outerFound : source.lookupStatement? outer.id = some outer
  outerForm : outer.form = .returnStmt (some lambda.id)

def capturedCell (word : Word) : Dynamic.Cell := {type := .word, value := some (.word word)}

/-- The factory's parameter cell. -/
def parameterHeap (word : Word) : Dynamic.Heap := ⟨[capturedCell word]⟩

/-- The parameter cell and the closure's snapshot of it. -/
def capturedHeap (word : Word) : Dynamic.Heap := ⟨[capturedCell word, capturedCell word]⟩

/-- A call appends its own copy of the snapshot. -/
def calledHeap (word : Word) : Dynamic.Heap :=
  ⟨[capturedCell word, capturedCell word, capturedCell word]⟩

def capturedFunction {compiled : SourceCoreUnifiedCompilation.Compiled}
    (header : Header compiled (Program.ofChecked compiled.sourceProgram))
    (shape : Shape header.function.source) : Dynamic.Closure := {
  parameters := [], resultType := .word, body := [shape.inner.id]
  source := header.function.source, captured := [(shape.binder.id, ⟨1⟩)]
  context := header.context, evidence := header.function.evidence }

private theorem roots_injective {left right : List StatementId}
    (same : left.map NodeId.statement = right.map NodeId.statement) : left = right := by
  induction left generalizing right with
  | nil => cases right <;> simp at same ⊢
  | cons head rest ih =>
    cases right with
    | nil => simp at same
    | cons other tail =>
      simp only [List.map_cons, List.cons.injEq] at same
      cases same.1
      exact congrArg (List.cons head) (ih same.2)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (header : Header compiled (Program.ofChecked compiled.sourceProgram))
  (shape : Shape header.function.source)

include shape in
theorem input_types : header.types = [.word] := by
  have params : header.function.parameters = [shape.binder] :=
    header.parameters.trans (header.inputs.symm.trans shape.inputs)
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq header.extended
  simpa only [params, List.map_cons, List.map_nil, shape.binderType, TypeSystem.Scheme.mono] using types.symm

/-- Build the factory execution directly from its original allocation and
lambda, which copies the parameter cell into the closure's snapshot. -/
theorem factory_plain {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {global : Dynamic.GlobalFunction}
    (sourceAt : NamedSourceAt header rawD global) (invocation : Staging.Recursive.Scope) (word : Word) :
    RecursiveNamedPublicPhysicalSessionState.PlainValue header header invocation ⟨[]⟩ [.word word]
      (.closure (capturedFunction header shape)) (capturedHeap word) := by
  have params : header.function.parameters = [shape.binder] :=
    header.parameters.trans (header.inputs.symm.trans shape.inputs)
  have allocated : Dynamic.Heap.Allocates ⟨[]⟩ shape.binder.scheme.body
      (some (.word word)) ⟨0⟩ (parameterHeap word) := by
    rw [shape.binderType]
    exact .append
  have bound : Dynamic.BindersAllocate [] ⟨[]⟩ header.function.parameters [.word word]
      [(shape.binder.id, ⟨0⟩)] (parameterHeap word) := by
    rw [params]
    exact .cons allocated (.nil _ _)
  have stored : Dynamic.Heap.Allocates ⟨[]⟩ .word (some (.word word)) ⟨0⟩ (parameterHeap word) := .append
  have snapshot : Dynamic.EnvironmentCopies header.function.source [(shape.binder.id, ⟨0⟩)]
      (parameterHeap word) [(shape.binder.id, ⟨1⟩)] (capturedHeap word) :=
    .copied shape.binderCopied stored.reads_new .append (.nil _)
  have roots : header.function.body = [shape.outer.id] :=
    roots_injective (header.agreement.roots.symm.trans shape.roots)
  have expression : Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram)
      header.context header.function.evidence header.function.source [(shape.binder.id, ⟨0⟩)]
      (parameterHeap word) shape.lambda.id (.closure (capturedFunction header shape)) (capturedHeap word) := by
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound shape.lambdaFound)
    · rw [shape.lambdaForm]
      exact .lambda (by rw [shape.lambdaRequirements, shape.lambdaCoercions]; rfl) snapshot
    · rw [shape.lambdaCoercions]; exact .nil
  have body : Dynamic.FunctionStatementsExecute (Program.ofChecked compiled.sourceProgram)
      header.context header.function.evidence header.function.source [(shape.binder.id, ⟨0⟩)] (parameterHeap word)
      header.function.body header.context (.returned (.closure (capturedFunction header shape))) (capturedHeap word) := by
    rw [roots]
    exact .singleton (lookupStatement?_sound shape.outerFound)
      (by rw [shape.outerForm]; intro id impossible; cases impossible)
      (.returnValue (lookupStatement?_sound shape.outerFound) shape.outerForm expression)
  have invoked := sourceAt.frame.body_of_trace header.extended bound (FunctionCallBody.Trace.returned body)
  cases invoked with
  | value invoked =>
    exact ⟨rawD, global, sourceAt, .global sourceAt.frame.instantiated rfl
      (sourceAt.dictionary ▸ sourceAt.frame.covers) (sourceAt.dictionary ▸ invoked)⟩

/-- Copy the retained snapshot and read the copy, without observing a completed
direct call. -/
theorem closure_plain (word : Word) {context : SourceSemantics.Context} (invocation : Staging.Recursive.Scope)
    (signatures : context.signatures = (Program.ofChecked compiled.sourceProgram).signatures)
    (typed : Dynamic.ValueHasType context (capturedHeap word)
      (.closure (capturedFunction header shape)) (.function .unit .word)) :
    Dynamic.CallableApplies (Program.ofChecked compiled.sourceProgram) context invocation.evidence
      (capturedFunction header shape).evidence (capturedHeap word)
      (.closure (capturedFunction header shape)) [] (.word word) (calledHeap word) := by
  obtain ⟨_parameters, _result, sameSignatures, code, covers, _captures⟩ := typed.closure_function_inv
  have frame : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) (capturedFunction header shape) :=
    ⟨sameSignatures.trans signatures, code.owner, code, code.requirement_ledger.idsUnique, covers⟩
  have copy : Dynamic.EnvironmentCopies header.function.source [(shape.binder.id, ⟨1⟩)] (capturedHeap word)
      [(shape.binder.id, ⟨2⟩)] (calledHeap word) :=
    .copied shape.binderCopied (.intro (.tail .head)) .append (.nil _)
  have read : Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram)
      header.context header.function.evidence header.function.source [(shape.binder.id, ⟨2⟩)]
      (calledHeap word) shape.read.id (.word word) (calledHeap word) := by
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound shape.readFound)
    · rw [shape.readForm]
      exact .local (by rw [shape.readRequirements, shape.readCoercions]; rfl) .head
        (.intro (.tail (.tail .head))) rfl rfl
    · rw [shape.readCoercions]; exact .nil
  exact .closure rfl frame (.nil _) copy (.nil _ _)
    (.singleton (lookupStatement?_sound shape.innerFound)
      (by rw [shape.innerForm]; intro id impossible; cases impossible)
      (.returnValue (lookupStatement?_sound shape.innerFound) shape.innerForm read)) rfl

end Tests.SourceCoreSelectedCapturedDirect
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedCapturedDirectSourceFirst
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreSelectedCapturedDirect
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedFunctionValues (Header)
open SelectedCompilationCertifiedPublicSession (Profiled Initial)
open RecursiveNamedPublicPhysicalSessionState (StartedCall PlainValue SourceCall)
open RecursiveNamedPublicFunctionHistory (Entry)

variable {recipe : SourceCoreIndexedSession.Recipe} (issued : Profiled recipe)
  {header : Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
  (shape : Shape header.function.source) (word : Word)
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}

/-- The actual prior factory result fixes the closure's snapshot, and the call
reads its own copy. This next-call law has only a start receipt; the direct
call has not executed yet. -/
theorem direct_from_captured (entry : Entry)
    (state : issued.toIssued.State header session [entry])
    (heap : state.heap = capturedHeap word)
    (source : entry.source = .closure (capturedFunction header shape))
    (entryType : entry.sourceType = .function .unit .word)
    (handleType : entry.handle.sourceType = .function .unit .word)
    (ready : session.ExportsReady)
    {fuel : Nat} {checkpoint : SourceCoreExecution.Checkpoint artifact}
    (started : session.startHandlePacked entry.handle .unit fuel = .ok checkpoint)
    (invocation : Staging.Recursive.Scope) :
    Dynamic.CallableApplies (Program.ofChecked recipe.compiled.sourceProgram) header.function.context
      invocation.evidence (Staging.Recursive.callableEvidence entry.source)
      state.heap entry.source [] (.word word) (calledHeap word) ∧
    ((Staging.Recursive.Applies (Program.ofChecked recipe.compiled.sourceProgram)
        (SelectedCompilationPhysicalProgramSupport.stages recipe.compiled) invocation
        header.function.context state.heap entry.source [] (.value (.word word)) (calledHeap word) ∧
      SelectedCompilationPublicSessionDirectScalarForward.ForwardAt issued.catalog.rows header issued.initial
        issued.support.profile recipe [entry] (.word word) checkpoint (calledHeap word)) ∨
      SelectedCompilationStageClosedDirectForward.StageStopped issued state entry checkpoint invocation []) := by
  have typed := (state.history.semantic.current.2.2.2.2 entry (List.mem_singleton_self _)).2.2
  rw [entryType, source, heap] at typed
  have plain := closure_plain header shape word invocation
    (SelectedCompilationPublicHistorySourceInputs.header_runtime issued.support.bodyTyping header).signatures typed
  have ordinary : Dynamic.CallableApplies (Program.ofChecked recipe.compiled.sourceProgram) header.function.context
      invocation.evidence (Staging.Recursive.callableEvidence entry.source)
      state.heap entry.source [] (.word word) (calledHeap word) := by
    simpa only [source, heap, Staging.Recursive.callableEvidence] using plain
  have input : RecursiveNamedPublicFunctionHistoryInputs.Input [entry] header.function.context
      .unit .unit .unit := .data ⟨.unit, by simp [SourceCoreIndexedSession.DataInput.publicValue], .unit⟩ ⟨.unit, by simp [SourceCoreIndexedSession.DataInput.publicValue], .unit⟩
  exact ⟨ordinary, SelectedCompilationStageClosedDirectForward.scalar issued state entry
    (List.mem_singleton_self _) entryType input started ready .nil (.word word) rfl handleType ordinary⟩

variable {key : SourceCoreIndexedSession.Key} {options : SourceCoreExecution.RunOptions}
  (call : StartedCall session key [.word word] options) (initial : Initial issued.toIssued call)

/-- Factory and direct invocation are related before either public execution is
observed. All sufficiently fueled factory completions expose the exact closure. -/
def ForwardChain (shape : Shape initial.header.function.source) (invocation : Staging.Recursive.Scope) : Prop :=
  ∃ requiredExecution requiredOutput,
    ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome artifact),
      requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
      call.checkpoint.ResumeAt executionFuel outputFuel outcome →
      ∃ completion : SourceCoreExecution.Completion artifact,
        outcome = .succeeded completion ∧
        ∃ (entry : Entry) (state : issued.toIssued.State initial.header completion.session [entry]),
          completion.value = .function entry.handle ∧ state.heap = capturedHeap word ∧
          entry.source = .closure (capturedFunction initial.header shape) ∧
          ∀ fuel (checkpoint : SourceCoreExecution.Checkpoint artifact),
            completion.session.startHandlePacked entry.handle .unit fuel = .ok checkpoint →
            Dynamic.CallableApplies (Program.ofChecked recipe.compiled.sourceProgram) initial.header.function.context
              invocation.evidence (Staging.Recursive.callableEvidence entry.source)
              state.heap entry.source [] (.word word) (calledHeap word) ∧
            ((Staging.Recursive.Applies (Program.ofChecked recipe.compiled.sourceProgram)
                (SelectedCompilationPhysicalProgramSupport.stages recipe.compiled) invocation
                initial.header.function.context state.heap entry.source [] (.value (.word word)) (calledHeap word) ∧
              SelectedCompilationPublicSessionDirectScalarForward.ForwardAt issued.catalog.rows initial.header
                issued.initial issued.support.profile recipe [entry] (.word word) checkpoint (calledHeap word)) ∨
              SelectedCompilationStageClosedDirectForward.StageStopped issued state entry checkpoint invocation [])

/-- The lambda copies the original parameter allocation, and the subsequent
ordinary read of a call's copy drives the closed direct public theorem. -/
theorem initial_source_first (shape : Shape initial.header.function.source)
    (resultType : initial.header.function.resultType = .function .unit .word)
    (invocation : Staging.Recursive.Scope) :
    PlainValue initial.header initial.header invocation ⟨[]⟩ [.word word]
      (.closure (capturedFunction initial.header shape)) (capturedHeap word) ∧
    (ForwardChain issued word call initial shape invocation ∨
      SelectedCompilationStageClosedInitialForward.StageStopped issued call initial invocation [.word word]) := by
  obtain ⟨rawD, global, sourceAt⟩ :=
    (CallableIndexedOwnedPreparedFiniteNamedInventories.source_receipts issued.catalog.rows).receipts
      initial.header initial.start.selected.member
  have plain := factory_plain initial.header shape sourceAt invocation word
  have simple : ∀ value ∈ ([.word word] : List SourceCorePublicValues.Value),
      SourceCoreIndexedSession.SimplePublic value := by
    intro value member
    cases List.mem_singleton.mp member
    exact .word _
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes initial.header.function.context
      [.word word] initial.header.types := by
    rw [input_types initial.header shape]
    exact .cons ⟨.word word, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word word⟩ .nil
  have meanings : RecursiveNamedPublicDataInputs.Meanings [.word word] [.word word] :=
    .cons ⟨.word word, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word word⟩ .nil
  have forward := SelectedCompilationStageClosedInitialForward.function issued call initial simple inputTypes meanings
    (by rw [resultType]; rfl) plain
  refine ⟨plain, ?_⟩
  rcases forward with ⟨_source, requiredExecution, requiredOutput, forward⟩ | stopped
  · left
    refine ⟨requiredExecution, requiredOutput, ?_⟩
    intro executionFuel outputFuel outcome executionBound outputBound resumed
    obtain ⟨completion, actual, ready, entry, entryType, source, returned, handleType, state, heap⟩ :=
      forward executionFuel outputFuel outcome executionBound outputBound resumed
    rw [resultType] at entryType handleType
    refine ⟨completion, actual, entry, state, returned, heap, source, ?_⟩
    intro fuel checkpoint accepted
    exact direct_from_captured issued shape word entry state heap source entryType handleType ready accepted invocation
  · exact .inr stopped

/-- The same independent factory trace also determines the whole exported value
and its ordered collection of callable leaves. -/
theorem initial_whole_output (shape : Shape initial.header.function.source)
    (invocation : Staging.Recursive.Scope) :
    (SourceCall initial.header initial.header invocation ⟨[]⟩ [.word word]
        (.value (.closure (capturedFunction initial.header shape))) (capturedHeap word) ∧
      SelectedCompilationStageClosedDirectForward.Output.ForwardAt issued.catalog.rows initial.header
        issued.initial issued.support.profile recipe [] initial.header.function.resultType call.checkpoint
        (.closure (capturedFunction initial.header shape)) (capturedHeap word)) ∨
    SelectedCompilationStageClosedInitialForward.StageStopped issued call initial invocation [.word word] := by
  obtain ⟨rawD, global, sourceAt⟩ :=
    (CallableIndexedOwnedPreparedFiniteNamedInventories.source_receipts issued.catalog.rows).receipts
      initial.header initial.start.selected.member
  have plain := factory_plain initial.header shape sourceAt invocation word
  have simple : ∀ value ∈ ([.word word] : List SourceCorePublicValues.Value),
      SourceCoreIndexedSession.SimplePublic value := by
    intro value member
    cases List.mem_singleton.mp member
    exact .word _
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes initial.header.function.context
      [.word word] initial.header.types := by
    rw [input_types initial.header shape]
    exact .cons ⟨.word word, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word word⟩ .nil
  have meanings : RecursiveNamedPublicDataInputs.Meanings [.word word] [.word word] :=
    .cons ⟨.word word, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word word⟩ .nil
  exact SelectedCompilationStageClosedOutputForward.initial issued call initial simple inputTypes meanings plain

end Tests.SourceCoreSelectedCapturedDirect
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedCapturedDirectFixture
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreSelectedCapturedDirect
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open SelectedCompilationCertifiedPublicSession (Profiled Initial)
open RecursiveNamedPublicPhysicalSessionState (StartedCall PlainValue SourceCall)

def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content :=
    "function make(seed: Word) returns (function() returns (Word)) { return lam() { return seed; }; }"}] }

def options : SourceCompiler.Options := {checkingFuel := 1000, compilationFuel := 1000, specializationBudget := 128}
def runOptions : SourceCoreExecution.RunOptions := {executionFuel := 100000, outputValidationFuel := 1000}
def seed : Word := Word.ofNatModulo 37

private def observed (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
  if witness : p then pure ⟨witness⟩ else throw (IO.userError message)

def observeShape (source : TypedSource) : IO (Shape source) := do
  let [binder] := source.inputs | throw (IO.userError "captured source input shape")
  let [.expression read, .statement inner, .expression lambda, .statement outer] := source.nodes
    | throw (IO.userError "captured source occurrence shape")
  let ⟨inputs⟩ ← observed (source.inputs = [binder]) "captured inputs"
  let ⟨binderType⟩ ← observed (binder.scheme = .mono .word) "captured parameter type"
  let ⟨binderCopied⟩ ← observed (CaptureBinders.copiedBinder? source binder.id = some binder) "captured parameter copied"
  let ⟨roots⟩ ← observed (source.roots = [.statement outer.id]) "captured roots"
  let ⟨readFound⟩ ← observed (source.lookupExpression? read.id = some read) "captured read occurrence"
  let ⟨readForm⟩ ← observed (read.form = .reference binder.name (.local binder.id)) "captured read form"
  let ⟨readRequirements⟩ ← observed (read.requirements = []) "captured read requirements"
  let ⟨readCoercions⟩ ← observed (read.coercions = []) "captured read coercions"
  let ⟨innerFound⟩ ← observed (source.lookupStatement? inner.id = some inner) "captured inner occurrence"
  let ⟨innerForm⟩ ← observed (inner.form = .returnStmt (some read.id)) "captured inner return"
  let ⟨lambdaFound⟩ ← observed (source.lookupExpression? lambda.id = some lambda) "captured lambda occurrence"
  let ⟨lambdaForm⟩ ← observed (lambda.form = .lambda [] .word [inner.id]) "captured lambda"
  let ⟨lambdaRequirements⟩ ← observed (lambda.requirements = []) "captured lambda requirements"
  let ⟨lambdaCoercions⟩ ← observed (lambda.coercions = []) "captured lambda coercions"
  let ⟨outerFound⟩ ← observed (source.lookupStatement? outer.id = some outer) "captured outer occurrence"
  let ⟨outerForm⟩ ← observed (outer.form = .returnStmt (some lambda.id)) "captured outer return"
  return {
    binder := binder
    read := read
    inner := inner
    lambda := lambda
    outer := outer
    inputs := inputs
    binderType := binderType
    binderCopied := binderCopied
    roots := roots
    readFound := readFound
    readForm := readForm
    readRequirements := readRequirements
    readCoercions := readCoercions
    innerFound := innerFound
    innerForm := innerForm
    lambdaFound := lambdaFound
    lambdaForm := lambdaForm
    lambdaRequirements := lambdaRequirements
    lambdaCoercions := lambdaCoercions
    outerFound := outerFound
    outerForm := outerForm }

structure Fixture where
  recipe : SourceCoreIndexedSession.Recipe
  checked : checkProgram workspace options.checkingFuel = .ok recipe.compiled.sourceProgram
  seeds : List SourceCompiler.Seed
  facade : SourceCoreExecution.Compiled
  accepted : SourceCompiler.compileChecked recipe.compiled.sourceProgram seeds options = .ok facade
  selected : RecursiveNamedPreparedStageContracts.PublicRecipe facade recipe
  profile : CompilerProgramStaticProfile.StaticProfile recipe.compiled
  original : SourceSpecialization.SpecializedFunction
  originalMember : original ∈ recipe.compiled.validationPlan.specializations
  named : SourceCoreGeneralFunctions.Function
  functions : recipe.compiled.indexed.base.functions = [named]
  shape : Shape named.specialized.function.typedBody
  resultType : named.specialized.function.inferredBodyType = .function .unit .word
  substitution : named.specialized.parameterSubstitution = []
  ordinary : named.specialized.function.returnComptime = false
  ordinaryInputs : ∀ binder ∈ named.specialized.function.typedBody.inputs, binder.comptime = false
  slot : CallableNamedMetadata.Slot recipe.compiled.indexed.base.globals 0 named.signature

/-- This fixture contains actual checker/compiler observations only. -/
def fixture : IO Fixture := do
  match checked : checkProgram workspace options.checkingFuel with
  | .error errors => throw (IO.userError (reprStr errors))
  | .ok program =>
    let seeds := program.signatures.functions.map (fun signature => SourceCompiler.Seed.declaration signature.id)
    match generated : SourceCoreCompiler.compileChecked program seeds options with
    | .error error => throw (IO.userError (reprStr error))
    | .ok source =>
      match present : source.artifact? with
      | none => throw (IO.userError "captured artifact absent")
      | some cached =>
        match prepared : SourceCoreIndexedSession.Recipe.prepare cached with
        | .error error => throw (IO.userError (reprStr error))
        | .ok recipe =>
          match facade : SourceCoreExecution.prepare source with
          | .error error => throw (IO.userError (reprStr error))
          | .ok publicCompiled =>
            have sameProgram : recipe.compiled.sourceProgram = program :=
              (congrArg (·.sourceProgram) (SourceCoreIndexedSession.Recipe.prepare_compiled prepared)).trans
                ((source.artifact_fields present).1.trans (SourceCoreCompiler.compileChecked_program generated))
            have original : checkProgram workspace options.checkingFuel = .ok recipe.compiled.sourceProgram := by
              rw [sameProgram]; exact checked
            have accepted : SourceCompiler.compileChecked recipe.compiled.sourceProgram seeds options = .ok publicCompiled := by
              rw [sameProgram]
              simpa only [SourceCoreExecution.compileChecked, generated, Except.mapError, bind, Except.bind] using facade
            let some profile := SelectedCompilationCompilerStaticProfile.validateCheckedProfile recipe.compiled original
              | throw (IO.userError "captured selected profile rejected")
            match originals : recipe.compiled.validationPlan.specializations with
            | [] => throw (IO.userError "captured original row absent")
            | originalRow :: rest =>
              match functions : recipe.compiled.indexed.base.functions with
              | [named] =>
                let shape ← observeShape named.specialized.function.typedBody
                let ⟨resultType⟩ ← observed (named.specialized.function.inferredBodyType = .function .unit .word) "captured factory result"
                let ⟨substitution⟩ ← observed (named.specialized.parameterSubstitution = []) "captured substitution"
                let ⟨ordinary⟩ ← observed (named.specialized.function.returnComptime = false) "captured factory marker"
                let ⟨ordinaryInputs⟩ ← observed (named.specialized.function.typedBody.inputs.all (fun binder => !binder.comptime) = true) "captured parameter markers"
                let ⟨slot⟩ ← observed (recipe.compiled.indexed.base.globals.zipIdx.filter (fun item => decide (item.1.key = named.signature.key)) = [(named.signature, 0)]) "captured physical slot"
                return {
                  recipe := recipe
                  checked := original
                  seeds := seeds
                  facade := publicCompiled
                  accepted := accepted
                  selected := RecursiveNamedPreparedStageContracts.public_preparation present prepared facade
                  profile := profile
                  original := originalRow
                  originalMember := by
                    rw [originals]
                    exact List.mem_cons_self
                  named := named
                  functions := functions
                  shape := shape
                  resultType := resultType
                  substitution := substitution
                  ordinary := ordinary
                  ordinaryInputs := by
                    intro binder member
                    have same := List.all_eq_true.mp ordinaryInputs binder member
                    cases marker : binder.comptime <;> simp_all
                  slot := slot }
              | _ => throw (IO.userError "captured cache shape")

theorem Fixture.eligible (fixture : Fixture) :
    Nonempty (SelectedCompilationCertifiedPublicSession.EligibleRow fixture.recipe.compiled fixture.named.signature.key) := by
  obtain ⟨prepared⟩ := RecursiveNamedPublicSpecializationMeaning.of_public_compile fixture.accepted
    fixture.selected fixture.originalMember
  have member := List.mem_of_getElem? prepared.selected
  rw [fixture.functions] at member
  have same := List.mem_singleton.mp member
  have origin : RecursiveNamedPublicSpecializationMeaning.Origin fixture.recipe.compiled.sourceProgram fixture.named.specialized := by
    rw [← same, prepared.same]
    exact prepared.origin
  have range : ParameterSubstitution.RangeWellFormed (SourceSemantics.Context.ofSignatures fixture.recipe.compiled.sourceProgram.signatures)
      fixture.named.specialized.parameterSubstitution := by
    rw [fixture.substitution]
    intro parameter replacement impossible
    cases impossible
  exact ⟨⟨fixture.named, 0, fixture.named.signature,
    by rw [fixture.functions]; rfl, fixture.slot, rfl,
    ⟨origin, range, fixture.ordinary, fixture.ordinaryInputs⟩⟩⟩

structure Started (fixture : Fixture) where
  artifact : SourceCoreExecution.Artifact
  opened : artifact.CompiledAt fixture.facade
  bootstrap : SourceCoreExecution.Bootstrap artifact
  fresh : bootstrap.FreshAt
  authority : bootstrap.ExportAuthorityAt
  session : SourceCoreExecution.Session artifact
  ready : bootstrap.resume 100000 = .ready session
  call : StartedCall session fixture.named.signature.key [.word seed] runOptions

def observeStarted (fixture : Fixture) : IO (Started fixture) := do
  let opened ← fixture.facade.openWithReceipt
  let bootstrap ← opened.val.bootstrapWithExportReceipt
  match ready : bootstrap.val.resume 100000 with
  | .error error => throw (IO.userError (reprStr error))
  | .outOfFuel _ => throw (IO.userError "captured bootstrap exhausted")
  | .ready session =>
    match started : session.start fixture.named.signature.key [.word seed] runOptions.inputValidationFuel with
    | .error error => throw (IO.userError (reprStr error))
    | .ok checkpoint => return ⟨opened.val, opened.property, bootstrap.val, bootstrap.property.1,
        bootstrap.property.2, session, ready, checkpoint, started⟩

theorem from_source (fixture : Fixture) (started : Started fixture) :
    ∃ (issued : Profiled fixture.recipe) (initial : Initial issued.toIssued started.call)
      (shape : Shape initial.header.function.source),
      ∀ invocation, PlainValue initial.header initial.header invocation ⟨[]⟩ [.word seed]
        (.closure (capturedFunction initial.header shape)) (capturedHeap seed) ∧
        (ForwardChain issued seed started.call initial shape invocation ∨
          SelectedCompilationStageClosedInitialForward.StageStopped issued started.call initial invocation [.word seed]) ∧
        ((SourceCall initial.header initial.header invocation ⟨[]⟩ [.word seed]
            (.value (.closure (capturedFunction initial.header shape))) (capturedHeap seed) ∧
          SelectedCompilationStageClosedDirectForward.Output.ForwardAt issued.catalog.rows initial.header
            issued.initial issued.support.profile fixture.recipe [] initial.header.function.resultType started.call.checkpoint
            (.closure (capturedFunction initial.header shape)) (capturedHeap seed)) ∨
          SelectedCompilationStageClosedInitialForward.StageStopped issued started.call initial invocation [.word seed]) := by
  obtain ⟨row⟩ := fixture.eligible
  obtain ⟨issued, initial, namedEq⟩ := SelectedCompilationCertifiedPublicSession.from_checked_profiled_initial_row
    fixture.checked fixture.accepted fixture.selected fixture.profile started.opened started.call
    started.bootstrap started.fresh started.authority (.single started.ready) row
  have rowSame : row.named = fixture.named := by
    have member := List.mem_of_getElem? row.cached
    rw [fixture.functions] at member
    exact List.mem_singleton.mp member
  have sourceEq := initial.header.agreement.source.trans (congrArg (fun named => named.specialized.function.typedBody)
    (namedEq.trans rowSame))
  let shape : Shape initial.header.function.source := sourceEq.symm ▸ fixture.shape
  have resultType : initial.header.function.resultType = .function .unit .word := by
    rw [initial.header.agreement.result, namedEq, rowSame]
    exact fixture.resultType
  refine ⟨issued, initial, shape, ?_⟩
  intro invocation
  have first := initial_source_first issued seed started.call initial shape resultType invocation
  exact ⟨first.1, first.2, initial_whole_output issued seed started.call initial shape invocation⟩

end Tests.SourceCoreSelectedCapturedDirect
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedCapturedDirectRuntime
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedCapturedDirect
open Solcore Frontend SourceInference SourceSemantics CoreLowering

private def require (condition : Bool) (message : String) : IO Unit :=
  if condition then pure () else throw (IO.userError message)

def run : IO Unit := do
  let fixture ← fixture
  let started ← observeStarted fixture
  have _sourceFirst := from_source fixture started
  let .outOfFuel factorySuspended ← started.call.checkpoint.resume 0 0
    | throw (IO.userError "captured factory did not suspend at zero fuel")
  let .succeeded factory ← factorySuspended.resume 100000 1000
    | throw (IO.userError "captured factory did not complete")
  let .function handle := factory.value
    | throw (IO.userError "captured factory did not return its closure handle")
  require (handle.sourceType == .function .unit .word) "captured handle type changed"
  let .ok checkpoint := factory.session.startHandlePacked handle .unit runOptions.inputValidationFuel
    | throw (IO.userError "captured direct call did not start")
  let .outOfFuel suspended ← checkpoint.resume 0 0
    | throw (IO.userError "captured direct call did not suspend at zero fuel")
  let .succeeded first ← suspended.resume 100000 1000
    | throw (IO.userError "captured direct call did not complete")
  require (first.value == .word seed) "captured Source read changed"
  let .ok repeatedCheckpoint := first.session.startHandlePacked handle .unit runOptions.inputValidationFuel
    | throw (IO.userError "captured handle was not retained after the direct call")
  let .succeeded repeated ← repeatedCheckpoint.resume 100000 1000
    | throw (IO.userError "retained captured call did not complete")
  require (repeated.value == .word seed) "retained captured Source read changed"
  require ([started.session.heapSize, factory.session.heapSize, first.session.heapSize, repeated.session.heapSize]
    == [2, 8, 11, 14]) "captured direct heap sizes changed"
  require (fixture.recipe.compiled.indexed.base.functions.length == 1) "captured cache changed"
  IO.println s!"SOURCE_FIRST_DIRECT_CAPTURED_PASS: actual checked factory copies parameter37 into its snapshot at Source location1 and each call reads its own copy; independently constructed factory and direct closure traces before execution; closed initial function/full-output and retained direct scalar alternatives; zero-fuel factory/direct resume; old closure handle repeated; heaps{[started.session.heapSize, factory.session.heapSize, first.session.heapSize, repeated.session.heapSize]}"

end Tests.SourceCoreSelectedCapturedDirect
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedCoercedDirectSource
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreSelectedCoercedDirect
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedFunctionValues (Header NamedSourceAt)

structure Shape (source : TypedSource) where
  binder : TypedBinder
  read : ExpressionNode
  call : ExpressionNode
  inner : StatementNode
  lambda : ExpressionNode
  outer : StatementNode
  inputs : source.inputs = [binder]
  binderType : binder.scheme = .mono .bool
  binderCopied : CaptureBinders.copiedBinder? source binder.id = some binder
  roots : source.roots = [.statement outer.id]
  readFound : source.lookupExpression? read.id = some read
  readForm : read.form = .reference binder.name (.local binder.id)
  readRequirements : read.requirements = []
  readCoercions : read.coercions = []
  innerFound : source.lookupStatement? inner.id = some inner
  innerForm : inner.form = .returnStmt (some call.id)
  lambdaFound : source.lookupExpression? lambda.id = some lambda
  lambdaForm : lambda.form = .lambda [] .word [inner.id]
  lambdaRequirements : lambda.requirements = []
  lambdaCoercions : lambda.coercions = []
  outerFound : source.lookupStatement? outer.id = some outer
  outerForm : outer.form = .returnStmt (some lambda.id)

def capturedCell (flag : Bool) : Dynamic.Cell := {type := .bool, value := some (.bool flag)}

/-- The factory's parameter cell. -/
def parameterHeap (flag : Bool) : Dynamic.Heap := ⟨[capturedCell flag]⟩

/-- The parameter cell and the closure's snapshot of it. -/
def capturedHeap (flag : Bool) : Dynamic.Heap := ⟨[capturedCell flag, capturedCell flag]⟩

/-- A call appends its own copy of the snapshot. -/
def calledHeap (flag : Bool) : Dynamic.Heap :=
  ⟨[capturedCell flag, capturedCell flag, capturedCell flag]⟩

def capturedFunction {compiled : SourceCoreUnifiedCompilation.Compiled}
    (header : Header compiled (Program.ofChecked compiled.sourceProgram))
    (shape : Shape header.function.source) : Dynamic.Closure := {
  parameters := [], resultType := .word, body := [shape.inner.id]
  source := header.function.source, captured := [(shape.binder.id, ⟨1⟩)]
  context := header.context, evidence := header.function.evidence }

private theorem roots_injective {left right : List StatementId}
    (same : left.map NodeId.statement = right.map NodeId.statement) : left = right := by
  induction left generalizing right with
  | nil => cases right <;> simp at same ⊢
  | cons head rest ih =>
    cases right with
    | nil => simp at same
    | cons other tail =>
      simp only [List.map_cons, List.cons.injEq] at same
      cases same.1
      exact congrArg (List.cons head) (ih same.2)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (header : Header compiled (Program.ofChecked compiled.sourceProgram))
  (shape : Shape header.function.source)

include shape in
theorem input_types : header.types = [.bool] := by
  have params : header.function.parameters = [shape.binder] :=
    header.parameters.trans (header.inputs.symm.trans shape.inputs)
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq header.extended
  simpa only [params, List.map_cons, List.map_nil, shape.binderType, TypeSystem.Scheme.mono] using types.symm

/-- Build the factory execution directly from its original allocation and
lambda, which copies the parameter cell into the closure's snapshot. -/
theorem factory_plain {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {global : Dynamic.GlobalFunction}
    (sourceAt : NamedSourceAt header rawD global) (invocation : Staging.Recursive.Scope) (flag : Bool) :
    RecursiveNamedPublicPhysicalSessionState.PlainValue header header invocation ⟨[]⟩ [.bool flag]
      (.closure (capturedFunction header shape)) (capturedHeap flag) := by
  have params : header.function.parameters = [shape.binder] :=
    header.parameters.trans (header.inputs.symm.trans shape.inputs)
  have allocated : Dynamic.Heap.Allocates ⟨[]⟩ shape.binder.scheme.body
      (some (.bool flag)) ⟨0⟩ (parameterHeap flag) := by
    rw [shape.binderType]
    exact .append
  have bound : Dynamic.BindersAllocate [] ⟨[]⟩ header.function.parameters [.bool flag]
      [(shape.binder.id, ⟨0⟩)] (parameterHeap flag) := by
    rw [params]
    exact .cons allocated (.nil _ _)
  have stored : Dynamic.Heap.Allocates ⟨[]⟩ .bool (some (.bool flag)) ⟨0⟩ (parameterHeap flag) := .append
  have snapshot : Dynamic.EnvironmentCopies header.function.source [(shape.binder.id, ⟨0⟩)]
      (parameterHeap flag) [(shape.binder.id, ⟨1⟩)] (capturedHeap flag) :=
    .copied shape.binderCopied stored.reads_new .append (.nil _)
  have roots : header.function.body = [shape.outer.id] :=
    roots_injective (header.agreement.roots.symm.trans shape.roots)
  have expression : Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram)
      header.context header.function.evidence header.function.source [(shape.binder.id, ⟨0⟩)]
      (parameterHeap flag) shape.lambda.id (.closure (capturedFunction header shape)) (capturedHeap flag) := by
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound shape.lambdaFound)
    · rw [shape.lambdaForm]
      exact .lambda (by rw [shape.lambdaRequirements, shape.lambdaCoercions]; rfl) snapshot
    · rw [shape.lambdaCoercions]; exact .nil
  have body : Dynamic.FunctionStatementsExecute (Program.ofChecked compiled.sourceProgram)
      header.context header.function.evidence header.function.source [(shape.binder.id, ⟨0⟩)] (parameterHeap flag)
      header.function.body header.context (.returned (.closure (capturedFunction header shape))) (capturedHeap flag) := by
    rw [roots]
    exact .singleton (lookupStatement?_sound shape.outerFound)
      (by rw [shape.outerForm]; intro id impossible; cases impossible)
      (.returnValue (lookupStatement?_sound shape.outerFound) shape.outerForm expression)
  have invoked := sourceAt.frame.body_of_trace header.extended bound (FunctionCallBody.Trace.returned body)
  cases invoked with
  | value invoked =>
    exact ⟨rawD, global, sourceAt, .global sourceAt.frame.instantiated rfl
      (sourceAt.dictionary ▸ sourceAt.frame.covers) (sourceAt.dictionary ▸ invoked)⟩

def appendBool (before : Dynamic.Heap) (flag : Bool) : Dynamic.Heap :=
  ⟨before.cells ++ [{type := .bool, value := some (.bool flag)}]⟩

/-- The numeric literal uses its original requirement and complete solved ledger. -/
theorem word_plain {program : SourceSemantics.Program} {function : CheckedFunction}
    (literal : Tests.SourceCoreCoercionPublic.WordLiteral function)
    {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    (ledger : context.solvedRequirements = function.solvedRequirements)
    (runtime : RuntimeRequirementLedgerValid context) :
    Dynamic.ExpressionEvaluates program context evidence function.typedBody environment heap
      literal.node.id (.word literal.validated.value) heap := by
  have metadata := SourceCoreElaboration.validateWordIntegerLiteral_sound literal.accepted
  apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound literal.found)
  · rw [literal.form]
    exact .integerLiteral (by rw [metadata.requirements, metadata.coercions]; rfl)
      (NumericLiteralEvidenceReceipts.word_constructs literal.accepted ledger runtime)
  · rw [metadata.coercions]; exact .nil

/-- Construct the selected method's ordinary allocation, read and chosen branch.
Its static extension and numeric ledger come from the exact selected body. -/
theorem method_plain {program : SourceSemantics.Program} {body : Dynamic.BodyInstance}
    {function : CheckedFunction} {signature : ProgramFunctionSignature}
    (method : Tests.SourceCoreCoercionPublic.MethodShape function signature)
    (source : body.source = function.typedBody)
    {types : List TypeSystem.Ty} {context : SourceSemantics.Context}
    (extended : MonoBindersExtend body.source.owner body.context body.source.inputs types context)
    (scheme : method.binder.scheme = .mono .bool)
    (ledger : context.solvedRequirements = function.solvedRequirements)
    (runtime : RuntimeRequirementLedgerValid context)
    {evidence : Dynamic.EvidenceEnvironment} (covers : evidence.Covers body.context)
    (before : Dynamic.Heap) (flag : Bool) :
    Dynamic.BodyInvokes program body evidence before [.bool flag]
      (.word (if flag then method.first.validated.value else method.second.validated.value))
      (appendBool before flag) := by
  let environment : Dynamic.Environment := [(method.binder.id, ⟨before.cells.length⟩)]
  have allocated : Dynamic.Heap.Allocates before method.binder.scheme.body
      (some (.bool flag)) ⟨before.cells.length⟩ (appendBool before flag) := by
    rw [scheme]; exact .append
  have bound : Dynamic.BindersAllocate [] before body.source.inputs [.bool flag]
      environment (appendBool before flag) := by
    rw [source, method.inputs]
    exact .cons allocated (.nil _ _)
  have read : Dynamic.ExpressionEvaluates program context evidence function.typedBody environment
      (appendBool before flag) method.read.node.id (.bool flag) (appendBool before flag) := by
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound method.read.found)
    · rw [method.read.form]
      exact .local (by rw [method.read.requirements, method.read.coercions]; rfl)
        .head allocated.reads_new rfl rfl
    · rw [method.read.coercions]; exact .nil
  have expression : Dynamic.ExpressionEvaluates program context evidence function.typedBody environment
      (appendBool before flag) method.value.node.id
      (.word (if flag then method.first.validated.value else method.second.validated.value))
      (appendBool before flag) := by
    cases flag with
    | false =>
      apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound method.value.found)
      · rw [method.conditional]
        exact .conditionalFalse (by rw [method.value.requirements, method.value.coercions]; rfl)
          read (word_plain method.second ledger runtime)
      · rw [method.value.coercions]; exact .nil
    | true =>
      apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound method.value.found)
      · rw [method.conditional]
        exact .conditionalTrue (by rw [method.value.requirements, method.value.coercions]; rfl)
          read (word_plain method.first ledger runtime)
      · rw [method.value.coercions]; exact .nil
  have roots : Dynamic.StatementRoots body.source.roots [method.statement.id] := by
    rw [source, method.roots]; exact .cons .nil
  have executed : Dynamic.FunctionStatementsExecute program context evidence body.source environment
      (appendBool before flag) [method.statement.id] context
      (.returned (.word (if flag then method.first.validated.value else method.second.validated.value)))
      (appendBool before flag) := by
    rw [source]
    exact .singleton (lookupStatement?_sound method.statementFound)
      (by rw [method.statementForm]; intro id impossible; cases impossible)
      (.returnValue (lookupStatement?_sound method.statementFound) method.statementForm expression)
  exact .returned covers roots extended bound executed rfl

/-- The generic target keeps its full retained instantiation and dictionary. -/
theorem identity_plain {function : CheckedFunction}
    (identity : Tests.SourceCoreCoercionPublic.SelectedIdentityShape function .bool)
    (source : header.function.source = function.typedBody)
    (scheme : identity.binder.scheme = .mono .bool)
    {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    (before : Dynamic.Heap) (flag : Bool) :
    Dynamic.CallableApplies (Program.ofChecked compiled.sourceProgram) context evidence header.function.evidence
      before (.global ⟨header.instantiation, header.function.evidence⟩) [.bool flag]
      (.bool flag) (appendBool before flag) := by
  have parameters : header.function.parameters = [identity.binder] := by
    rw [header.parameters, ← header.inputs, source, identity.inputs]
  have allocated : Dynamic.Heap.Allocates before identity.binder.scheme.body
      (some (.bool flag)) ⟨before.cells.length⟩ (appendBool before flag) := by
    rw [scheme]; exact .append
  have bound : Dynamic.BindersAllocate [] before header.function.parameters [.bool flag]
      [(identity.binder.id, ⟨before.cells.length⟩)] (appendBool before flag) := by
    rw [parameters]; exact .cons allocated (.nil _ _)
  have roots : header.function.body = [identity.statement.id] :=
    roots_injective (header.agreement.roots.symm.trans (by rw [source, identity.roots]; rfl))
  have read : Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram)
      header.context header.function.evidence header.function.source
      [(identity.binder.id, ⟨before.cells.length⟩)] (appendBool before flag)
      identity.read.node.id (.bool flag) (appendBool before flag) := by
    rw [source]
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound identity.read.found)
    · rw [identity.read.form]
      exact .local (by rw [identity.read.requirements, identity.read.coercions]; rfl)
        .head allocated.reads_new rfl rfl
    · rw [identity.read.coercions]; exact .nil
  have body : Dynamic.FunctionStatementsExecute (Program.ofChecked compiled.sourceProgram)
      header.context header.function.evidence header.function.source
      [(identity.binder.id, ⟨before.cells.length⟩)] (appendBool before flag)
      header.function.body header.context (.returned (.bool flag)) (appendBool before flag) := by
    rw [source] at read
    rw [roots, source]
    exact .singleton (lookupStatement?_sound identity.statementFound)
      (by rw [identity.statementForm]; intro id impossible; cases impossible)
      (.returnValue (lookupStatement?_sound identity.statementFound) identity.statementForm read)
  have invoked := header.frame.body_of_trace header.extended bound (FunctionCallBody.Trace.returned body)
  cases invoked with
  | value invoked => exact .global header.frame.instantiated rfl header.frame.covers invoked

end Tests.SourceCoreSelectedCoercedDirect
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedCoercedDirectFixture
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreSelectedCoercedDirect
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open SelectedCompilationCertifiedPublicSession (Profiled Initial)
open RecursiveNamedPublicPhysicalSessionState (StartedCall)

private def observed (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
  if witness : p then pure ⟨witness⟩ else throw (IO.userError message)

structure Row (compiled : SourceCoreUnifiedCompilation.Compiled) where
  named : SourceCoreGeneralFunctions.Function
  index : Nat
  cached : compiled.indexed.base.functions[index]? = some named
  eligible : CallableIndexedOwnedPreparedOrdinaryCatalogReceipts.Eligible compiled named.specialized

structure Fixture where
  recipe : SourceCoreIndexedSession.Recipe
  checked : checkProgram Tests.SourceCoreCoercionPublic.workspace 1024 = .ok recipe.compiled.sourceProgram
  seeds : List SourceCompiler.Seed
  options : SourceCompiler.Options
  facade : SourceCoreExecution.Compiled
  accepted : SourceCompiler.compileChecked recipe.compiled.sourceProgram seeds options = .ok facade
  selected : RecursiveNamedPreparedStageContracts.PublicRecipe facade recipe
  profile : CompilerProgramStaticProfile.StaticProfile recipe.compiled
  closed : CompilerCoercedMethodProfile.Closed recipe.compiled
  make : Row recipe.compiled
  keep : Row recipe.compiled
  makeSignature : ProgramFunctionSignature
  keepSignature : ProgramFunctionSignature
  parameter : TypeSystem.TypeParameterId
  mark : ProgramTraitSignature
  coercion : ProgramTraitSignature
  shape : Tests.SourceCoreCoercionPublic.FactoryShape make.named.specialized.function
    makeSignature keepSignature parameter mark coercion
  identity : Tests.SourceCoreCoercionPublic.SelectedIdentityShape keep.named.specialized.function .bool
  makeResult : make.named.specialized.function.inferredBodyType = .function .unit .word
  makeBinder : shape.binder.scheme = .mono .bool
  makeCopied : CaptureBinders.copiedBinder? make.named.specialized.function.typedBody shape.binder.id = some shape.binder
  keepBinder : identity.binder.scheme = .mono .bool
  target : shape.call.instantiation = CallableNamedCanonicalOrder.retainedInstantiation keep.named.specialized
  available : SourceTypedRuntime.RuntimeEvidenceEnvironment
  resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment recipe.compiled.sourceProgram
    make.named.specialized.key make.named.specialized.assumptions = .ok available
  dictionary : SourceTypedRuntime.RuntimeEvidenceEnvironment
  direct : SourceCompilationPlan.exactDirectCallRuntimeEvidence make.named.specialized shape.call.node available shape.call.instantiation = .ok dictionary
  authenticated : SourceCompilationPlan.validateAuthenticatedRuntimeEvidence recipe.compiled.sourceProgram.signatures
    keep.named.specialized.key shape.call.instantiation.predicates dictionary = .ok ()
  keepResolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment recipe.compiled.sourceProgram
    keep.named.specialized.key keep.named.specialized.assumptions = .ok dictionary
  method : ExecutableImplMethods.CheckedMethod
  methodSelected : SourceCompilationPlan.checkedCoercionMethod recipe.compiled.sourceProgram
    make.named.specialized shape.call.node available shape.call.step = .ok method
  methodDictionary : SourceTypedRuntime.RuntimeEvidenceEnvironment
  materialized : SourceCompilationPlan.coercionMethodRuntimeEvidence recipe.compiled.sourceProgram
    make.named.specialized shape.call.node shape.call.step method = .ok methodDictionary
  methodMember : method.specialized ∈ recipe.compiled.indexed.base.plan.specializations
  methodShape : Tests.SourceCoreCoercionPublic.MethodShape method.specialized.function method.synthetic
  methodBinder : methodShape.binder.scheme = .mono .bool
  firstValue : methodShape.first.validated.value = Word.ofNatModulo 41
  secondValue : methodShape.second.validated.value = Word.ofNatModulo 7

private def rowOfObserved {fixture : Tests.SourceCoreCoercionPublic.CompiledFixture}
    {signature : ProgramFunctionSignature} (row : Tests.SourceCoreCoercionPublic.ObservedRow fixture signature) :
    Row fixture.recipe.compiled :=
  ⟨row.named, row.index, row.cached, row.same.symm ▸ row.eligible⟩

/-- Retain only actual checker, compiler, flat-profile and metadata receipts. -/
def fixture : IO Fixture := do
  let original ← Tests.SourceCoreCoercionPublic.compiledFixture
  let actual ← Tests.SourceCoreCoercionPublic.observeProgram original
  let compiled := original.recipe.compiled
  have checked : checkProgram Tests.SourceCoreCoercionPublic.workspace 1024 = .ok compiled.sourceProgram :=
    original.sameProgram.symm ▸ original.checked
  let some profile := SelectedCompilationCompilerStaticProfile.validateCheckedProfile compiled checked
    | throw (IO.userError "coerced automatic profile rejected")
  let some closed := CompilerCoercedMethodProfile.certify compiled
    | throw (IO.userError "closed method catalog rejected")
  let make := rowOfObserved actual.makeRow.toObservedRow
  let keep := rowOfObserved actual.keepRow
  let shape : Tests.SourceCoreCoercionPublic.FactoryShape make.named.specialized.function
      original.makeSignature original.keepSignature original.parameter original.mark original.coercion :=
    actual.makeRow.same.symm ▸ actual.makeShape
  let identity : Tests.SourceCoreCoercionPublic.SelectedIdentityShape keep.named.specialized.function .bool :=
    actual.keepRow.same.symm ▸ actual.keepShape
  let ⟨makeResult⟩ ← observed (make.named.specialized.function.inferredBodyType = .function .unit .word) "coerced factory result"
  let ⟨makeBinder⟩ ← observed (shape.binder.scheme = .mono .bool) "coerced original make binder"
  let ⟨makeCopied⟩ ← observed (CaptureBinders.copiedBinder? make.named.specialized.function.typedBody shape.binder.id =
    some shape.binder) "coerced original make binder copied"
  let ⟨keepBinder⟩ ← observed (identity.binder.scheme = .mono .bool) "coerced original keep binder"
  let ⟨target⟩ ← observed (shape.call.instantiation = CallableNamedCanonicalOrder.retainedInstantiation keep.named.specialized) "coerced complete direct instantiation"
  match resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment compiled.sourceProgram
      make.named.specialized.key make.named.specialized.assumptions with
  | .error error => throw (IO.userError (reprStr error))
  | .ok available =>
    match direct : SourceCompilationPlan.exactDirectCallRuntimeEvidence make.named.specialized shape.call.node available shape.call.instantiation with
    | .error error => throw (IO.userError (reprStr error))
    | .ok dictionary =>
      match authenticated : SourceCompilationPlan.validateAuthenticatedRuntimeEvidence compiled.sourceProgram.signatures
          keep.named.specialized.key shape.call.instantiation.predicates dictionary with
      | .error error => throw (IO.userError (reprStr error))
      | .ok () =>
        let ⟨keepResolved⟩ ← (do
          match accepted : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment compiled.sourceProgram
              keep.named.specialized.key keep.named.specialized.assumptions with
          | .error error => throw (IO.userError (reprStr error))
          | .ok actual =>
            let ⟨same⟩ ← observed ((actual == dictionary) = true) "coerced ordered callee dictionary"
            return ⟨eq_of_beq same ▸ accepted⟩ : IO (PLift (
              SourceCompilationPlan.resolveRuntimeEvidenceEnvironment compiled.sourceProgram
                keep.named.specialized.key keep.named.specialized.assumptions = .ok dictionary)))
        match methodSelected : SourceCompilationPlan.checkedCoercionMethod compiled.sourceProgram make.named.specialized
            shape.call.node available shape.call.step with
        | .error error => throw (IO.userError (reprStr error))
        | .ok method =>
          match materialized : SourceCompilationPlan.coercionMethodRuntimeEvidence compiled.sourceProgram
              make.named.specialized shape.call.node shape.call.step method with
          | .error error => throw (IO.userError (reprStr error))
          | .ok methodDictionary =>
            let ⟨methodMember⟩ ← observed (method.specialized ∈ compiled.indexed.base.plan.specializations) "coerced actual full method record"
            let methodShape ← Tests.SourceCoreCoercionPublic.observeMethod method.specialized.function method.synthetic
            let ⟨methodBinder⟩ ← observed (methodShape.binder.scheme = .mono .bool) "coerced method binder"
            let ⟨firstValue⟩ ← observed (methodShape.first.validated.value = Word.ofNatModulo 41) "coerced true result"
            let ⟨secondValue⟩ ← observed (methodShape.second.validated.value = Word.ofNatModulo 7) "coerced false result"
            return {
              recipe := original.recipe
              checked := checked
              seeds := original.seeds
              options := original.options
              facade := original.facadeCompiled
              accepted := by rw [original.sameProgram]; exact original.accepted
              selected := original.issued
              profile := profile
              closed := closed
              make := make
              keep := keep
              makeSignature := original.makeSignature
              keepSignature := original.keepSignature
              parameter := original.parameter
              mark := original.mark
              coercion := original.coercion
              shape := shape
              identity := identity
              makeResult := makeResult
              makeBinder := makeBinder
              makeCopied := makeCopied
              keepBinder := keepBinder
              target := target
              available := available
              resolved := resolved
              dictionary := dictionary
              direct := direct
              authenticated := authenticated
              keepResolved := keepResolved
              method := method
              methodSelected := methodSelected
              methodDictionary := methodDictionary
              materialized := materialized
              methodMember := methodMember
              methodShape := methodShape
              methodBinder := methodBinder
              firstValue := firstValue
              secondValue := secondValue
            }

end Tests.SourceCoreSelectedCoercedDirect
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedCoercedDirectMeaning
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
namespace Tests.SourceCoreSelectedCoercedDirect
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory)
open SelectedCompilationCertifiedPublicSession (Profiled Initial)

structure HeaderFacts {compiled : SourceCoreUnifiedCompilation.Compiled}
    (row : SourceSpecialization.SpecializedFunction) (available : SourceTypedRuntime.RuntimeEvidenceEnvironment)
    (header : Header compiled (Program.ofChecked compiled.sourceProgram)) : Prop where
  source : header.function.source = row.function.typedBody
  result : header.function.resultType = row.function.inferredBodyType
  metadata : header.instantiation = CallableNamedCanonicalOrder.retainedInstantiation row
  signatures : header.context.signatures = compiled.sourceProgram.signatures
  ledger : header.context.solvedRequirements = row.function.solvedRequirements
  assumptions : header.context.assumptions = row.assumptions
  evidence : header.function.evidence = CallableNamedMetadata.environment available

theorem header_facts {compiled : SourceCoreUnifiedCompilation.Compiled} {input : Input compiled}
    (packet : CallableIndexedOwnedPreparedFiniteNamedInventories.Issued input)
    {row : SourceSpecialization.SpecializedFunction} (sameRow : input.row = row)
    {available : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    (resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment compiled.sourceProgram row.key row.assumptions = .ok available) :
    HeaderFacts row available packet.header := by
  have extension := packet.header.extended
  rw [packet.function] at extension
  have fields := RecursiveNamedPreparedCallEvidence.Prepared.context_fields input.prepared extension
  have evidence : input.prepared.available = available := by
    have actual := input.prepared.resolved
    have actual : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment compiled.sourceProgram row.key row.assumptions = .ok input.prepared.available :=
      Eq.mp (congrArg (fun r => SourceCompilationPlan.resolveRuntimeEvidenceEnvironment compiled.sourceProgram r.key r.assumptions = .ok input.prepared.available) sameRow) actual
    exact Except.ok.inj (actual.symm.trans resolved)
  refine ⟨?_, ?_, ?_, fields.1, ?_, ?_, ?_⟩
  · rw [packet.function]
    change input.prepared.named.specialized.function.typedBody = row.function.typedBody
    rw [input.prepared.same, sameRow]
  · rw [packet.function]
    change input.prepared.named.specialized.function.inferredBodyType = row.function.inferredBodyType
    rw [input.prepared.same, sameRow]
  · exact packet.aligned.metadata.trans (congrArg _ sameRow)
  · simpa only [sameRow] using fields.2.1
  · simpa only [sameRow] using fields.2.2
  · rw [packet.function]
    change CallableNamedMetadata.environment input.prepared.available = _
    rw [evidence]

def Fixture.shapeAt (fixture : Fixture) {header : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    (facts : HeaderFacts fixture.make.named.specialized fixture.available header) : Shape header.function.source where
  binder := fixture.shape.binder
  read := fixture.shape.read.node
  call := fixture.shape.call.node
  inner := fixture.shape.innerReturn
  lambda := fixture.shape.expression.node
  outer := fixture.shape.statement
  inputs := by rw [facts.source]; exact fixture.shape.inputs
  binderType := fixture.makeBinder
  binderCopied := by rw [facts.source]; exact fixture.makeCopied
  roots := by rw [facts.source]; exact fixture.shape.roots
  readFound := by rw [facts.source]; exact fixture.shape.read.found
  readForm := fixture.shape.read.form
  readRequirements := fixture.shape.read.requirements
  readCoercions := fixture.shape.read.coercions
  innerFound := by rw [facts.source]; exact fixture.shape.innerReturnFound
  innerForm := fixture.shape.innerReturnForm
  lambdaFound := by rw [facts.source]; exact fixture.shape.expression.found
  lambdaForm := fixture.shape.lambda
  lambdaRequirements := fixture.shape.expression.requirements
  lambdaCoercions := fixture.shape.expression.coercions
  outerFound := by rw [facts.source]; exact fixture.shape.statementFound
  outerForm := fixture.shape.statementForm

/-- All semantic selection data are derived before invocation from the actual
checker, selected cache and original evidence actions. -/
theorem Fixture.method_certificate (fixture : Fixture) (issued : Profiled fixture.recipe) :
    ∃ types lexical facts, Dynamic.BodyInstanceTypingCertificate
      (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      (CallableCoercionMethodInstantiation.bodyInstance fixture.recipe.compiled.sourceProgram fixture.method)
      types lexical facts := by
  obtain ⟨receipt⟩ := CallableCoercionSourceSelection.of_accepted fixture.methodSelected
  exact SelectedCompilationRegistryMethodCertificates.of_origin issued.support.bodyTyping fixture.checked
    (SelectedCompilationRegistryMethodCertificates.ranges_of_profile fixture.profile)
    receipt.selected.toSelection fixture.methodMember

def converted (flag : Bool) : Word := if flag then Word.ofNatModulo 41 else Word.ofNatModulo 7

def convertedHeap (flag : Bool) : Dynamic.Heap := appendBool (appendBool (calledHeap flag) flag) flag

/-- Independently execute the call's copy of the snapshot, the original captured
read, generic named call and complete conversion suffix. No staged or completed
native trace is used. -/
theorem Fixture.closure_plain (fixture : Fixture) (issued : Profiled fixture.recipe)
    {makeHeader keepHeader : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    (makeFacts : HeaderFacts fixture.make.named.specialized fixture.available makeHeader)
    (keepFacts : HeaderFacts fixture.keep.named.specialized fixture.dictionary keepHeader)
    {context : SourceSemantics.Context} (invocation : Staging.Recursive.Scope) (flag : Bool)
    (signatures : context.signatures = fixture.recipe.compiled.sourceProgram.signatures)
    (typed : Dynamic.ValueHasType context (capturedHeap flag)
      (.closure (capturedFunction makeHeader (fixture.shapeAt makeFacts))) (.function .unit .word)) :
    Dynamic.CallableApplies (Program.ofChecked fixture.recipe.compiled.sourceProgram) context invocation.evidence
      (capturedFunction makeHeader (fixture.shapeAt makeFacts)).evidence (capturedHeap flag)
      (.closure (capturedFunction makeHeader (fixture.shapeAt makeFacts))) []
      (.word (converted flag)) (convertedHeap flag) := by
  obtain ⟨_parameters, _result, sameSignatures, code, covers, _captures⟩ := typed.closure_function_inv
  have frame : Dynamic.ClosureFrame (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      (capturedFunction makeHeader (fixture.shapeAt makeFacts)) :=
    ⟨sameSignatures.trans signatures, code.owner, code, code.requirement_ledger.idsUnique, covers⟩
  have certified := SelectedCompilationHeaderCertificates.certified issued.support.bodyTyping makeHeader
  have runtime := certified.runtime.transport (RecursiveNamedInitialContextValidity.mono_fields makeHeader.extended)
  have binders : TypeParameterBindersWellFormed makeHeader.context := by
    simp [TypeParameterBindersWellFormed, runtime.closed]
  have metadata : keepHeader.instantiation = fixture.shape.call.instantiation :=
    keepFacts.metadata.trans fixture.target.symm
  have valid : SourceSemantics.DeclarationInstantiation.Valid makeHeader.context fixture.shape.call.instantiation := by
    rw [← metadata]
    have supports := CallableCoercionRawNamedCallAdmission.catalog_supports makeFacts.signatures binders
    cases keepHeader.frame.instantiated with
    | intro _ _ _ _ valid _ _ _ =>
      exact Dynamic.DeclarationInstantiation.Valid.transportContext supports valid
  have produced := CallableCallRequirementLayouts.direct_produces makeFacts.signatures makeFacts.ledger
    (fun goal member => makeFacts.assumptions.symm ▸ member) fixture.resolved fixture.direct fixture.authenticated
  have produced : Dynamic.DirectCallProducesEvidence makeHeader.context makeHeader.function.evidence
      fixture.shape.call.node.requirements fixture.shape.call.node.coercions fixture.shape.call.instantiation.predicates
      keepHeader.function.evidence := by
    rw [makeFacts.evidence, keepFacts.evidence]
    exact produced
  have chosen := SelectedCompilationClosedCoercionSourceSelection.selects
    (CallableMethodBodyCoherence.of_checked fixture.checked) fixture.closed.catalog
    fixture.methodSelected fixture.resolved fixture.materialized makeFacts.signatures makeFacts.ledger
    (fun goal member => makeFacts.assumptions.symm ▸ member)
  have chosen : Dynamic.OperatorMethodSelected (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      makeHeader.context makeHeader.function.evidence "Coerce" "coerce" fixture.shape.call.step.requirements
      (CallableCoercionMethodInstantiation.bodyInstance fixture.recipe.compiled.sourceProgram fixture.method)
      (CallableNamedMetadata.environment fixture.methodDictionary) := by
    rw [makeFacts.evidence]
    exact chosen
  obtain ⟨types, lexical, facts, methodCertificate⟩ := fixture.method_certificate issued
  have methodRuntime := methodCertificate.sourceRuntimeValid.transport
    (RecursiveNamedInitialContextValidity.mono_fields methodCertificate.typing.inputs_extend)
  have ledger : lexical.solvedRequirements = fixture.method.specialized.function.solvedRequirements := by
    exact (RecursiveNamedInitialContextValidity.mono_fields methodCertificate.typing.inputs_extend).solvedRequirements
  have methodCovers : (CallableNamedMetadata.environment fixture.methodDictionary).Covers
      (CallableCoercionMethodInstantiation.bodyInstance fixture.recipe.compiled.sourceProgram fixture.method).context := by
    cases chosen with | intro _ _ _ _ _ _ _ _ _ _ _ _ _ covered => exact covered
  have invoked := method_plain (program := Program.ofChecked fixture.recipe.compiled.sourceProgram) fixture.methodShape rfl methodCertificate.typing.inputs_extend fixture.methodBinder
    ledger methodRuntime.requirements methodCovers (appendBool (calledHeap flag) flag) flag
  have invoked : Dynamic.BodyInvokes (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      (CallableCoercionMethodInstantiation.bodyInstance fixture.recipe.compiled.sourceProgram fixture.method)
      (CallableNamedMetadata.environment fixture.methodDictionary) (appendBool (calledHeap flag) flag) [.bool flag]
      (.word (converted flag)) (convertedHeap flag) := by
    simpa only [fixture.firstValue, fixture.secondValue, converted, convertedHeap] using invoked
  have read : Dynamic.ExpressionEvaluates (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      makeHeader.context makeHeader.function.evidence makeHeader.function.source
      [(fixture.shape.binder.id, ⟨2⟩)] (calledHeap flag) fixture.shape.read.node.id (.bool flag) (calledHeap flag) := by
    rw [makeFacts.source]
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound fixture.shape.read.found)
    · rw [fixture.shape.read.form]
      exact .local (by rw [fixture.shape.read.requirements, fixture.shape.read.coercions]; rfl) .head
        (.intro (.tail (.tail .head))) rfl rfl
    · rw [fixture.shape.read.coercions]; exact .nil
  have called := identity_plain keepHeader fixture.identity keepFacts.source fixture.keepBinder
    (context := makeHeader.context) (evidence := makeHeader.function.evidence) (calledHeap flag) flag
  have expression : Dynamic.ExpressionEvaluates (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      makeHeader.context makeHeader.function.evidence makeHeader.function.source
      [(fixture.shape.binder.id, ⟨2⟩)] (calledHeap flag) fixture.shape.call.node.id
      (.word (converted flag)) (convertedHeap flag) := by
    apply Dynamic.ExpressionEvaluates.intro (by rw [makeFacts.source]; exact lookupExpression?_sound fixture.shape.call.found)
    · rw [fixture.shape.call.form]
      apply Dynamic.ExpressionFormEvaluates.directCall
        (by rw [makeFacts.source]; exact lookupExpression?_sound fixture.shape.call.callee.found)
        fixture.shape.call.calleeForm fixture.shape.call.callee.requirements fixture.shape.call.callee.coercions
        valid (.cons read .nil) produced
      simpa only [metadata] using called
    · rw [fixture.shape.call.coercions]
      exact .cons (.method chosen invoked) .nil
  have executed : Dynamic.FunctionStatementsExecute (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      makeHeader.context makeHeader.function.evidence makeHeader.function.source
      [(fixture.shape.binder.id, ⟨2⟩)] (calledHeap flag) [fixture.shape.innerReturn.id] makeHeader.context
      (.returned (.word (converted flag))) (convertedHeap flag) := by
    exact .singleton (by rw [makeFacts.source]; exact lookupStatement?_sound fixture.shape.innerReturnFound)
      (by rw [fixture.shape.innerReturnForm]; intro id impossible; cases impossible)
      (.returnValue (by rw [makeFacts.source]; exact lookupStatement?_sound fixture.shape.innerReturnFound)
        fixture.shape.innerReturnForm expression)
  have copy : Dynamic.EnvironmentCopies makeHeader.function.source [(fixture.shape.binder.id, ⟨1⟩)]
      (capturedHeap flag) [(fixture.shape.binder.id, ⟨2⟩)] (calledHeap flag) :=
    .copied (fixture.shapeAt makeFacts).binderCopied (.intro (.tail .head)) .append (.nil _)
  exact .closure rfl frame (.nil _) copy (.nil _ _) executed rfl

end Tests.SourceCoreSelectedCoercedDirect
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedCoercedDirectSourceFirst
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreSelectedCoercedDirect
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedFunctionValues (Header)
open SelectedCompilationCertifiedPublicSession (Profiled Initial)
open RecursiveNamedPublicPhysicalSessionState (StartedCall PlainValue SourceCall)
open RecursiveNamedPublicFunctionHistory (Entry)

variable (fixture : Fixture) (issued : Profiled fixture.recipe)
  {keepHeader : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
  (keepFacts : HeaderFacts fixture.keep.named.specialized fixture.dictionary keepHeader)
  {header : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
  (makeFacts : HeaderFacts fixture.make.named.specialized fixture.available header) (flag : Bool)
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}

/-- The actual prior factory result fixes the captured cell. This next-call law
has only a start receipt; the direct call has not executed yet. -/
theorem direct_from_captured (keepFacts : HeaderFacts fixture.keep.named.specialized fixture.dictionary keepHeader) (entry : Entry)
    (state : issued.toIssued.State header session [entry])
    (heap : state.heap = capturedHeap flag)
    (source : entry.source = .closure (capturedFunction header (fixture.shapeAt makeFacts)))
    (entryType : entry.sourceType = .function .unit .word)
    (handleType : entry.handle.sourceType = .function .unit .word)
    (ready : session.ExportsReady)
    {fuel : Nat} {checkpoint : SourceCoreExecution.Checkpoint artifact}
    (started : session.startHandlePacked entry.handle .unit fuel = .ok checkpoint)
    (invocation : Staging.Recursive.Scope) :
    Dynamic.CallableApplies (Program.ofChecked fixture.recipe.compiled.sourceProgram) header.function.context
      invocation.evidence (Staging.Recursive.callableEvidence entry.source)
      state.heap entry.source [] (.word (converted flag)) (convertedHeap flag) ∧
    ((Staging.Recursive.Applies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
        (SelectedCompilationPhysicalProgramSupport.stages fixture.recipe.compiled) invocation
        header.function.context state.heap entry.source [] (.value (.word (converted flag))) (convertedHeap flag) ∧
      SelectedCompilationPublicSessionDirectScalarForward.ForwardAt issued.catalog.rows header issued.initial
        issued.support.profile fixture.recipe [entry] (.word (converted flag)) checkpoint (convertedHeap flag)) ∨
      SelectedCompilationStageClosedDirectForward.StageStopped issued state entry checkpoint invocation []) := by
  have typed := (state.history.semantic.current.2.2.2.2 entry (List.mem_singleton_self _)).2.2
  rw [entryType, source, heap] at typed
  have plain := fixture.closure_plain issued makeFacts keepFacts invocation flag
    (SelectedCompilationPublicHistorySourceInputs.header_runtime issued.support.bodyTyping header).signatures typed
  have ordinary : Dynamic.CallableApplies (Program.ofChecked fixture.recipe.compiled.sourceProgram) header.function.context
      invocation.evidence (Staging.Recursive.callableEvidence entry.source)
      state.heap entry.source [] (.word (converted flag)) (convertedHeap flag) := by
    simpa only [source, heap, Staging.Recursive.callableEvidence] using plain
  have input : RecursiveNamedPublicFunctionHistoryInputs.Input [entry] header.function.context
      .unit .unit .unit := .data ⟨.unit, by simp [SourceCoreIndexedSession.DataInput.publicValue], .unit⟩ ⟨.unit, by simp [SourceCoreIndexedSession.DataInput.publicValue], .unit⟩
  exact ⟨ordinary, SelectedCompilationStageClosedDirectForward.scalar issued state entry
    (List.mem_singleton_self _) entryType input started ready .nil (.word (converted flag)) rfl handleType ordinary⟩

variable {key : SourceCoreIndexedSession.Key} {options : SourceCoreExecution.RunOptions}
  (call : StartedCall session key [.bool flag] options) (initial : Initial issued.toIssued call)

/-- Factory and direct invocation are related before either public execution is
observed. All sufficiently fueled factory completions expose the exact closure. -/
def ForwardChain (makeFacts : HeaderFacts fixture.make.named.specialized fixture.available initial.header) (invocation : Staging.Recursive.Scope) : Prop :=
  ∃ requiredExecution requiredOutput,
    ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome artifact),
      requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
      call.checkpoint.ResumeAt executionFuel outputFuel outcome →
      ∃ completion : SourceCoreExecution.Completion artifact,
        outcome = .succeeded completion ∧
        ∃ (entry : Entry) (state : issued.toIssued.State initial.header completion.session [entry]),
          completion.value = .function entry.handle ∧ state.heap = capturedHeap flag ∧
          entry.source = .closure (capturedFunction initial.header (fixture.shapeAt makeFacts)) ∧
          ∀ fuel (checkpoint : SourceCoreExecution.Checkpoint artifact),
            completion.session.startHandlePacked entry.handle .unit fuel = .ok checkpoint →
            Dynamic.CallableApplies (Program.ofChecked fixture.recipe.compiled.sourceProgram) initial.header.function.context
              invocation.evidence (Staging.Recursive.callableEvidence entry.source)
              state.heap entry.source [] (.word (converted flag)) (convertedHeap flag) ∧
            ((Staging.Recursive.Applies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
                (SelectedCompilationPhysicalProgramSupport.stages fixture.recipe.compiled) invocation
                initial.header.function.context state.heap entry.source [] (.value (.word (converted flag))) (convertedHeap flag) ∧
              SelectedCompilationPublicSessionDirectScalarForward.ForwardAt issued.catalog.rows initial.header
                issued.initial issued.support.profile fixture.recipe [entry] (.word (converted flag)) checkpoint (convertedHeap flag)) ∨
              SelectedCompilationStageClosedDirectForward.StageStopped issued state entry checkpoint invocation [])

/-- The lambda captures the original parameter allocation, and the subsequent
ordinary read drives the closed direct public theorem. -/
theorem initial_source_first (keepFacts : HeaderFacts fixture.keep.named.specialized fixture.dictionary keepHeader) (makeFacts : HeaderFacts fixture.make.named.specialized fixture.available initial.header)
    (resultType : initial.header.function.resultType = .function .unit .word)
    (invocation : Staging.Recursive.Scope) :
    PlainValue initial.header initial.header invocation ⟨[]⟩ [.bool flag]
      (.closure (capturedFunction initial.header (fixture.shapeAt makeFacts))) (capturedHeap flag) ∧
    (ForwardChain fixture issued flag call initial makeFacts invocation ∨
      SelectedCompilationStageClosedInitialForward.StageStopped issued call initial invocation [.bool flag]) := by
  obtain ⟨rawD, global, sourceAt⟩ :=
    (CallableIndexedOwnedPreparedFiniteNamedInventories.source_receipts issued.catalog.rows).receipts
      initial.header initial.start.selected.member
  have plain := factory_plain initial.header (fixture.shapeAt makeFacts) sourceAt invocation flag
  have simple : ∀ value ∈ ([.bool flag] : List SourceCorePublicValues.Value),
      SourceCoreIndexedSession.SimplePublic value := by
    intro value member
    cases List.mem_singleton.mp member
    exact .bool _
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes initial.header.function.context
      [.bool flag] initial.header.types := by
    rw [input_types initial.header (fixture.shapeAt makeFacts)]
    exact .cons ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩ .nil
  have meanings : RecursiveNamedPublicDataInputs.Meanings [.bool flag] [.bool flag] :=
    .cons ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩ .nil
  have forward := SelectedCompilationStageClosedInitialForward.function issued call initial simple inputTypes meanings
    (by rw [resultType]; rfl) plain
  refine ⟨plain, ?_⟩
  rcases forward with ⟨_source, requiredExecution, requiredOutput, forward⟩ | stopped
  · left
    refine ⟨requiredExecution, requiredOutput, ?_⟩
    intro executionFuel outputFuel outcome executionBound outputBound resumed
    obtain ⟨completion, actual, ready, entry, entryType, source, returned, handleType, state, heap⟩ :=
      forward executionFuel outputFuel outcome executionBound outputBound resumed
    rw [resultType] at entryType handleType
    refine ⟨completion, actual, entry, state, returned, heap, source, ?_⟩
    intro fuel checkpoint accepted
    exact direct_from_captured fixture issued makeFacts flag (keepFacts := keepFacts) entry state heap source entryType handleType ready accepted invocation
  · exact .inr stopped

/-- The same independent factory trace also determines the whole exported value
and its ordered collection of callable leaves. -/
theorem initial_whole_output (makeFacts : HeaderFacts fixture.make.named.specialized fixture.available initial.header)
    (invocation : Staging.Recursive.Scope) :
    (SourceCall initial.header initial.header invocation ⟨[]⟩ [.bool flag]
        (.value (.closure (capturedFunction initial.header (fixture.shapeAt makeFacts)))) (capturedHeap flag) ∧
      SelectedCompilationStageClosedDirectForward.Output.ForwardAt issued.catalog.rows initial.header
        issued.initial issued.support.profile fixture.recipe [] initial.header.function.resultType call.checkpoint
        (.closure (capturedFunction initial.header (fixture.shapeAt makeFacts))) (capturedHeap flag)) ∨
    SelectedCompilationStageClosedInitialForward.StageStopped issued call initial invocation [.bool flag] := by
  obtain ⟨rawD, global, sourceAt⟩ :=
    (CallableIndexedOwnedPreparedFiniteNamedInventories.source_receipts issued.catalog.rows).receipts
      initial.header initial.start.selected.member
  have plain := factory_plain initial.header (fixture.shapeAt makeFacts) sourceAt invocation flag
  have simple : ∀ value ∈ ([.bool flag] : List SourceCorePublicValues.Value),
      SourceCoreIndexedSession.SimplePublic value := by
    intro value member
    cases List.mem_singleton.mp member
    exact .bool _
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes initial.header.function.context
      [.bool flag] initial.header.types := by
    rw [input_types initial.header (fixture.shapeAt makeFacts)]
    exact .cons ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩ .nil
  have meanings : RecursiveNamedPublicDataInputs.Meanings [.bool flag] [.bool flag] :=
    .cons ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩ .nil
  exact SelectedCompilationStageClosedOutputForward.initial issued call initial simple inputTypes meanings plain

end Tests.SourceCoreSelectedCoercedDirect
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedCoercedDirectPublic
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
namespace Tests.SourceCoreSelectedCoercedDirect
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open SelectedCompilationCertifiedPublicSession (Profiled Initial)
open RecursiveNamedPublicPhysicalSessionState (StartedCall PlainValue SourceCall)

def runOptions : SourceCoreExecution.RunOptions := {executionFuel := 300000, outputValidationFuel := 2048}

structure Started (fixture : Fixture) (flag : Bool) where
  artifact : SourceCoreExecution.Artifact
  opened : artifact.CompiledAt fixture.facade
  bootstrap : SourceCoreExecution.Bootstrap artifact
  fresh : bootstrap.FreshAt
  authority : bootstrap.ExportAuthorityAt
  session : SourceCoreExecution.Session artifact
  ready : bootstrap.resume 100000 = .ready session
  call : StartedCall session fixture.make.named.signature.key [.bool flag] runOptions

def observeStarted (fixture : Fixture) (flag : Bool) : IO (Started fixture flag) := do
  let opened ← fixture.facade.openWithReceipt
  let bootstrap ← opened.val.bootstrapWithExportReceipt
  match ready : bootstrap.val.resume 100000 with
  | .error error => throw (IO.userError (reprStr error))
  | .outOfFuel _ => throw (IO.userError "coerced bootstrap exhausted")
  | .ready session =>
    match started : session.start fixture.make.named.signature.key [.bool flag] runOptions.inputValidationFuel with
    | .error error => throw (IO.userError (reprStr error))
    | .ok checkpoint => return ⟨opened.val, opened.property, bootstrap.val, bootstrap.property.1,
        bootstrap.property.2, session, ready, checkpoint, started⟩

/-- Automatic issuance supplies the real factory and generic callee headers.
Both ordinary traces are constructed before either target call is resumed. -/
theorem from_source (fixture : Fixture) (flag : Bool) (started : Started fixture flag) :
    ∃ (issued : Profiled fixture.recipe) (initial : Initial issued.toIssued started.call)
      (makeFacts : HeaderFacts fixture.make.named.specialized fixture.available initial.header),
      ∀ invocation, PlainValue initial.header initial.header invocation ⟨[]⟩ [.bool flag]
        (.closure (capturedFunction initial.header (fixture.shapeAt makeFacts))) (capturedHeap flag) ∧
        (ForwardChain fixture issued flag started.call initial makeFacts invocation ∨
          SelectedCompilationStageClosedInitialForward.StageStopped issued started.call initial invocation [.bool flag]) ∧
        ((SourceCall initial.header initial.header invocation ⟨[]⟩ [.bool flag]
            (.value (.closure (capturedFunction initial.header (fixture.shapeAt makeFacts)))) (capturedHeap flag) ∧
          SelectedCompilationStageClosedDirectForward.Output.ForwardAt issued.catalog.rows initial.header
            issued.initial issued.support.profile fixture.recipe [] initial.header.function.resultType started.call.checkpoint
            (.closure (capturedFunction initial.header (fixture.shapeAt makeFacts))) (capturedHeap flag)) ∨
          SelectedCompilationStageClosedInitialForward.StageStopped issued started.call initial invocation [.bool flag]) := by
  let row : SelectedCompilationCertifiedPublicSession.EligibleRow fixture.recipe.compiled
      fixture.make.named.signature.key :=
    ⟨fixture.make.named, fixture.make.index, fixture.make.named.signature, fixture.make.cached,
      CallableIndexedOwnedPreparedOrdinaryCachedInputs.cached_slot _ fixture.make.cached, rfl, fixture.make.eligible⟩
  obtain ⟨issued, initial, namedEq⟩ := SelectedCompilationCertifiedPublicSession.from_checked_profiled_initial_row
    fixture.checked fixture.accepted fixture.selected fixture.profile started.opened started.call
    started.bootstrap started.fresh started.authority (.single started.ready) row
  obtain ⟨input, packet, _retained, sameHeader⟩ := issued.catalog.rows.mem_headers initial.header initial.start.selected.member
  have sameRow : input.row = fixture.make.named.specialized :=
    input.prepared.same.symm.trans (congrArg (·.specialized)
      (packet.aligned.named.symm.trans ((congrArg (·.named) sameHeader).trans namedEq)))
  have makeFacts : HeaderFacts fixture.make.named.specialized fixture.available initial.header :=
    sameHeader ▸ header_facts packet sameRow fixture.resolved
  obtain ⟨keepInput, keepPacket, _keepRetained, keepRow, _slot, _same⟩ :=
    issued.catalog.packet_at fixture.keep.cached fixture.keep.eligible
  have keepFacts := header_facts keepPacket keepRow fixture.keepResolved
  have resultType := makeFacts.result.trans fixture.makeResult
  refine ⟨issued, initial, makeFacts, ?_⟩
  intro invocation
  have first := initial_source_first fixture issued flag started.call initial (keepFacts := keepFacts) makeFacts resultType invocation
  exact ⟨first.1, first.2, initial_whole_output fixture issued flag started.call initial makeFacts invocation⟩

end Tests.SourceCoreSelectedCoercedDirect
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedCoercedDirectRuntime
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedCoercedDirect
open Solcore Frontend SourceInference SourceSemantics CoreLowering

private def require (condition : Bool) (message : String) : IO Unit :=
  if condition then pure () else throw (IO.userError message)

private def branch (fixture : Fixture) (flag : Bool) : IO Unit := do
  let started ← observeStarted fixture flag
  have _sourceFirst := from_source fixture flag started
  let .outOfFuel factorySuspended ← started.call.checkpoint.resume 0 0
    | throw (IO.userError "coerced factory did not suspend at zero fuel")
  let .succeeded factory ← factorySuspended.resume 300000 2048
    | throw (IO.userError "coerced factory did not complete")
  let .function handle := factory.value
    | throw (IO.userError "coerced factory did not return its closure handle")
  require (handle.sourceType == .function .unit .word) "coerced handle type changed"
  let .ok checkpoint := factory.session.startHandlePacked handle .unit runOptions.inputValidationFuel
    | throw (IO.userError "coerced direct call did not start")
  let .outOfFuel suspended ← checkpoint.resume 0 0
    | throw (IO.userError "coerced direct call did not suspend at zero fuel")
  let .succeeded first ← suspended.resume 300000 2048
    | throw (IO.userError "coerced direct call did not complete")
  require (first.value == .word (converted flag)) "coerced Source read changed"
  let .ok repeatedCheckpoint := first.session.startHandlePacked handle .unit runOptions.inputValidationFuel
    | throw (IO.userError "coerced handle was not retained after the direct call")
  let .succeeded repeated ← repeatedCheckpoint.resume 300000 2048
    | throw (IO.userError "retained coerced call did not complete")
  require (repeated.value == .word (converted flag)) "retained coerced Source read changed"
  require ([started.session.heapSize, factory.session.heapSize, first.session.heapSize, repeated.session.heapSize]
    == [5, 11, 20, 29]) "coerced exact heap sizes changed"
  require (fixture.recipe.compiled.indexed.base.functions.length == 4) "coerced cache changed"
  IO.println s!"SOURCE_FIRST_COERCED_BRANCH_PASS: flag={flag}; result={converted flag}; heaps{[started.session.heapSize, factory.session.heapSize, first.session.heapSize, repeated.session.heapSize]}"

def run : IO Unit := do
  let fixture ← fixture
  branch fixture true
  branch fixture false
  IO.println "SOURCE_FIRST_COERCED_PROFILE_PASS: unchanged checked1024/compiled1000 original four-row program; automatic same-profile issuance; independent captured Bool/Mark dictionary/keep/Coerce traces; closed initial function and full output, direct scalar; both 41/7 branches, zero-fuel resumes and retained handle reuse"

end Tests.SourceCoreSelectedCoercedDirect
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedGeneralizedLocalFixture
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedGeneralizedLocal
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering

private def observed (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
  if witness : p then pure ⟨witness⟩ else throw (IO.userError message)

structure CompiledFixture where
  recipe : SourceCoreIndexedSession.Recipe
  checked : checkProgram workspace options.checkingFuel = .ok recipe.compiled.sourceProgram
  seeds : List SourceCompiler.Seed
  facade : SourceCoreExecution.Compiled
  accepted : SourceCompiler.compileChecked recipe.compiled.sourceProgram seeds options = .ok facade
  selected : RecursiveNamedPreparedStageContracts.PublicRecipe facade recipe

def compileFixture : IO CompiledFixture := do
  match checked : checkProgram workspace options.checkingFuel with
  | .error errors => throw (IO.userError (reprStr errors))
  | .ok program =>
    let seeds := program.signatures.functions.map (fun signature => SourceCompiler.Seed.declaration signature.id)
    match generated : SourceCoreCompiler.compileChecked program seeds options with
    | .error error => throw (IO.userError (reprStr error))
    | .ok source =>
      match present : source.artifact? with
      | none => throw (IO.userError "generalized local artifact absent")
      | some cached =>
        match prepared : SourceCoreIndexedSession.Recipe.prepare cached with
        | .error error => throw (IO.userError (reprStr error))
        | .ok recipe =>
          match facade : SourceCoreExecution.prepare source with
          | .error error => throw (IO.userError (reprStr error))
          | .ok publicCompiled =>
            have sameProgram : recipe.compiled.sourceProgram = program :=
              (congrArg (·.sourceProgram) (SourceCoreIndexedSession.Recipe.prepare_compiled prepared)).trans
                ((source.artifact_fields present).1.trans (SourceCoreCompiler.compileChecked_program generated))
            return {
              recipe := recipe
              checked := by rw [sameProgram]; exact checked
              seeds := seeds
              facade := publicCompiled
              accepted := by
                rw [sameProgram]
                simpa only [SourceCoreExecution.compileChecked, generated, Except.mapError, bind, Except.bind] using facade
              selected := RecursiveNamedPreparedStageContracts.public_preparation present prepared facade }


structure Row (fixture : CompiledFixture) where
  original : SourceSpecialization.SpecializedFunction
  member : original ∈ fixture.recipe.compiled.validationPlan.specializations
  global : SourceCoreCalls.Signature
  index : Nat
  slot : CallableNamedMetadata.Slot fixture.recipe.compiled.indexed.base.globals index global
  globalKey : global.key = original.key
  substitution : original.parameterSubstitution = []
  ordinary : original.function.returnComptime = false
  ordinaryInputs : ∀ binder ∈ original.function.typedBody.inputs, binder.comptime = false

def observeRow (fixture : CompiledFixture) (name : String) : IO (Row fixture) := do
  let some signature := fixture.recipe.compiled.sourceProgram.signatures.functions.find? (fun signature => signature.name == name)
    | throw (IO.userError "generalized local original signature")
  match found : fixture.recipe.compiled.validationPlan.specializations.find?
      (fun row => decide (row.function.typedBody.owner = signature.id)) with
  | none => throw (IO.userError "generalized local original row")
  | some original =>
    match slot : fixture.recipe.compiled.indexed.base.globals.zipIdx.filter
        (fun pair => decide (pair.1.key = original.key)) with
    | [(global, index)] =>
      let ⟨globalKey⟩ ← observed (global.key = original.key) "generalized local global key"
      let ⟨substitution⟩ ← observed (original.parameterSubstitution = []) "generalized local substitution"
      let ⟨ordinary⟩ ← observed (original.function.returnComptime = false) "generalized local ordinary return"
      let ⟨ordinaryInputs⟩ ← observed (original.function.typedBody.inputs.all (fun binder => !binder.comptime) = true) "generalized local ordinary parameters"
      return {
        original := original
        member := List.mem_of_find?_eq_some found
        global := global
        index := index
        slot := by unfold CallableNamedMetadata.Slot; rw [globalKey]; exact slot
        globalKey := globalKey
        substitution := substitution
        ordinary := ordinary
        ordinaryInputs := by
          intro binder member
          have selected := List.all_eq_true.mp ordinaryInputs binder member
          cases marker : binder.comptime <;> simp_all }
    | _ => throw (IO.userError "generalized local unique physical slot")

def observeCall (source : TypedSource) (binder : TypedBinder) (argument : ExpressionId)
    (type : TypeSystem.Ty) (callee node : ExpressionNode) : IO (CallShape source binder argument type) := do
  let read ← Tests.SourceCoreNamedBranch.observeRead source binder callee (.function type type)
  let .call _ _ (.indirect metadata) := node.form | throw (IO.userError "generalized original indirect call")
  let ⟨found⟩ ← observed (source.lookupExpression? node.id = some node) "generalized call identity"
  let ⟨form⟩ ← observed (node.form = .call read.node.id [argument] (.indirect metadata)) "generalized call order"
  let ⟨arity⟩ ← observed (metadata.argumentCount = 1) "generalized original arity"
  let ⟨argumentCoercions⟩ ← observed (metadata.argumentCoercions = []) "generalized argument coercions"
  let ⟨requirements⟩ ← observed (node.requirements = []) "generalized call requirements"
  let ⟨coercions⟩ ← observed (node.coercions = []) "generalized call coercions"
  return ⟨read,node,metadata,found,form,arity,argumentCoercions,requirements,coercions⟩

def observeShape (source : TypedSource) : IO (Shape source) := do
  let [flag] := source.inputs | throw (IO.userError "generalized input")
  let [.expression parameterNode,.statement identityReturn,.expression lambda,.statement initialized,
       .expression literalNode,.expression wordCallee,.expression first,
       .expression flagNode,.expression boolCallee,.expression second,
       .expression tuple,.statement returned] := source.nodes
    | throw (IO.userError "generalized original graph")
  let .letDecl binder _ := initialized.form | throw (IO.userError "generalized original binder")
  let .lambda [parameter] (.variable typeVariable) _ := lambda.form
    | throw (IO.userError "generalized principal lambda")
  let parameterRead ← Tests.SourceCoreNamedBranch.observeRead source parameter parameterNode (.variable typeVariable)
  let flagRead ← Tests.SourceCoreNamedBranch.observeRead source flag flagNode .bool
  let .integerLiteral raw resolution := literalNode.form | throw (IO.userError "generalized original literal")
  let ⟨literalFound⟩ ← observed (source.lookupExpression? literalNode.id = some literalNode) "generalized literal identity"
  let ⟨literalForm⟩ ← observed (literalNode.form = .integerLiteral raw resolution) "generalized literal form"
  let ⟨literalTarget⟩ ← observed (resolution.targetType = .word) "generalized literal Word"
  let ⟨literalRequirements⟩ ← observed (literalNode.requirements = [resolution.requirement]) "generalized literal requirements"
  let ⟨literalCoercions⟩ ← observed (literalNode.coercions = []) "generalized literal coercions"
  let literal : WordNode source :=
    ⟨literalNode,raw,resolution,literalFound,literalForm,literalTarget,literalRequirements,literalCoercions⟩
  let wordCall ← observeCall source binder literalNode.id .word wordCallee first
  let boolCall ← observeCall source binder flagRead.node.id .bool boolCallee second
  let ⟨inputs⟩ ← observed (source.inputs = [flag]) "generalized original inputs"
  let ⟨flagScheme⟩ ← observed (flag.scheme = .mono .bool) "generalized Bool input"
  let ⟨scheme⟩ ← observed (binder.scheme = ⟨[typeVariable], .function (.variable typeVariable) (.variable typeVariable)⟩) "generalized principal scheme"
  let ⟨schemeRequirements⟩ ← observed (binder.schemeRequirements = []) "generalized principal requirements"
  let ⟨parameterScheme⟩ ← observed (parameter.scheme = .mono (.variable typeVariable)) "generalized principal parameter"
  let ⟨parameterRequirements⟩ ← observed (parameter.schemeRequirements = []) "generalized parameter requirements"
  let ⟨roots⟩ ← observed (source.roots = [.statement initialized.id,.statement returned.id]) "generalized original root order"
  let ⟨initializedFound⟩ ← observed (source.lookupStatement? initialized.id = some initialized) "generalized let identity"
  let ⟨initializedForm⟩ ← observed (initialized.form = .letDecl binder (some lambda.id)) "generalized let initializer"
  let ⟨lambdaFound⟩ ← observed (source.lookupExpression? lambda.id = some lambda) "generalized lambda identity"
  let ⟨lambdaForm⟩ ← observed (lambda.form = .lambda [parameter] (.variable typeVariable) [identityReturn.id]) "generalized original lambda body"
  let ⟨lambdaRaw⟩ ← observed (lambda.rawType = binder.scheme.body) "generalized principal raw type"
  let ⟨lambdaType⟩ ← observed (lambda.type = binder.scheme.body) "generalized principal result type"
  let ⟨lambdaRequirements⟩ ← observed (lambda.requirements = []) "generalized initializer requirements"
  let ⟨lambdaCoercions⟩ ← observed (lambda.coercions = []) "generalized initializer coercions"
  let ⟨identityFound⟩ ← observed (source.lookupStatement? identityReturn.id = some identityReturn) "generalized identity return lookup"
  let ⟨identityForm⟩ ← observed (identityReturn.form = .returnStmt (some parameterRead.node.id)) "generalized identity return form"
  let ⟨literalValue⟩ ← observed (literal.resolution.rawValue = 11) "generalized original literal value"
  let ⟨tupleFound⟩ ← observed (source.lookupExpression? tuple.id = some tuple) "generalized tuple lookup"
  let ⟨tupleForm⟩ ← observed (tuple.form = .tuple [wordCall.node.id,boolCall.node.id]) "generalized ordered calls"
  let ⟨tupleRequirements⟩ ← observed (tuple.requirements = []) "generalized tuple requirements"
  let ⟨tupleCoercions⟩ ← observed (tuple.coercions = []) "generalized tuple coercions"
  let ⟨returnedFound⟩ ← observed (source.lookupStatement? returned.id = some returned) "generalized outer return lookup"
  let ⟨returnedForm⟩ ← observed (returned.form = .returnStmt (some tuple.id)) "generalized outer return form"
  return ⟨flag,binder,parameter,typeVariable,initialized,lambda,identityReturn,parameterRead,literal,flagRead,
    wordCall,boolCall,tuple,returned,inputs,flagScheme,scheme,schemeRequirements,parameterScheme,
    parameterRequirements,roots,initializedFound,initializedForm,lambdaFound,lambdaForm,lambdaRaw,
    lambdaType,lambdaRequirements,lambdaCoercions,identityFound,identityForm,literalValue,
    tupleFound,tupleForm,tupleRequirements,tupleCoercions,returnedFound,returnedForm⟩

/-- Runtime observation only. The separate Source proofs do not use these
completed target executions as premises. -/
def probe : IO Unit := do
  let fixture ← compileFixture
  let row ← observeRow fixture "local"
  let _shape ← observeShape row.original.function.typedBody
  unless fixture.recipe.compiled.sourceProgram.functions.length == 1 &&
      fixture.recipe.compiled.indexed.base.functions.length == 1 do
    throw (IO.userError "generalized complete original cache changed")
  let artifact ← fixture.facade.open
  let session ← Tests.SourceCompilerFeatureSupport.boot artifact
  let mut current := session
  let mut heaps := [current.heapSize]
  for flag in [true,false,true] do
    match ← current.run row.original.key [.bool flag] runOptions with
    | .ok (.succeeded returned) =>
      unless returned.value == .product (.word (Word.ofNatModulo 11)) (.bool flag) do
        throw (IO.userError "generalized original result changed")
      current := returned.session
      heaps := heaps ++ [current.heapSize]
    | _ => throw (IO.userError "generalized original runtime failed")
  IO.println s!"GENERALIZED_LOCAL_ORIGINAL_CACHE: originals1/cache1"
  IO.println s!"GENERALIZED_LOCAL_NATIVE_HEAPS: {heaps}"
  IO.println "GENERALIZED_LOCAL_RUNTIME_PROBE_PASS"

end Tests.SourceCoreSelectedGeneralizedLocal
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedGeneralizedLocalProgramProfile
/-! The unchanged original program retains a profile for every actual cached
named row. This packet certifies compiler syntax and preparation; original
declarative program typing remains a separate proof obligation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedGeneralizedLocal
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering

structure ProfiledFixture where
  original : CompiledFixture
  originals : original.recipe.compiled.sourceProgram.functions.length = 1
  cached : original.recipe.compiled.indexed.base.functions.length = 1
  profiles : CellAwareNamedProgramProfiles.Profile original.recipe.compiled.indexed

def compileProfiledFixture : IO ProfiledFixture := do
  let original ← compileFixture
  if originals : original.recipe.compiled.sourceProgram.functions.length = 1 then
    if cached : original.recipe.compiled.indexed.base.functions.length = 1 then
      match CellAwareNamedProgramProfiles.profile? original.recipe.compiled.indexed with
      | none => throw (IO.userError "original generalized program profile rejected")
      | some profiles => pure ⟨original, originals, cached, profiles⟩
    else throw (IO.userError "original generalized full cache changed")
  else throw (IO.userError "original generalized source count changed")

theorem ProfiledFixture.ready (fixture : ProfiledFixture) :
    SourceCoreIndexedSession.Recipe.prepare fixture.original.recipe.compiled = .ok fixture.original.recipe := by
  obtain ⟨_, _, _, ready⟩ := RecursiveNamedPreparedStageContracts.public_compilation
    fixture.original.accepted fixture.original.selected
  exact ready

theorem ProfiledFixture.body (fixture : ProfiledFixture)
    {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared fixture.original.recipe.compiled row)
    {instantiation : DeclarationInstantiation}
    {header : CallableIndexedOwnedFunctionValues.Header fixture.original.recipe.compiled
      (Program.ofChecked fixture.original.recipe.compiled.sourceProgram)}
    (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
    (wellFormed : ProgramWellFormed (Program.ofChecked fixture.original.recipe.compiled.sourceProgram))
    {entry : SourceCoreCallableIndexedPrograms.Entry fixture.original.recipe.compiled.indexed.layouts}
    (member : entry ∈ fixture.original.recipe.compiled.indexed.entries) :
    Nonempty (CellAwareNamedBodySupport.Body prepared.compilation
      (CellAwareNamedBodyProducer.Certificate prepared.compilation)
      (RecursiveNamedLambdaFormationHeads.nativePrefix
        (values := .initial fixture.original.recipe.compiled.compatible.checked) header)
      header.context header.function.resultType) := by
  obtain ⟨profile⟩ := fixture.profiles.at_slot prepared.selected
  exact CellAwareNamedBodyReceipt.of_header prepared aligned fixture.ready wellFormed member
    (profile.for_compilation prepared.compilation)

def checkProgramProfile : IO Unit := do
  let _fixture ← compileProfiledFixture
  IO.println "GENERALIZED_LOCAL_COMPLETE_STATIC_INVENTORY: originals1/cache1/profile1"

end Tests.SourceCoreSelectedGeneralizedLocal
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedGeneralizedLocalInventory
/-! The actual original row supplies the complete one-position named inventory.
Its selected compiler packet is retained through public root selection; no
other cached row is removed or replaced by a body execution assumption. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedGeneralizedLocal
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Issued Inventory headers)

structure SelectedInventory (fixture : ProfiledFixture) (row : Row fixture.original) where
  input : Input fixture.original.recipe.compiled
  original : input.row = row.original
  packet : Issued input
  position : input.prepared.index = 0
  complete : fixture.original.recipe.compiled.indexed.base.functions = [input.prepared.named]

def SelectedInventory.rows {fixture : ProfiledFixture} {row : Row fixture.original}
    (selected : SelectedInventory fixture row) : Inventory [selected.input] :=
  .cons selected.packet .nil

theorem SelectedInventory.distinct {fixture : ProfiledFixture} {row : Row fixture.original}
    (selected : SelectedInventory fixture row) :
    ([selected.input].map (fun input => input.prepared.index)).Nodup := by
  simp

theorem ProfiledFixture.inventory (fixture : ProfiledFixture) (row : Row fixture.original)
    (wellFormed : ProgramWellFormed (Program.ofChecked fixture.original.recipe.compiled.sourceProgram)) :
    Nonempty (SelectedInventory fixture row) := by
  obtain ⟨prepared⟩ := RecursiveNamedPublicSpecializationMeaning.of_public_compile
    fixture.original.accepted fixture.original.selected row.member
  have range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures fixture.original.recipe.compiled.sourceProgram.signatures)
      row.original.parameterSubstitution := by
    rw [row.substitution]
    intro name value found
    cases found
  let input : Input fixture.original.recipe.compiled := {
    row := row.original
    prepared := prepared
    range := range
    ordinaryReturn := row.ordinary
    ordinaryParameters := fun binder member => row.ordinaryInputs binder member
    target := by
      have target := SelectedCompilationCatalog.retained_target fixture.original.recipe.compiled
        wellFormed.signatures prepared.selected (prepared.same.symm ▸ prepared.origin)
      simpa only [prepared.same] using target
    slot := CallableIndexedOwnedPreparedOrdinaryCachedInputs.cached_slot
      fixture.original.recipe.compiled prepared.selected }
  obtain ⟨packet⟩ := CallableIndexedOwnedPreparedFiniteNamedInventories.issue wellFormed input
  have bound := (List.getElem?_eq_some_iff.mp prepared.selected).1
  rw [fixture.cached] at bound
  have position : prepared.index = 0 := by omega
  obtain ⟨named, complete⟩ := List.length_eq_one_iff.mp fixture.cached
  have selected := prepared.selected
  rw [complete, position] at selected
  have same : named = prepared.named := Option.some.inj selected
  exact ⟨⟨input, rfl, packet, position, by simpa only [same] using complete⟩⟩

theorem SelectedInventory.root_selection {fixture : ProfiledFixture} {row : Row fixture.original}
    (selected : SelectedInventory fixture row)
    {root : SourceCoreIndexedSession.Root fixture.original.recipe.compiled}
    (member : root ∈ fixture.original.recipe.roots) :
    RecursiveNamedPublicRootMeaning.RootSelection
      (values := .initial fixture.original.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.original.recipe.compiled.indexed)
      (program := Program.ofChecked fixture.original.recipe.compiled.sourceProgram)
      (headers selected.rows) root selected.packet.header := by
  obtain ⟨entry, present, shape⟩ := SourceCoreIndexedSession.Recipe.prepare_roots fixture.ready member
  obtain ⟨named, index, found, rest⟩ := shape
  have atIndex : fixture.original.recipe.compiled.indexed.base.functions[index]? = some named :=
    List.mk_mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some found)
  have bound := (List.getElem?_eq_some_iff.mp atIndex).1
  rw [fixture.cached] at bound
  have indexEq : index = 0 := by omega
  have sourceSelected := selected.input.prepared.selected
  rw [selected.position] at sourceSelected
  rw [indexEq] at atIndex
  have same : selected.input.prepared.named = named := Option.some.inj (sourceSelected.symm.trans atIndex)
  refine ⟨by exact List.mem_cons_self, entry, present, ⟨named, index, found, rest⟩, ?_⟩
  rw [selected.packet.aligned.named, selected.packet.aligned.slot]
  change _ = some (selected.input.prepared.named, selected.input.prepared.index)
  simpa only [selected.position, same, indexEq] using found

theorem SelectedInventory.header_original {fixture : ProfiledFixture} {row : Row fixture.original}
    (selected : SelectedInventory fixture row) :
    selected.packet.header.named.specialized = row.original :=
  (congrArg (·.specialized) selected.packet.aligned.named).trans
    (selected.input.prepared.same.trans selected.original)

end Tests.SourceCoreSelectedGeneralizedLocal
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedGeneralizedLocalTrace
/-! Independent Source execution of the original identity body after a genuine
local-scheme instance has been selected. No target execution is a premise.
Closures capture by value: the generalized `let` copies the function's
environment once, and each instance call copies the descriptor's captures
again before allocating its parameter. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedGeneralizedLocal
open Solcore Frontend SourceInference SourceSemantics
open Tests.SourceSemanticsCaptureCopies

/-- The exact materialized body copies the descriptor's captures, reads its
newly allocated parameter and returns it. The supplied frame is static Source
code/evidence validity. -/
theorem Shape.identity_applies {source : TypedSource} (shape : Shape source)
    {program : SourceSemantics.Program} {definitionContext context : SourceSemantics.Context}
    (captured : Dynamic.Environment) (substitution : TypeSystem.Substitution)
    (evidence callerEvidence : Dynamic.EvidenceEnvironment)
    (before : Dynamic.Heap) (argument : Dynamic.Value)
    {entry : Dynamic.Environment} {copied : Dynamic.Heap}
    (copy : Dynamic.EnvironmentCopies (source.applySubstitution substitution) captured before entry copied)
    (frame : Dynamic.ClosureFrame program
      ((shape.descriptor definitionContext captured).instantiate substitution evidence)) :
    Dynamic.CallableApplies program context callerEvidence evidence before
      (.closure ((shape.descriptor definitionContext captured).instantiate substitution evidence))
      [argument] argument
      ⟨copied.cells ++ [{type := (shape.parameter.applySubstitution substitution).scheme.body, value := some argument}]⟩ := by
  let function := (shape.descriptor definitionContext captured).instantiate substitution evidence
  let parameter := shape.parameter.applySubstitution substitution
  let after : Dynamic.Heap := ⟨copied.cells ++ [{type := parameter.scheme.body, value := some argument}]⟩
  have allocation : Dynamic.Heap.Allocates copied parameter.scheme.body (some argument)
      ⟨copied.cells.length⟩ after := .append
  have read : Dynamic.ExpressionEvaluates program
      (function.context.withLocal parameter.id parameter.scheme parameter.schemeRequirements)
      evidence function.source ((parameter.id, ⟨copied.cells.length⟩) :: entry)
      after shape.parameterRead.node.id argument after := by
    apply Dynamic.ExpressionEvaluates.intro
      (FlexibleSubstitution.ContainsExpression.applySubstitution substitution
        (lookupExpression?_sound shape.parameterRead.found))
    · simp only [ExpressionNode.applySubstitution, ExpressionForm.applySubstitution,
        shape.parameterRead.form, shape.parameterRead.requirements, shape.parameterRead.coercions]
      exact .local rfl .head allocation.reads_new rfl rfl
    · simp only [ExpressionNode.applySubstitution, shape.parameterRead.coercions, List.map_nil]
      exact .nil
  have returned : Dynamic.StatementExecutes program
      (function.context.withLocal parameter.id parameter.scheme parameter.schemeRequirements)
      evidence function.source ((parameter.id, ⟨copied.cells.length⟩) :: entry)
      after shape.identityReturn.id
      (function.context.withLocal parameter.id parameter.scheme parameter.schemeRequirements)
      (.returned argument) after := by
    exact .returnValue
      (FlexibleSubstitution.ContainsStatement.applySubstitution substitution
        (lookupStatement?_sound shape.identityFound))
      (by simp only [StatementNode.applySubstitution, shape.identityForm,
        StatementForm.applySubstitution]) read
  have parameters : ∃ types callContext,
      MonoBindersExtend function.source.owner function.context function.parameters types callContext := by
    rcases frame.code.occurrence with ⟨id, node, _contains, form, _raw, typed⟩
    rw [form] at typed
    generalize rawEq : TypeSystem.Ty.function
      (TypeSystem.Ty.productMany (function.parameters.map (fun binder => binder.scheme.body)))
      function.resultType = raw at typed
    cases typed with
    | lambda names parameters body completes => exact ⟨_, _, parameters⟩
  obtain ⟨types, callContext, parameters⟩ := parameters
  have parameterList : function.parameters = [parameter] := rfl
  rw [parameterList] at parameters
  cases parameters with
  | cons scheme extended tail =>
    cases tail
    cases extended with
    | intro wellformed fresh =>
      apply Dynamic.CallableApplies.closure rfl frame
        (parameterList.symm ▸ MonoBindersExtend.cons scheme (.intro wellformed fresh) (.nil _)) copy
      · exact .cons allocation (.nil _ _)
      · apply Dynamic.FunctionStatementsExecute.singleton
          (FlexibleSubstitution.ContainsStatement.applySubstitution substitution
            (lookupStatement?_sound shape.identityFound))
        · intro expression impossible
          simp only [StatementNode.applySubstitution, shape.identityForm,
            StatementForm.applySubstitution] at impossible
          cases impossible
        · exact returned
      · rfl

/-- A read selects the actual instance before the ordered argument evaluation.
The call copies the captures and allocates the identity parameter only after
that argument finishes. -/
theorem Shape.invoke {source : TypedSource} (shape : Shape source)
    {argumentId : ExpressionId} {type : TypeSystem.Ty}
    (call : CallShape source shape.binder argumentId type)
    {program : SourceSemantics.Program} {definitionContext context : SourceSemantics.Context}
    (captured environment : Dynamic.Environment) (substitution : TypeSystem.Substitution)
    (evidence produced : Dynamic.EvidenceEnvironment)
    {before argumentsHeap : Dynamic.Heap} {argument : Dynamic.Value}
    {location : Dynamic.Location} {cell : Dynamic.Cell}
    (lookup : Dynamic.Environment.LooksUp environment shape.binder.id location)
    (read : Dynamic.Heap.Reads before location cell)
    (descriptor : cell.generalized = some (shape.descriptor definitionContext captured))
    (fields : Dynamic.RuntimeContextFields definitionContext context)
    (instantiation : Dynamic.LocalSchemeRuntimeInstantiation context evidence shape.binder
      (.function type type) [] substitution produced)
    (frame : Dynamic.ClosureFrame program
      ((shape.descriptor definitionContext captured).instantiate substitution
        (produced ++ evidence.applySubstitution substitution)))
    (argumentTrace : Dynamic.ExpressionEvaluates program context evidence source environment
      before argumentId argument argumentsHeap)
    {entry : Dynamic.Environment} {copied : Dynamic.Heap}
    (copy : Dynamic.EnvironmentCopies (source.applySubstitution substitution) captured argumentsHeap entry copied) :
    Dynamic.ExpressionEvaluates program context evidence source environment before call.node.id
      argument ⟨copied.cells ++ [{type := (shape.parameter.applySubstitution substitution).scheme.body, value := some argument}]⟩ := by
  have callee : Dynamic.ExpressionEvaluates program context evidence source environment before
      call.callee.node.id
      (.closure ((shape.descriptor definitionContext captured).instantiate substitution
        (produced ++ evidence.applySubstitution substitution))) before := by
    apply Dynamic.ExpressionEvaluates.generalizedLocal (owned := [])
      (lookupExpression?_sound call.callee.found) call.callee.form
      (by rw [call.callee.requirements, call.callee.coercions]; rfl)
      lookup read descriptor fields
    · rw [call.callee.raw]; exact instantiation
    · rw [call.callee.coercions]; exact .nil
  apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound call.found)
  · rw [call.form]
    exact .indirectCall
      (by rw [call.requirements, call.argumentCoercions, call.coercions]; rfl)
      callee (.cons argumentTrace .nil) (.singleton argument)
      (by rw [call.argumentCoercions]; exact .nil) (.singleton argument)
      (by rw [call.arity]; rfl) (by rw [call.arity]; rfl)
      (shape.identity_applies captured substitution _ evidence argumentsHeap argument copy frame)
  · rw [call.coercions]; exact .nil

/-- The two runtime instances use an exact singleton substitution. Original
scheme validity and the requested ground type are the only typing inputs. -/
theorem Shape.instance {source : TypedSource} (shape : Shape source)
    {context : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment)
    {type : TypeSystem.Ty} (wellformed : SchemeWellFormed context shape.binder.scheme)
    (ground : TypeWellFormed context type) :
    Dynamic.LocalSchemeRuntimeInstantiation context evidence shape.binder
      (.function type type) [] [(shape.typeVariable, type)] [] := by
  refine ⟨LocalSchemeRequirementsWellFormed.empty _ _ shape.schemeRequirements,
    wellformed, ?_, ?_, ?_, by simp, ?_, ?_⟩
  · rw [shape.scheme]; exact ExactSubstitution.singleton _ _
  · intro typeVariable replacement member
    have same := List.mem_singleton.mp member
    cases same
    exact ground
  · simp [shape.scheme, TypeSystem.Substitution.apply, TypeSystem.Substitution.lookup?]
  · intro id member; cases member
  · rw [instantiateLocalSchemePredicates, shape.schemeRequirements]
    exact .nil

/-- Deep typing of the actual captured descriptor supplies the static invocation
frame for each instance, independently of executing either call. -/
theorem Shape.frame {source : TypedSource} (shape : Shape source)
    {program : SourceSemantics.Program} {context nextContext : SourceSemantics.Context}
    (environment : Dynamic.Environment) (heap : Dynamic.Heap)
    (evidence : Dynamic.EvidenceEnvironment) {type : TypeSystem.Ty}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (typed : Dynamic.GeneralizedClosureWellTyped nextContext heap (shape.descriptor context environment))
    (fields : Dynamic.RuntimeContextFields context nextContext)
    (signatures : nextContext.signatures = program.signatures)
    (covers : evidence.Covers nextContext)
    (wellformed : SchemeWellFormed nextContext shape.binder.scheme)
    (ground : TypeWellFormed nextContext type) :
    Dynamic.ClosureFrame program
      ((shape.descriptor context environment).instantiate [(shape.typeVariable, type)]
        (evidence.applySubstitution [(shape.typeVariable, type)])) := by
  have materialized := Dynamic.GeneralizedClosureWellTyped.instantiateHasType
    catalog typed fields covers (shape.instance evidence wellformed ground)
  obtain ⟨_parameter, _result, same, code, closed, _captured⟩ := materialized.closure_function_inv
  exact ⟨same.trans signatures, code.owner, code, code.requirement_ledger.idsUnique, closed⟩

/-- The heap after the generalized `let`: the copies of the function's
environment, then the principal descriptor over those copies. -/
def Shape.declaredHeap {source : TypedSource} (shape : Shape source)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) : Dynamic.Heap :=
  shape.allocatedHeap context (copies source environment before).1 (copies source environment before).2

/-- The Word call copies the descriptor's captures, then allocates its
parameter. -/
def Shape.wordHeap {source : TypedSource} (shape : Shape source)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) : Dynamic.Heap :=
  ⟨(copies source (copies source environment before).1 (shape.declaredHeap context environment before)).2.cells ++
    [{type := (shape.parameter.applySubstitution [(shape.typeVariable, .word)]).scheme.body, value := some (.word (Core.Word.ofNatModulo 11))}]⟩

/-- The Bool call copies the same captures again, then allocates its
parameter. -/
def Shape.finalHeap {source : TypedSource} (shape : Shape source)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (flag : Bool) : Dynamic.Heap :=
  ⟨(copies source (copies source environment before).1 (shape.wordHeap context environment before)).2.cells ++
    [{type := (shape.parameter.applySubstitution [(shape.typeVariable, .bool)]).scheme.body, value := some (.bool flag)}]⟩

/-- Full independent body trace: the environment copies and principal
descriptor allocation, Word read, copies and call, Bool read, copies and call,
then ordered product return. All frame premises are static code/evidence
validity, and no native result is used. -/
theorem Shape.body_trace {source : TypedSource} (shape : Shape source)
    {program : SourceSemantics.Program} {context nextContext : SourceSemantics.Context}
    (evidence : Dynamic.EvidenceEnvironment) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (flag : Bool)
    (unique : NodeOccurrencesUnique source)
    (different : shape.binder.id ≠ shape.flag.id)
    (extended : BinderExtends source.owner context shape.binder nextContext)
    (fields : Dynamic.RuntimeContextFields context nextContext)
    (wellformed : SchemeWellFormed nextContext shape.binder.scheme)
    (word : TypeWellFormed nextContext .word) (boolean : TypeWellFormed nextContext .bool)
    {literalType : TypeSystem.Ty}
    (literal : ExpressionHasType source nextContext shape.literal.node.id literalType)
    {location : Dynamic.Location} {cell : Dynamic.Cell}
    (flagLookup : Dynamic.Environment.LooksUp environment shape.flag.id location)
    (flagRead : Dynamic.Heap.Reads before location cell)
    (flagDescriptor : cell.generalized = none) (flagValue : cell.value = some (.bool flag))
    (readable : Readable before environment)
    (wordFrame : Dynamic.ClosureFrame program
      ((shape.descriptor context (copies source environment before).1).instantiate [(shape.typeVariable, .word)]
        (evidence.applySubstitution [(shape.typeVariable, .word)])))
    (boolFrame : Dynamic.ClosureFrame program
      ((shape.descriptor context (copies source environment before).1).instantiate [(shape.typeVariable, .bool)]
        (evidence.applySubstitution [(shape.typeVariable, .bool)]))) :
    Dynamic.FunctionStatementsExecute program context evidence source environment before
      [shape.initialized.id, shape.returned.id] nextContext
      (.returned (.product (.word (Core.Word.ofNatModulo 11)) (.bool flag)))
      (shape.finalHeap context environment before flag) := by
  let captured := (copies source environment before).1
  let middle := (copies source environment before).2
  have snapshot : Dynamic.EnvironmentCopies source environment before captured middle :=
    copies_spec source readable
  let allocated := shape.declaredHeap context environment before
  let wordCopied := (copies source captured allocated).2
  let first := shape.wordHeap context environment before
  let after := shape.finalHeap context environment before flag
  let locals := (shape.binder.id, ⟨middle.cells.length⟩) :: environment
  have allocation : Dynamic.Heap.AllocatesGeneralized middle (shape.descriptor context captured)
      ⟨middle.cells.length⟩ allocated := .append
  have capturedAllocated : Readable allocated captured :=
    (Readable.of_copies snapshot readable).mono (Dynamic.HeapMetadataExtend.of_generalized_allocation allocation)
  have wordCopy := copies_spec_applySubstitution [(shape.typeVariable, .word)] source capturedAllocated
  have firstAllocation : Dynamic.Heap.Allocates wordCopied
      (shape.parameter.applySubstitution [(shape.typeVariable, .word)]).scheme.body
      (some (.word (Core.Word.ofNatModulo 11))) ⟨wordCopied.cells.length⟩ first := .append
  have literalTrace : Dynamic.ExpressionEvaluates program nextContext evidence source locals
      allocated shape.literal.node.id (.word (Core.Word.ofNatModulo 11)) allocated := by
    simpa only [shape.literalValue] using shape.literal.evaluates evidence locals allocated unique literal
  have firstTrace := shape.invoke shape.wordCall captured locals [(shape.typeVariable, .word)] evidence []
    Dynamic.Environment.LooksUp.head allocation.reads_new rfl fields
    (shape.instance evidence wellformed word) wordFrame literalTrace wordCopy
  have flagTrace : Dynamic.ExpressionEvaluates program nextContext evidence source locals first
      shape.flagRead.node.id (.bool flag) first := by
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound shape.flagRead.found)
    · rw [shape.flagRead.form]
      exact .local (by rw [shape.flagRead.requirements, shape.flagRead.coercions]; rfl)
        (.tail different flagLookup)
        (firstAllocation.preserves_read (wordCopy.preserves_read
          (allocation.preserves_read (snapshot.preserves_read flagRead))))
        flagDescriptor flagValue
    · rw [shape.flagRead.coercions]; exact .nil
  have capturedFirst : Readable first captured :=
    (capturedAllocated.mono wordCopy.metadata_extends).mono (Dynamic.HeapMetadataExtend.of_allocation firstAllocation)
  have boolCopy := copies_spec_applySubstitution [(shape.typeVariable, .bool)] source capturedFirst
  have secondTrace := shape.invoke shape.boolCall captured locals [(shape.typeVariable, .bool)] evidence []
    Dynamic.Environment.LooksUp.head (firstAllocation.preserves_read (wordCopy.preserves_read allocation.reads_new))
    rfl fields (shape.instance evidence wellformed boolean) boolFrame flagTrace boolCopy
  have tupleTrace : Dynamic.ExpressionEvaluates program nextContext evidence source locals allocated
      shape.tuple.id (.product (.word (Core.Word.ofNatModulo 11)) (.bool flag)) after := by
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound shape.tupleFound)
    · rw [shape.tupleForm]
      exact .tuple (by rw [shape.tupleRequirements, shape.tupleCoercions]; rfl)
        (.cons firstTrace (.cons secondTrace .nil)) (.cons (.singleton _))
    · rw [shape.tupleCoercions]; exact .nil
  apply Dynamic.FunctionStatementsExecute.cons (shape.initializes evidence snapshot extended)
  apply Dynamic.FunctionStatementsExecute.singleton (lookupStatement?_sound shape.returnedFound)
  · intro expression impossible; rw [shape.returnedForm] at impossible; cases impossible
  · exact .returnValue (lookupStatement?_sound shape.returnedFound) shape.returnedForm tupleTrace

end Tests.SourceCoreSelectedGeneralizedLocal
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedGeneralizedLocalSourceFirst
/-! Original checker typing supplies both materialized closure frames before
the independent Source execution. No completed native call is an input. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedGeneralizedLocal
open Solcore Frontend SourceInference SourceSemantics
open Tests.SourceSemanticsCaptureCopies

private theorem head_tail {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {rest : List StatementId} {facts : BodyFacts}
    (typed : StatementsHaveType source control context (id :: rest) final facts) :
    ∃ middle headFacts tailFacts, StatementHasType source control context id middle headFacts ∧
      StatementsHaveType source control middle rest final tailFacts := by
  cases typed with
  | singleton head => exact ⟨_, _, _, head, .nil _ _⟩
  | cons head tail => exact ⟨_, _, _, head, tail⟩

private theorem form_at {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {facts : StatementFacts} {node : StatementNode}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (typed : StatementHasType source control context id final facts) :
    Dynamic.StatementHasType.FormTyping source control context node.form final := by
  obtain ⟨actual, contains, original⟩ := Dynamic.StatementHasType.formTyping typed
  cases Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  exact original

private theorem lookup_declared {heap : Dynamic.Heap} {scope : Resolved.LocalScope TypeSystem.Scheme}
    {environment : Dynamic.Environment} (agrees : Dynamic.EnvironmentAgrees heap scope environment)
    {id : Resolved.LocalId} {location : Dynamic.Location}
    (lookup : Dynamic.Environment.LooksUp environment id location) : id ∈ scope.map Prod.fst := by
  induction agrees with
  | nil => cases lookup
  | cons _ _ _ _ ih =>
    cases lookup with
    | head => simp
    | tail _ tail => exact List.mem_cons_of_mem _ (ih tail)

private theorem Shape.literal_typed {source : TypedSource} (shape : Shape source)
    {context : SourceSemantics.Context} {type : TypeSystem.Ty}
    (unique : NodeOccurrencesUnique source)
    (typed : ExpressionHasType source context shape.tuple.id type) :
    ∃ literalType, ExpressionHasType source context shape.literal.node.id literalType := by
  cases typed with
  | intro contains raw _ _ _ _ =>
    cases Option.some.inj ((lookupExpression?_complete unique contains).symm.trans shape.tupleFound)
    rw [shape.tupleForm] at raw
    cases raw with
    | tuple children =>
      cases children with
      | cons first _ =>
        cases first with
        | intro contains raw _ _ _ _ =>
          cases Option.some.inj ((lookupExpression?_complete unique contains).symm.trans shape.wordCall.found)
          rw [shape.wordCall.form] at raw
          cases raw with
          | indirectCall _ arguments _ =>
            cases arguments with
            | cons literal _ => exact ⟨_, literal⟩

/-- The actual generalized declaration rule derives both Word and Bool code
frames from the copies of the lexical environment and the original typed body. -/
theorem Shape.body_from_source {source : TypedSource} (shape : Shape source)
    {program : SourceSemantics.Program} {context final : SourceSemantics.Context}
    {control : ControlContext} {facts : BodyFacts}
    (evidence : Dynamic.EvidenceEnvironment) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (flag : Bool)
    (runtime : Dynamic.SourceRuntimeValid program context source)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (covers : evidence.Covers context)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (typed : StatementsHaveType source control context
      [shape.initialized.id, shape.returned.id] final facts)
    {location : Dynamic.Location} {cell : Dynamic.Cell}
    (flagLookup : Dynamic.Environment.LooksUp environment shape.flag.id location)
    (flagRead : Dynamic.Heap.Reads before location cell)
    (flagDescriptor : cell.generalized = none) (flagValue : cell.value = some (.bool flag)) :
    ∃ nextContext, Dynamic.FunctionStatementsExecute program context evidence source environment before
      [shape.initialized.id, shape.returned.id] nextContext
      (.returned (.product (.word (Core.Word.ofNatModulo 11)) (.bool flag)))
      (shape.finalHeap context environment before flag) := by
  have unique := runtime.graph.nodeOccurrencesUnique
  obtain ⟨next, _, _, first, rest⟩ := head_tail typed
  have original := form_at unique shape.initializedFound first
  rw [shape.initializedForm] at original
  cases original with
  | letInitialized _ monomorphic _ =>
    rw [shape.scheme] at monomorphic
    cases monomorphic
  | letInitializedGeneralized polymorphic requirements generalizes initializer extended =>
    have readable := Readable.of_agrees locals
    have snapshot := copies_spec source readable
    have descriptorTyped := (shape.captures context (copies source environment before).1).wellTyped runtime
      (snapshot.agrees locals) polymorphic requirements generalizes initializer extended
    have fields := Dynamic.RuntimeContextFields.ofBinderExtends extended
    obtain ⟨_, _, _, returned, _⟩ := head_tail rest
    have originalReturn := form_at unique shape.returnedFound returned
    rw [shape.returnedForm] at originalReturn
    cases originalReturn with
    | returnValue tuple =>
      obtain ⟨literalType, literal⟩ := shape.literal_typed unique tuple
      cases extended with
      | intro wellformed fresh =>
        have scheme : SchemeWellFormed
            (context.withLocal shape.binder.id shape.binder.scheme shape.binder.schemeRequirements)
            shape.binder.scheme := {
          binders := wellformed.scheme.binders.withLocal _ _ _
          quantified_nodup := wellformed.scheme.quantified_nodup
          body := wellformed.scheme.body.withLocal _ _ _
        }
        have word : TypeWellFormed
            (context.withLocal shape.binder.id shape.binder.scheme shape.binder.schemeRequirements) .word :=
          ⟨scheme.binders, .builtin .word⟩
        have boolean : TypeWellFormed
            (context.withLocal shape.binder.id shape.binder.scheme shape.binder.schemeRequirements) .bool :=
          ⟨scheme.binders, .builtin .bool⟩
        have descriptorNext : Dynamic.GeneralizedClosureWellTyped
            (context.withLocal shape.binder.id shape.binder.scheme shape.binder.schemeRequirements)
            (copies source environment before).2 (shape.descriptor context (copies source environment before).1) :=
          ⟨descriptorTyped.same_signatures, descriptorTyped.code, descriptorTyped.captures⟩
        have different : shape.binder.id ≠ shape.flag.id := by
          intro same
          exact fresh.1 (same.symm ▸ lookup_declared locals flagLookup)
        exact ⟨_, shape.body_trace evidence environment before flag unique different
          (.intro wellformed fresh) fields scheme word boolean literal flagLookup flagRead flagDescriptor flagValue
          readable
          (shape.frame _ _ evidence catalog descriptorNext fields runtime.signatures
            (fields.covers covers) scheme word)
          (shape.frame _ _ evidence catalog descriptorNext fields runtime.signatures
            (fields.covers covers) scheme boolean)⟩

end Tests.SourceCoreSelectedGeneralizedLocal
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedGeneralizedLocalSelectedSource
/-! The selected actual header receives the original Bool argument by Source
allocation. Original program typing then constructs the complete Source body
execution, before any target execution is considered. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedGeneralizedLocal
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering

private theorem roots_injective {left right : List StatementId}
    (same : left.map NodeId.statement = right.map NodeId.statement) : left = right := by
  induction left generalizing right with
  | nil => cases right <;> simp at same ⊢
  | cons head rest ih =>
    cases right with
    | nil => simp at same
    | cons other tail =>
      simp only [List.map_cons, List.cons.injEq] at same
      cases same.1
      exact congrArg (List.cons head) (ih same.2)

variable {fixture : ProfiledFixture} {row : Row fixture.original}

theorem SelectedInventory.source_eq (selected : SelectedInventory fixture row) :
    selected.packet.header.function.source = row.original.function.typedBody :=
  selected.packet.header.agreement.source.trans
    (congrArg (fun named => named.function.typedBody) selected.header_original)

def SelectedInventory.shape (selected : SelectedInventory fixture row)
    (original : Shape row.original.function.typedBody) :
    Shape selected.packet.header.function.source :=
  selected.source_eq.symm ▸ original

theorem SelectedInventory.parameters (selected : SelectedInventory fixture row)
    (shape : Shape selected.packet.header.function.source) :
    selected.packet.header.function.parameters = [shape.flag] :=
  selected.packet.header.parameters.trans (selected.packet.header.inputs.symm.trans shape.inputs)

theorem SelectedInventory.input_types (selected : SelectedInventory fixture row)
    (shape : Shape selected.packet.header.function.source) :
    selected.packet.header.types = [.bool] := by
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq selected.packet.header.extended
  simpa only [selected.parameters shape, List.map_cons, List.map_nil,
    shape.flagScheme, TypeSystem.Scheme.mono] using types.symm

theorem SelectedInventory.statements (selected : SelectedInventory fixture row)
    (shape : Shape selected.packet.header.function.source) :
    selected.packet.header.function.body = [shape.initialized.id, shape.returned.id] :=
  roots_injective (selected.packet.header.agreement.roots.symm.trans shape.roots)

def flagHeap (before : Dynamic.Heap) (flag : Bool) : Dynamic.Heap :=
  ⟨before.cells ++ [{type := .bool, value := some (.bool flag)}]⟩

def flagEnvironment (binder : TypedBinder) (before : Dynamic.Heap) : Dynamic.Environment :=
  [(binder.id, ⟨before.cells.length⟩)]

/-- Source parameters and the complete independent body are obtained from the
actual selected Header and the original program typing certificate. -/
theorem SelectedInventory.source_body (selected : SelectedInventory fixture row)
    (shape : Shape selected.packet.header.function.source)
    (wellFormed : ProgramWellFormed (Program.ofChecked fixture.original.recipe.compiled.sourceProgram))
    (before : Dynamic.Heap) (flag : Bool) :
    Dynamic.BindersAllocate [] before selected.packet.header.function.parameters [.bool flag]
      (flagEnvironment shape.flag before) (flagHeap before flag) ∧
    ∃ final, Dynamic.FunctionStatementsExecute
      (Program.ofChecked fixture.original.recipe.compiled.sourceProgram)
      selected.packet.header.context selected.packet.header.function.evidence
      selected.packet.header.function.source (flagEnvironment shape.flag before) (flagHeap before flag)
      selected.packet.header.function.body final
      (.returned (.product (.word (Word.ofNatModulo 11)) (.bool flag)))
      (shape.finalHeap selected.packet.header.context (flagEnvironment shape.flag before)
        (flagHeap before flag) flag) := by
  let header := selected.packet.header
  have allocation : Dynamic.Heap.Allocates before .bool (some (.bool flag))
      ⟨before.cells.length⟩ (flagHeap before flag) := .append
  have bound : Dynamic.BindersAllocate [] before header.function.parameters [.bool flag]
      (flagEnvironment shape.flag before) (flagHeap before flag) := by
    rw [selected.parameters shape]
    exact .cons (by simpa only [shape.flagScheme, TypeSystem.Scheme.mono] using allocation) (.nil _ _)
  have initialLocals : header.function.context.locals = [] := by
    rw [header.frame.context]
    cases header.frame.instantiated with
    | intro _ _ _ _ _ _ _ contextEq => rw [contextEq]; rfl
  have locals : Dynamic.EnvironmentAgrees (flagHeap before flag) header.context.locals
      (flagEnvironment shape.flag before) := by
    rw [header.extended.locals_eq, selected.parameters shape, initialLocals]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.map_cons, List.map_nil,
      List.append_nil]
    exact .cons allocation.reads_new (by rw [shape.flagScheme]; rfl)
      (.ordinary (by rw [shape.flagScheme]; rfl) rfl) .nil
  have certified : SelectedCompilationNamedSourceTyping.Certified header :=
    RecursiveNamedHeaderSourceTyping.certificate header wellFormed
  have fields := Dynamic.MonoBindersExtend.runtimeContextFields header.extended
  have runtime := certified.runtime.transport fields
  have catalog : SignatureCatalogWellFormed header.context.signatures :=
    runtime.signatures.symm ▸ wellFormed.signatures
  have covers : header.function.evidence.Covers header.context :=
    fields.covers (header.frame.context.symm ▸ header.frame.covers)
  obtain ⟨final, facts, typed, _⟩ := certified.statements
  rw [selected.statements shape] at typed
  obtain ⟨next, body⟩ := shape.body_from_source header.function.evidence
    (flagEnvironment shape.flag before) (flagHeap before flag) flag runtime catalog covers locals typed
    Dynamic.Environment.LooksUp.head allocation.reads_new rfl rfl
  exact ⟨bound, next, selected.statements shape ▸ body⟩

end Tests.SourceCoreSelectedGeneralizedLocal
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedGeneralizedLocalTyping
/-! The actual original generalized identity body receives independent
declarative typing, including its principal initializer and both instances.
The observer checks finite metadata and constructs every typing rule. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedGeneralizedLocal
open Solcore Core Frontend SourceInference SourceSemantics
open TypingValidation

def resultType : TypeSystem.Ty := .product .word .bool

def returnFacts (type : TypeSystem.Ty) : StatementFacts :=
  {type, hasValue := true, sawReturn := true, control := .returned}

def localFacts : StatementFacts :=
  {type := .unit, hasValue := false, sawReturn := false, control := .ordinary .unit}

def bodyFacts : BodyFacts := .cons localFacts (.singleton (returnFacts resultType))

structure BodyTyping (signatures : ProgramSignatures) (function : CheckedFunction)
    (signature : ProgramFunctionSignature) where
  statements : List StatementId
  roots : function.typedBody.roots = statements.map NodeId.statement
  context : SourceSemantics.Context
  finalContext : SourceSemantics.Context
  inputs : MonoBindersExtend signature.id (checkedBodyContext signatures signature function)
    function.typedBody.inputs signature.parameterTypes context
  typed : StatementsHaveType function.typedBody {returnType := resultType} context statements finalContext bodyFacts
  result : TypeSystem.Ty.productMany signature.returnTypes = resultType

private theorem roots_injective_variant {left right : List StatementId}
    (mapped : left.map NodeId.statement = right.map NodeId.statement) : left = right := by
  induction left generalizing right with
  | nil => cases right <;> simp_all
  | cons head tail ih =>
    cases right with
    | nil => simp at mapped
    | cons other rest =>
      simp only [List.map_cons, List.cons.injEq] at mapped
      have headEq := NodeId.statement.inj mapped.1
      have tailEq := ih mapped.2
      rw [headEq, tailEq]

theorem BodyTyping.statements_typed {signatures : ProgramSignatures} {function : CheckedFunction}
    {signature : ProgramFunctionSignature} (certificate : BodyTyping signatures function signature) :
    CheckedBodyStatementsHaveType signatures signature function := by
  intro statements roots
  have same : statements = certificate.statements := roots_injective_variant (roots.symm.trans certificate.roots)
  subst statements
  refine ⟨bodyFacts, ?_, ?_⟩
  · rw [certificate.result]; rfl
  · intro context extension
    have same := certificate.inputs.functional extension
    subst context
    exact ⟨certificate.finalContext, by simpa only [certificate.result] using certificate.typed⟩

def observeBodyTyping (signatures : ProgramSignatures) (function : CheckedFunction)
    (signature : ProgramFunctionSignature) : IO (BodyTyping signatures function signature) := do
  let shape ← observeShape function.typedBody
  let ⟨inputTypes⟩ ← observe (signature.parameterTypes = [.bool]) "generalized original signature input"
  let ⟨result⟩ ← observe (TypeSystem.Ty.productMany signature.returnTypes = resultType)
    "generalized original signature result"
  let base := checkedBodyContext signatures signature function
  let lexical := base.withLocal shape.flag.id shape.flag.scheme shape.flag.schemeRequirements
  let ⟨flagExtended⟩ ← TypingValidation.binder base signature.id shape.flag
  let ⟨flagRequirements⟩ ← observe (shape.flag.schemeRequirements = []) "generalized input requirements"
  have inputs : MonoBindersExtend signature.id base function.typedBody.inputs signature.parameterTypes lexical := by
    rw [shape.inputs, inputTypes]
    exact .cons shape.flagScheme flagExtended (.nil _)
  let principal := localSchemeInitializerContext lexical shape.binder
  let parameterContext := principal.withLocal shape.parameter.id shape.parameter.scheme shape.parameter.schemeRequirements
  let ⟨parameterExtended⟩ ← TypingValidation.binder principal function.typedBody.owner shape.parameter
  let ⟨parameterTyped⟩ ← TypingValidation.read shape.parameterRead parameterContext
    parameterExtended.local_self parameterExtended.local_scheme_requirements_self
  let ⟨identityType⟩ ← observe (shape.identityReturn.type = .variable shape.typeVariable)
    "generalized original identity return type"
  have identity : StatementHasType function.typedBody {returnType := .variable shape.typeVariable}
      parameterContext shape.identityReturn.id parameterContext (returnFacts (.variable shape.typeVariable)) :=
    .returnValue (lookupStatement?_sound shape.identityFound) shape.identityForm parameterTyped identityType
  have parameterInputs : MonoBindersExtend function.typedBody.owner principal [shape.parameter]
      [.variable shape.typeVariable] parameterContext :=
    .cons shape.parameterScheme parameterExtended (.nil _)
  have lambdaForm : ExpressionFormHasRawType function.typedBody principal shape.lambda.form
      (.function (.variable shape.typeVariable) (.variable shape.typeVariable)) (.ordinary []) := by
    rw [shape.lambdaForm]
    exact .lambda (by simp) parameterInputs (.singleton identity) (by simp [BodyCompletes, BodyFacts.singleton, returnFacts, ControlSummary.returned])
  let ⟨initializerTyped⟩ ← uncoerced principal shape.lambda
    (.function (.variable shape.typeVariable) (.variable shape.typeVariable)) shape.lambdaFound lambdaForm
  let finalContext := lexical.withLocal shape.binder.id shape.binder.scheme shape.binder.schemeRequirements
  let ⟨localExtended⟩ ← TypingValidation.binder lexical function.typedBody.owner shape.binder
  let ⟨generalized⟩ ← generalizes lexical shape.binder
  let ⟨initializedType⟩ ← observe (shape.initialized.type = .unit) "generalized original let type"
  have initialized : StatementHasType function.typedBody {returnType := resultType} lexical
      shape.initialized.id finalContext localFacts := by
    refine .letInitializedGeneralized (lookupStatement?_sound shape.initializedFound) shape.initializedForm
      (by rw [shape.scheme]; simp) (LocalSchemeRequirementsWellFormed.empty _ _ shape.schemeRequirements)
      generalized ?_ localExtended initializedType
    simpa only [shape.scheme] using initializerTyped
  let ⟨wordRead⟩ ← TypingValidation.read shape.wordCall.callee finalContext
    localExtended.local_self localExtended.local_scheme_requirements_self
  let ⟨boolRead⟩ ← TypingValidation.read shape.boolCall.callee finalContext
    localExtended.local_self localExtended.local_scheme_requirements_self
  let ⟨different⟩ ← observe (shape.binder.id ≠ shape.flag.id) "generalized distinct input and local"
  let ⟨flagRead⟩ ← TypingValidation.read shape.flagRead finalContext
    (.tail different flagExtended.local_self) (.tail different flagExtended.local_scheme_requirements_self)
  let ⟨literalTyped⟩ ← word shape.literal finalContext
  let ⟨wordCall⟩ ← call shape.wordCall finalContext wordRead literalTyped
  let ⟨boolCall⟩ ← call shape.boolCall finalContext boolRead flagRead
  have tupleForm : ExpressionFormHasRawType function.typedBody finalContext shape.tuple.form resultType (.ordinary []) := by
    rw [shape.tupleForm]
    exact .tuple (.cons wordCall (.cons boolCall (.nil _)))
  let ⟨tupleTyped⟩ ← uncoerced finalContext shape.tuple resultType shape.tupleFound tupleForm
  let ⟨returnedType⟩ ← observe (shape.returned.type = resultType) "generalized original return type"
  have returned : StatementHasType function.typedBody {returnType := resultType} finalContext
      shape.returned.id finalContext (returnFacts resultType) :=
    .returnValue (lookupStatement?_sound shape.returnedFound) shape.returnedForm tupleTyped returnedType
  return {
    statements := [shape.initialized.id, shape.returned.id]
    roots := shape.roots
    context := lexical
    finalContext := finalContext
    inputs := inputs
    typed := .cons initialized (.singleton returned)
    result := result }

end Tests.SourceCoreSelectedGeneralizedLocal
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedGeneralizedLocalWellFormed
/-! Whole-program validity of the unchanged one-function regression follows
from its actual checker result and the constructed declarative body proof. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedGeneralizedLocal
open Solcore Core Frontend SourceInference SourceSemantics
open TypingValidation

structure OriginalTyping (fixture : CompiledFixture) where
  function : CheckedFunction
  signature : ProgramFunctionSignature
  functions : fixture.recipe.compiled.sourceProgram.functions = [function]
  methods : fixture.recipe.compiled.sourceProgram.methods = []
  member : signature ∈ fixture.recipe.compiled.sourceProgram.signatures.functions
  owner : function.declaration = signature.id
  body : BodyTyping fixture.recipe.compiled.sourceProgram.signatures function signature

theorem OriginalTyping.wellFormed {fixture : CompiledFixture} (original : OriginalTyping fixture) :
    ProgramWellFormed (Program.ofChecked fixture.recipe.compiled.sourceProgram) := by
  apply programWellFormed_ofCheckProgram_statements fixture.checked
  constructor
  · intro function member signature signatureMember accepted
    rw [original.functions] at member
    have same := List.mem_singleton.mp member
    subst function
    have signatureEq : signature = original.signature := by
      apply eq_of_mem_of_nodup_map (SignatureCatalogWellFormed.ofCheckProgram fixture.checked).function_ids
        signatureMember original.member
      exact (checkFunctionBody_success_declaration accepted).symm.trans original.owner
    subst signature
    exact original.body.statements_typed
  · intro method member
    rw [original.methods] at member
    cases member

def observeOriginalTyping (fixture : CompiledFixture) : IO (OriginalTyping fixture) := do
  match functions : fixture.recipe.compiled.sourceProgram.functions with
  | [function] =>
    let ⟨methodCount⟩ ← observe (fixture.recipe.compiled.sourceProgram.methods.length = 0)
      "generalized full original method list"
    match found : fixture.recipe.compiled.sourceProgram.signatures.functions.find?
        (fun signature => decide (signature.id = function.declaration)) with
    | none => throw (IO.userError "generalized original signature membership")
    | some signature =>
      let body ← observeBodyTyping fixture.recipe.compiled.sourceProgram.signatures function signature
      return {
        function := function
        signature := signature
        functions := functions
        methods := List.length_eq_zero_iff.mp methodCount
        member := List.mem_of_find?_eq_some found
        owner := (of_decide_eq_true (List.find?_some
          (p := fun signature : ProgramFunctionSignature => decide (signature.id = function.declaration)) found)).symm
        body := body }
  | _ => throw (IO.userError "generalized original single function")

def typingProbe : IO Unit := do
  let fixture ← compileFixture
  let original ← observeOriginalTyping fixture
  let _wellFormed : ProgramWellFormed (Program.ofChecked fixture.recipe.compiled.sourceProgram) := original.wellFormed
  unless fixture.recipe.compiled.indexed.base.functions.length == 1 do
    throw (IO.userError "generalized original complete cache size")
  IO.println "GENERALIZED_LOCAL_ORIGINAL_TYPING: originals1/cache1"
  IO.println "GENERALIZED_LOCAL_DECLARATIVE_TYPING_PASS"

end Tests.SourceCoreSelectedGeneralizedLocal
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedGeneralizedLocalPublicStart
/-! Actual opening, export-aware bootstrap and public input receipt, recorded
before resuming the selected function. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedGeneralizedLocal
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open SelectedCompilationPublicSessionState (StartedCall)

structure Started (fixture : CompiledFixture) (key : SourceCoreIndexedSession.Key)
    (arguments : List SourceCorePublicValues.Value) where
  artifact : SourceCoreExecution.Artifact
  opened : artifact.CompiledAt fixture.facade
  bootstrap : SourceCoreExecution.Bootstrap artifact
  fresh : bootstrap.FreshAt
  authority : bootstrap.ExportAuthorityAt
  session : SourceCoreExecution.Session artifact
  ready : bootstrap.resume 100000 = .ready session
  call : StartedCall session key arguments runOptions

def observeStarted (fixture : CompiledFixture) (key : SourceCoreIndexedSession.Key)
    (arguments : List SourceCorePublicValues.Value) : IO (Started fixture key arguments) := do
  let opened ← fixture.facade.openWithReceipt
  let bootstrap ← opened.val.bootstrapWithExportReceipt
  match ready : bootstrap.val.resume 100000 with
  | .error error => throw (IO.userError (reprStr error))
  | .outOfFuel _ => throw (IO.userError "generalized local bootstrap exhausted")
  | .ready session =>
    match started : session.start key arguments runOptions.inputValidationFuel with
    | .error error => throw (IO.userError (reprStr error))
    | .ok checkpoint => return ⟨opened.val, opened.property, bootstrap.val, bootstrap.property.1,
        bootstrap.property.2, session, ready, checkpoint, started⟩


end Tests.SourceCoreSelectedGeneralizedLocal
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedGeneralizedLocalPublic
/-! The complete original cache supplies the real initial public receiver.
Independent Source parameter/body traces are constructed before target resume. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreSelectedGeneralizedLocal
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys owner)

variable {fixture : ProfiledFixture} {row : Row fixture.original}

theorem SelectedInventory.invocation (selected : SelectedInventory fixture row) :
    ∃ sidecar : SourceCoreStageContracts.Sidecar,
      SourceCoreStageContracts.prepareSidecar fixture.original.recipe.compiled.indexed.base.plan
        selected.packet.header.named.signature.key = .ok sidecar ∧
      (SelectedCompilationPhysicalProgramSupport.stages fixture.original.recipe.compiled).Closure
        selected.packet.header.function (RecursiveStageRegistry.scope sidecar [] selected.packet.header.function) := by
  obtain ⟨rawD, function, sourceAt⟩ :=
    (CallableIndexedOwnedPreparedFiniteNamedInventories.source_receipts selected.rows).receipts
      selected.packet.header (by exact List.mem_cons_self)
  obtain ⟨descriptor⟩ := SelectedCompilationCertifiedPublicSession.header_descriptor selected.packet.header
  obtain ⟨sidecar, issued, _same, globalSelected, _declaration, _local, _evidence, _return, _analysis⟩ :=
    CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts.selected sourceAt (CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued selected.input.prepared selected.packet.selected)
      selected.packet.aligned (SelectedCompilationPhysicalProgramSupport.stagePrepared fixture.original.recipe.compiled)
      descriptor
  refine ⟨sidecar, ?_, ?_⟩
  · simpa only [selected.packet.aligned.named, CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued,
      RecursiveNamedPreparedCallEvidence.Prepared.signature_key selected.input.prepared] using issued
  · rw [CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts.global_view sourceAt] at globalSelected
    exact globalSelected

structure InitialForward (selected : SelectedInventory fixture row)
    (shape : Shape row.original.function.typedBody) (flag : Bool)
    (started : Started fixture.original row.original.key [.bool flag])
    (callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true) where
  start : SelectedCompilationPublicSessionInitial.Started selected.rows fixture.ready selected.packet.header started.call
  origin : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.original.recipe.compiled.indexed
  initial : CellAwarePublicInitialStart.Ready callableProfile origin.result.context.registry
    (CallableIndexedOwnedPublicDecodedCallFaults.faults origin.result.diagnostics) start [.bool flag]
  forward : CellAwarePublicNamedForward.ValueForward callableProfile
    (completion := initial.receiving) (header := selected.packet.header)
    (bodyRegistry := origin.result.context.registry)
    (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults origin.result.diagnostics)
    (owner fixture.original.recipe.compiled) initial.caller.base.val
    (payloads := start.native) (nativeCheckpoint := start.checkpoint)
    (publicCheckpoint := started.call.checkpoint)
    (.product (.word (Word.ofNatModulo 11)) (.bool flag))
    ((selected.shape shape).finalHeap selected.packet.header.context
      (flagEnvironment (selected.shape shape).flag ⟨[]⟩) (flagHeap ⟨[]⟩ flag) flag)

/-- Every premise is an original checked/static observation or an actual public
start. Source execution is constructed inside, before the target is resumed. -/
theorem initial_from_source (selected : SelectedInventory fixture row)
    (shape : Shape row.original.function.typedBody) (flag : Bool)
    (typing : OriginalTyping fixture.original)
    (started : Started fixture.original row.original.key [.bool flag])
    (callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true) :
    Nonempty (InitialForward selected shape flag started callableProfile) := by
  obtain ⟨start⟩ := CellAwarePublicInitialStart.from_call
    (rows := selected.rows) (prepared := fixture.ready) (header := selected.packet.header) (call := started.call)
    fixture.original.accepted fixture.original.selected started.opened started.bootstrap started.fresh
    started.authority (.single started.ready) (fun _ member => selected.root_selection member)
  let actualShape := selected.shape shape
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      selected.packet.header.function.context [.bool flag] selected.packet.header.types := by
    rw [selected.input_types actualShape]
    exact .cons ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩ .nil
  have inputMeanings : RecursiveNamedPublicDataInputs.Meanings [.bool flag] [.bool flag] :=
    .cons ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩ .nil
  obtain ⟨origin, _contextAt, _issued, _extension⟩ := CellAwarePublicInitialStart.receiver start
  obtain ⟨initial⟩ := CellAwarePublicInitialStart.of_started selected.distinct callableProfile
    origin.result.context.registry (CallableIndexedOwnedPublicDecodedCallFaults.faults origin.result.diagnostics)
    (SelectedCompilationBodyTyping.Bodies.of_program typing.wellFormed) start inputTypes inputMeanings
  let prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued selected.input.prepared selected.packet.selected
  have diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared :=
    ⟨selected.packet.selected.diagnostics, selected.packet.selected.found, rfl⟩
  obtain ⟨profile⟩ := fixture.profiles.at_slot prepared.selected
  obtain ⟨sidecar, issued, bodySelected⟩ := selected.invocation
  obtain ⟨allocated, final, sourceTrace⟩ := selected.source_body actualShape typing.wellFormed ⟨[]⟩ flag
  obtain ⟨sourceSize, measured⟩ := RecursiveNamedCallBounds.FunctionOutcome.has_size (.control sourceTrace)
  have forward := CellAwarePublicNamedForward.first_value callableProfile initial.issued initial.extension
    prepared selected.packet.aligned fixture.ready diagnostic typing.wellFormed
    (profile.for_compilation prepared.compilation) start.selected
    (owner fixture.original.recipe.compiled) initial.caller.base.val initial.globalReference initial.keyPhysical
    initial.caller.physical initial.stable initial.heapTyped initial.argumentsTyped issued bodySelected
    initial.represented initial.heaps rfl start.started start.atCheckpoint
    (congrArg SourceCoreCompatibleValues.Context.registry initial.contextAt) initial.exportsReady allocated measured
  exact ⟨⟨start, origin, initial, forward⟩⟩

end Tests.SourceCoreSelectedGeneralizedLocal
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedGeneralizedLocalRetained
/-! A later invocation uses the exact physical Source/native state returned
by the first public call. Its independent Source execution is reconstructed
at that retained heap, before evaluating the new target call. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreSelectedGeneralizedLocal
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedBootstrapRootState (keys owner)
open SelectedCompilationPublicSessionState (StartedCall)

variable {fixture : ProfiledFixture} {row : Row fixture.original}
  {selected : SelectedInventory fixture row} {shape : Shape row.original.function.typedBody}
  {firstFlag : Bool} {firstStart : Started fixture.original row.original.key [.bool firstFlag]}
  {callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true}

def InitialForward.functions (first : InitialForward selected shape firstFlag firstStart callableProfile) :=
  CellAwareSelectedPublicSessionState.functions selected.rows first.origin callableProfile

def InitialForward.cells (first : InitialForward selected shape firstFlag firstStart callableProfile) :=
  CellAwareSelectedPublicSessionState.cells selected.rows first.origin callableProfile

structure InitialForward.Retained (first : InitialForward selected shape firstFlag firstStart callableProfile)
    {artifact : SourceCoreExecution.Artifact} (session : SourceCoreExecution.Session artifact)
    (entries : List RecursiveNamedPublicFunctionHistory.Entry) where
  state : CellAwarePublicSessionState.State selected.rows first.functions first.cells selected.packet.header
    first.initial.receiving fixture.original.recipe session entries
  exportsReady : state.session.ExportsReady

def InitialForward.Stopped (first : InitialForward selected shape firstFlag firstStart callableProfile) : Prop :=
  ∃ origin call reason reached,
  ∃ capture : CallableIndexedOwnedFunctionValues.NamedCapture
    (CallableIndexedOwnedPreparedFiniteNamedInventories.headers selected.rows)
    (owner fixture.original.recipe.compiled).key selected.packet.header [] first.start.world,
  ∃ value finalStore finalMap finalWorld required,
    (∀ fuel, required ≤ fuel → first.start.checkpoint.NativeDone fuel value finalStore) ∧
    CellAwarePublicApplicationResult.NamedResultAt
      (registry := first.initial.receiving.result.context.registry)
      first.functions (first.cells first.initial.receiving.result.context.registry)
      (owner fixture.original.recipe.compiled) first.initial.caller.base.val selected.packet.header capture
      first.start.native selected.packet.header.context (.fault (.stage origin call reason)) reached
      value finalStore finalMap finalWorld
      (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults first.initial.receiving.result.diagnostics)

/-- Successful public output manufactures the continuation state from its exact
returned history. The other branch keeps the actual earlier stage rejection. -/
theorem InitialForward.retained (first : InitialForward selected shape firstFlag firstStart callableProfile) :
    (∃ requiredExecution requiredOutput,
      ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome firstStart.artifact),
        requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
        firstStart.call.checkpoint.ResumeAt executionFuel outputFuel outcome →
        ∃ (returned : SourceCoreExecution.Completion firstStart.artifact)
          (retained : first.Retained returned.session []),
          outcome = .succeeded returned ∧
          retained.state.heap = (selected.shape shape).finalHeap selected.packet.header.context
            (flagEnvironment (selected.shape shape).flag ⟨[]⟩) (flagHeap ⟨[]⟩ firstFlag) firstFlag) ∨
    first.Stopped := by
  rcases first.forward with success | stopped
  · obtain ⟨capture, value, finalStore, finalMap, finalWorld, requiredExecution, requiredOutput,
      _result, output⟩ := success
    refine .inl ⟨requiredExecution, requiredOutput, ?_⟩
    intro executionFuel outputFuel outcome enough outputEnough resumed
    obtain ⟨returned, actual, generation, caller, succeeded, _nativeResult, atReturned, _related,
      history, registry, exportsReady⟩ := output executionFuel outputFuel outcome enough outputEnough resumed
    exact ⟨returned, ⟨{
      artifact := first.start.artifact, session := actual.session,
      mapping := finalMap, world := finalWorld,
      heap := (selected.shape shape).finalHeap selected.packet.header.context
        (flagEnvironment (selected.shape shape).flag ⟨[]⟩) (flagHeap ⟨[]⟩ firstFlag) firstFlag,
      store := finalStore, caller := caller, atSession := atReturned.2.2.2,
      atRecipe := first.start.started.recipe_eq, receiving := first.initial.receiving,
      issued := first.initial.issued, extension := .refl _, registry := registry, history := history
      }, exportsReady⟩, succeeded, rfl⟩
  · exact .inr stopped

structure NextForward (first : InitialForward selected shape firstFlag firstStart callableProfile)
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (retained : first.Retained session entries) (flag : Bool)
    (call : StartedCall session row.original.key [.bool flag] runOptions) where
  start : CellAwarePublicNextStart.Started (header := selected.packet.header) retained.state call
  ready : CellAwarePublicNextStart.Ready retained.state call start [.bool flag]
  forward : CellAwarePublicNamedContinuation.ValueForward callableProfile
    (completion := ready.receiving) (header := selected.packet.header)
    (bodyRegistry := first.origin.result.context.registry)
    (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults first.origin.result.diagnostics)
    (owner fixture.original.recipe.compiled) retained.state.caller
    (payloads := start.payloads) (nativeCheckpoint := start.checkpoint)
    (publicCheckpoint := call.checkpoint) entries
    (.product (.word (Word.ofNatModulo 11)) (.bool flag))
    ((selected.shape shape).finalHeap selected.packet.header.context
      (flagEnvironment (selected.shape shape).flag retained.state.heap)
      (flagHeap retained.state.heap flag) flag)

/-- A retained state is produced by prior public output. No trace or result of
the new call is assumed; its complete original Source body is constructed here. -/
theorem next_from_source (first : InitialForward selected shape firstFlag firstStart callableProfile)
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (retained : first.Retained session entries) (flag : Bool)
    (typing : OriginalTyping fixture.original)
    (call : StartedCall session row.original.key [.bool flag] runOptions) :
    Nonempty (NextForward first retained flag call) := by
  obtain ⟨start⟩ := CellAwarePublicNextStart.from_call (prepared := fixture.ready)
    (header := selected.packet.header) retained.state call
    (fun _ found => selected.root_selection (List.mem_of_find?_eq_some found))
  let actualShape := selected.shape shape
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      selected.packet.header.function.context [.bool flag] selected.packet.header.types := by
    rw [selected.input_types actualShape]
    exact .cons ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩ .nil
  have inputMeanings : RecursiveNamedPublicDataInputs.Meanings [.bool flag] [.bool flag] :=
    .cons ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩ .nil
  obtain ⟨ready⟩ := CellAwarePublicNextStart.of_started retained.state call
    (CellAwarePublicCells.generalized_extends_registry _ _)
    (SelectedCompilationBodyTyping.Bodies.of_program typing.wellFormed) start inputTypes inputMeanings
  let prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued selected.input.prepared selected.packet.selected
  have diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared :=
    ⟨selected.packet.selected.diagnostics, selected.packet.selected.found, rfl⟩
  obtain ⟨profile⟩ := fixture.profiles.at_slot prepared.selected
  obtain ⟨sidecar, issued, bodySelected⟩ := selected.invocation
  obtain ⟨allocated, final, sourceTrace⟩ := selected.source_body actualShape typing.wellFormed retained.state.heap flag
  obtain ⟨sourceSize, measured⟩ := RecursiveNamedCallBounds.FunctionOutcome.has_size (.control sourceTrace)
  have forward := CellAwarePublicNamedContinuation.after_value callableProfile ready.issued ready.receiving.result.extension
    prepared selected.packet.aligned fixture.ready diagnostic typing.wellFormed
    (profile.for_compilation prepared.compilation) start.selected
    (owner fixture.original.recipe.compiled) retained.state.caller ready.globalReference
    (CallableIndexedOwnedPreparedPhysicalBootstrap.key_physical _ _) ready.history.physical ready.stable
    ready.heapTyped ready.argumentsTyped issued bodySelected ready.represented ready.history.semantic.current.2.1
    rfl start.started start.atCheckpoint (congrArg SourceCoreCompatibleValues.Context.registry ready.contextAt)
    retained.exportsReady ready.history allocated measured
  exact ⟨⟨start, ready, forward⟩⟩

variable {first : InitialForward selected shape firstFlag firstStart callableProfile}
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {entries : List RecursiveNamedPublicFunctionHistory.Entry}
  {retained : first.Retained session entries} {flag : Bool}
  {call : StartedCall session row.original.key [.bool flag] runOptions}

def NextForward.Stopped (next : NextForward first retained flag call) : Prop :=
  ∃ origin stageCall reason reached,
  ∃ capture : CallableIndexedOwnedFunctionValues.NamedCapture
    (CallableIndexedOwnedPreparedFiniteNamedInventories.headers selected.rows)
    (owner fixture.original.recipe.compiled).key selected.packet.header
    retained.state.mapping retained.state.world,
  ∃ value finalStore finalMap finalWorld required,
    (∀ fuel, required ≤ fuel → next.start.checkpoint.NativeDone fuel value finalStore) ∧
    CellAwarePublicApplicationResult.NamedResultAt
      (registry := next.ready.receiving.result.context.registry)
      first.functions (first.cells next.ready.receiving.result.context.registry)
      (owner fixture.original.recipe.compiled) retained.state.caller selected.packet.header capture
      next.start.payloads selected.packet.header.context (.fault (.stage origin stageCall reason)) reached
      value finalStore finalMap finalWorld
      (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults next.ready.receiving.result.diagnostics)

/-- Repeated calls keep the actual returned heap, receiver and full history.
The initial model remains fixed while each call uses its current decoder. -/
theorem NextForward.retains_state (next : NextForward first retained flag call) :
    (∃ requiredExecution requiredOutput,
      ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome artifact),
        requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
        call.checkpoint.ResumeAt executionFuel outputFuel outcome →
        ∃ (returned : SourceCoreExecution.Completion artifact)
          (continued : first.Retained returned.session entries),
          outcome = .succeeded returned ∧
          continued.state.heap = (selected.shape shape).finalHeap selected.packet.header.context
            (flagEnvironment (selected.shape shape).flag retained.state.heap)
            (flagHeap retained.state.heap flag) flag) ∨
    next.Stopped := by
  rcases next.forward with success | stopped
  · obtain ⟨capture, value, finalStore, finalMap, finalWorld, requiredExecution, requiredOutput,
      _result, output⟩ := success
    refine .inl ⟨requiredExecution, requiredOutput, ?_⟩
    intro executionFuel outputFuel outcome enough outputEnough resumed
    obtain ⟨returned, actual, generation, caller, succeeded, _nativeResult, atReturned, _related,
      history, registry, exportsReady⟩ := output executionFuel outputFuel outcome enough outputEnough resumed
    exact ⟨returned, ⟨{
      artifact := retained.state.artifact, session := actual.session,
      mapping := finalMap, world := finalWorld,
      heap := (selected.shape shape).finalHeap selected.packet.header.context
        (flagEnvironment (selected.shape shape).flag retained.state.heap)
        (flagHeap retained.state.heap flag) flag,
      store := finalStore, caller := caller, atSession := atReturned.2.2.2,
      atRecipe := retained.state.atRecipe, receiving := next.ready.receiving,
      issued := next.ready.issued, extension := next.ready.extension, registry := registry, history := history
      }, exportsReady⟩, succeeded, rfl⟩
  · exact .inr stopped

end Tests.SourceCoreSelectedGeneralizedLocal
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedGeneralizedLocalObserved
/-! Actual completed public calls retain the Source-derived continuation without
requiring the observer to guess a sufficient execution or export budget. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreSelectedGeneralizedLocal
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedBootstrapRootState (keys owner)
open SelectedCompilationPublicSessionState (StartedCall)

variable {fixture : ProfiledFixture} {row : Row fixture.original}
  {selected : SelectedInventory fixture row} {shape : Shape row.original.function.typedBody}
  {firstFlag : Bool} {firstStart : Started fixture.original row.original.key [.bool firstFlag]}
  {callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true}

/-- The initial independent body and actual observed export retain the same
heap, decoder and original complete compiler inventory. -/
theorem InitialForward.observed_retained
    (first : InitialForward selected shape firstFlag firstStart callableProfile)
    (typing : OriginalTyping fixture.original)
    {executionFuel outputFuel : Nat} {returned : SourceCoreExecution.Completion firstStart.artifact}
    (resumed : firstStart.call.checkpoint.ResumeAt executionFuel outputFuel (.succeeded returned)) :
    Nonempty (first.Retained returned.session []) := by
  let prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued selected.input.prepared selected.packet.selected
  have diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared :=
    ⟨selected.packet.selected.diagnostics, selected.packet.selected.found, rfl⟩
  obtain ⟨profile⟩ := fixture.profiles.at_slot prepared.selected
  obtain ⟨sidecar, issued, bodySelected⟩ := selected.invocation
  obtain ⟨allocated, final, sourceTrace⟩ := selected.source_body (selected.shape shape) typing.wellFormed ⟨[]⟩ firstFlag
  obtain ⟨sourceSize, measured⟩ := RecursiveNamedCallBounds.FunctionOutcome.has_size (.control sourceTrace)
  obtain ⟨stagedContext, stagedOutcome, heap, capture, native, store, mapping, world, required, adapted, run, result⟩ :=
    CellAwarePublicNamedSource.checkpoint_has_sufficient_fuel callableProfile first.initial.issued first.initial.extension
      prepared selected.packet.aligned fixture.ready diagnostic typing.wellFormed
      (profile.for_compilation prepared.compilation) first.start.selected
      (owner fixture.original.recipe.compiled) first.initial.caller.base.val first.initial.globalReference first.initial.keyPhysical
      first.initial.caller.physical first.initial.stable first.initial.heapTyped first.initial.argumentsTyped issued bodySelected
      first.initial.represented first.initial.heaps rfl first.start.started allocated measured
  cases adapted with
  | completed matched =>
    cases matched
    have publicResult := result.context
      (SelectedCompilationPublicReturnedValues.header_context_supports selected.packet.header selected.packet.header
        (SelectedCompilationBodyTyping.Bodies.of_program typing.wellFormed)).2
    obtain ⟨actual, generation, caller, _exported, atReturned, _related, history, registry, exportsReady⟩ :=
      CellAwarePublicNamedObservedOutput.first_success _ _ first.start.selected first.start.started
        (congrArg SourceCoreCompatibleValues.Context.registry first.initial.contextAt)
        first.initial.exportsReady first.start.atCheckpoint publicResult (run required (Nat.le_refl _)) resumed
        first.initial.caller.physical
    exact ⟨⟨{
      artifact := first.start.artifact, session := actual.session,
      mapping := mapping, world := world,
      heap := (selected.shape shape).finalHeap selected.packet.header.context
        (flagEnvironment (selected.shape shape).flag ⟨[]⟩) (flagHeap ⟨[]⟩ firstFlag) firstFlag,
      store := store, caller := caller, atSession := atReturned.2.2.2,
      atRecipe := first.start.started.recipe_eq, receiving := first.initial.receiving,
      issued := first.initial.issued, extension := .refl _, registry := registry, history := history
      }, exportsReady⟩⟩
  | rejected origin call reason stagedContext reached =>
    obtain ⟨actual, generation, exported, _atReturned⟩ :=
      CellAwarePublicNamedObservedOutput.actual_result first.start.atCheckpoint (run required (Nat.le_refl _)) resumed
    obtain ⟨payload, _extension, _slots, _encoded, decoded, _rest⟩ := exported.2
    have represented := result.2.1
    cases represented with
    | fault _ => cases decoded

variable {first : InitialForward selected shape firstFlag firstStart callableProfile}
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {entries : List RecursiveNamedPublicFunctionHistory.Entry}
  {retained : first.Retained session entries} {flag : Bool}
  {call : StartedCall session row.original.key [.bool flag] runOptions}

/-- Each actual later success keeps the previous handles and captured cells,
using the independently reconstructed Source execution at the prior heap. -/
theorem NextForward.observed_retained (next : NextForward first retained flag call)
    (typing : OriginalTyping fixture.original)
    {executionFuel outputFuel : Nat} {returned : SourceCoreExecution.Completion artifact}
    (resumed : call.checkpoint.ResumeAt executionFuel outputFuel (.succeeded returned)) :
    Nonempty (first.Retained returned.session entries) := by
  let prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued selected.input.prepared selected.packet.selected
  have diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared :=
    ⟨selected.packet.selected.diagnostics, selected.packet.selected.found, rfl⟩
  obtain ⟨profile⟩ := fixture.profiles.at_slot prepared.selected
  obtain ⟨sidecar, issued, bodySelected⟩ := selected.invocation
  obtain ⟨allocated, final, sourceTrace⟩ := selected.source_body (selected.shape shape) typing.wellFormed retained.state.heap flag
  obtain ⟨sourceSize, measured⟩ := RecursiveNamedCallBounds.FunctionOutcome.has_size (.control sourceTrace)
  obtain ⟨stagedContext, stagedOutcome, heap, capture, native, store, mapping, world, required, adapted, run, result⟩ :=
    CellAwarePublicNamedSource.checkpoint_has_sufficient_fuel callableProfile next.ready.issued next.ready.receiving.result.extension
      prepared selected.packet.aligned fixture.ready diagnostic typing.wellFormed
      (profile.for_compilation prepared.compilation) next.start.selected
      (owner fixture.original.recipe.compiled) retained.state.caller next.ready.globalReference
      (CallableIndexedOwnedPreparedPhysicalBootstrap.key_physical _ _)
      next.ready.history.physical next.ready.stable next.ready.heapTyped next.ready.argumentsTyped issued bodySelected
      next.ready.represented next.ready.history.semantic.current.2.1 rfl next.start.started allocated measured
  cases adapted with
  | completed matched =>
    cases matched
    have publicResult := result.context
      (SelectedCompilationPublicReturnedValues.header_context_supports selected.packet.header selected.packet.header
        (SelectedCompilationBodyTyping.Bodies.of_program typing.wellFormed)).2
    obtain ⟨actual, generation, caller, _exported, atReturned, _related, history, registry, exportsReady⟩ :=
      CellAwarePublicNamedObservedOutput.after_success _ _ next.start.selected next.start.started
        (congrArg SourceCoreCompatibleValues.Context.registry next.ready.contextAt)
        retained.exportsReady next.start.atCheckpoint publicResult (run required (Nat.le_refl _)) resumed
        next.ready.history
    exact ⟨⟨{
      artifact := retained.state.artifact, session := actual.session,
      mapping := mapping, world := world,
      heap := (selected.shape shape).finalHeap selected.packet.header.context
        (flagEnvironment (selected.shape shape).flag retained.state.heap)
        (flagHeap retained.state.heap flag) flag,
      store := store, caller := caller, atSession := atReturned.2.2.2,
      atRecipe := retained.state.atRecipe, receiving := next.ready.receiving,
      issued := next.ready.issued, extension := next.ready.extension, registry := registry, history := history
      }, exportsReady⟩⟩
  | rejected origin stageCall reason stagedContext reached =>
    obtain ⟨actual, generation, exported, _atReturned⟩ :=
      CellAwarePublicNamedObservedOutput.actual_result next.start.atCheckpoint (run required (Nat.le_refl _)) resumed
    obtain ⟨payload, _extension, _slots, _encoded, decoded, _rest⟩ := exported.2
    have represented := result.2.1
    cases represented with
    | fault _ => cases decoded

end Tests.SourceCoreSelectedGeneralizedLocal
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedGeneralizedLocalObservedRuntime
/-! Each runtime request constructs its independent Source continuation before
resuming, then retains the exact receipt returned by that one public action. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedGeneralizedLocal.ObservedRuntime
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open SelectedCompilationPublicSessionState (StartedCall)

variable {fixture : ProfiledFixture} {row : Row fixture.original}
  {shape : Shape row.original.function.typedBody}
  {callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true}
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}

def CertifiedSession (fixture : ProfiledFixture) (row : Row fixture.original)
    (shape : Shape row.original.function.typedBody)
    (callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true)
    {artifact : SourceCoreExecution.Artifact} (session : SourceCoreExecution.Session artifact) : Prop :=
  ∃ (selected : SelectedInventory fixture row)
    (firstStart : Started fixture.original row.original.key [.bool true])
    (first : InitialForward selected shape true firstStart callableProfile),
    Nonempty (first.Retained session [])

def Planned (fixture : ProfiledFixture) (row : Row fixture.original)
    (shape : Shape row.original.function.typedBody)
    (callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true)
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    (flag : Bool) (call : StartedCall session row.original.key [.bool flag] runOptions) : Prop :=
  ∃ (selected : SelectedInventory fixture row)
    (firstStart : Started fixture.original row.original.key [.bool true])
    (first : InitialForward selected shape true firstStart callableProfile)
    (retained : first.Retained session []), Nonempty (NextForward first retained flag call)

/-- Only the previous public history and the actual new input are used. -/
theorem plan (certified : CertifiedSession fixture row shape callableProfile session)
    (typing : OriginalTyping fixture.original) (flag : Bool)
    (call : StartedCall session row.original.key [.bool flag] runOptions) :
    Planned fixture row shape callableProfile flag call := by
  obtain ⟨selected, firstStart, first, ⟨retained⟩⟩ := certified
  exact ⟨selected, firstStart, first, retained, next_from_source first retained flag typing call⟩

/-- The observation belongs to the exact call whose Source proof was planned. -/
theorem retained {flag : Bool} {call : StartedCall session row.original.key [.bool flag] runOptions}
    (planned : Planned fixture row shape callableProfile flag call)
    (typing : OriginalTyping fixture.original)
    {executionFuel outputFuel : Nat} {returned : SourceCoreExecution.Completion artifact}
    (resumed : call.checkpoint.ResumeAt executionFuel outputFuel (.succeeded returned)) :
    CertifiedSession fixture row shape callableProfile returned.session := by
  obtain ⟨selected, firstStart, first, previous, ⟨next⟩⟩ := planned
  exact ⟨selected, firstStart, first, next.observed_retained typing resumed⟩

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def observeCall {artifact : SourceCoreExecution.Artifact} (session : SourceCoreExecution.Session artifact)
    (key : SourceCoreIndexedSession.Key) (flag : Bool) : IO (StartedCall session key [.bool flag] runOptions) := do
  match started : session.start key [.bool flag] runOptions.inputValidationFuel with
  | .error error => throw (IO.userError (reprStr error))
  | .ok checkpoint => pure ⟨checkpoint, started⟩

/-- Three calls use the actual current session and an independently constructed
Source proof before every resume. All three observed heaps retain those proofs. -/
def run : IO Unit := do
  let fixture ← compileProfiledFixture
  let row ← observeRow fixture.original "local"
  let shape ← observeShape row.original.function.typedBody
  let typing ← observeOriginalTyping fixture.original
  if callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true then
    let firstStart ← observeStarted fixture.original row.original.key [.bool true]
    have firstPlan : ∃ selected : SelectedInventory fixture row,
        Nonempty (InitialForward selected shape true firstStart callableProfile) := by
      obtain ⟨selected⟩ := fixture.inventory row typing.wellFormed
      exact ⟨selected, initial_from_source selected shape true typing firstStart callableProfile⟩
    let firstObserved ← firstStart.call.checkpoint.resumeWithReceipt 100000 10000
    match firstResult : firstObserved.val with
    | .succeeded firstReturned =>
      have firstReceipt := firstResult ▸ firstObserved.property
      have firstCertified : CertifiedSession fixture row shape callableProfile firstReturned.session := by
        obtain ⟨selected, ⟨first⟩⟩ := firstPlan
        exact ⟨selected, firstStart, first, first.observed_retained typing firstReceipt⟩
      require (firstReturned.value == .product (.word (Word.ofNatModulo 11)) (.bool true))
        "first generalized retained Source value changed"
      let secondCall ← observeCall firstReturned.session row.original.key false
      have secondPlan := plan firstCertified typing false secondCall
      let secondObserved ← secondCall.checkpoint.resumeWithReceipt 100000 10000
      match secondResult : secondObserved.val with
      | .succeeded secondReturned =>
        have secondReceipt := secondResult ▸ secondObserved.property
        have secondCertified := retained secondPlan typing secondReceipt
        require (secondReturned.value == .product (.word (Word.ofNatModulo 11)) (.bool false))
          "second generalized retained Source value changed"
        let thirdCall ← observeCall secondReturned.session row.original.key true
        have thirdPlan := plan secondCertified typing true thirdCall
        let thirdObserved ← thirdCall.checkpoint.resumeWithReceipt 100000 10000
        match thirdResult : thirdObserved.val with
        | .succeeded thirdReturned =>
          have thirdReceipt := thirdResult ▸ thirdObserved.property
          have _thirdCertified := retained thirdPlan typing thirdReceipt
          require (thirdReturned.value == .product (.word (Word.ofNatModulo 11)) (.bool true))
            "third generalized retained Source value changed"
          let heaps := [firstStart.session.heapSize, firstReturned.session.heapSize,
            secondReturned.session.heapSize, thirdReturned.session.heapSize]
          require (heaps == [2,23,44,65]) "generalized Source-certified repeated native heaps changed"
          IO.println "GENERALIZED_RETAINED_SOURCE_PUBLIC: originals1/cache1/typing1/profile1; proof before every resume"
          IO.println s!"GENERALIZED_RETAINED_SOURCE_HEAPS: {heaps}"
          IO.println "GENERALIZED_RETAINED_SOURCE_PUBLIC_PASS"
        | _ => throw (IO.userError "third generalized certified call did not succeed")
      | _ => throw (IO.userError "second generalized certified call did not succeed")
    | _ => throw (IO.userError "first generalized certified call did not succeed")
  else throw (IO.userError "generalized callable catalog disabled")

end Tests.SourceCoreSelectedGeneralizedLocal.ObservedRuntime
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedGeneralizedLocalProfile
/-! The complete original checked cache supplies the concrete Source-first
initial public proof. Repeated returned-session calls are runtime companions. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedGeneralizedLocal
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

/-- The finite scanner retains every actual cached named row. -/
def checkProfile : IO Unit := do
  let _fixture ← compileProfiledFixture
  IO.println "GENERALIZED_LOCAL_ORIGINAL_PROFILE: originals1/cache1/profile1"

/-- Original source typing and its independent execution proof are assembled
before the first target resume. Later calls reuse that exact returned session. -/
def run : IO Unit := do
  let fixture ← compileProfiledFixture
  let row ← observeRow fixture.original "local"
  let shape ← observeShape row.original.function.typedBody
  let typing ← observeOriginalTyping fixture.original
  if callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true then
    let started ← observeStarted fixture.original row.original.key [.bool true]
    have _sourceFirst : ∃ selected : SelectedInventory fixture row,
        Nonempty (InitialForward selected shape true started callableProfile) := by
      obtain ⟨selected⟩ := fixture.inventory row typing.wellFormed
      exact ⟨selected, initial_from_source selected shape true typing started callableProfile⟩
    let .outOfFuel suspended ← started.call.checkpoint.resume 0 0
      | throw (IO.userError "generalized initial zero fuel did not suspend")
    let .succeeded returned ← suspended.resume 100000 10000
      | throw (IO.userError "generalized initial public execution failed")
    require (returned.value == .product (.word (Word.ofNatModulo 11)) (.bool true))
      "generalized initial Source value changed"
    let mut session := returned.session
    let mut heaps := [started.session.heapSize, session.heapSize]
    match session.start row.original.key [.word (Word.ofNatModulo 1)] runOptions.inputValidationFuel with
    | .ok _ => throw (IO.userError "generalized raw Bool input boundary changed")
    | .error _ => pure ()
    for flag in [false,true] do
      match ← session.run row.original.key [.bool flag] runOptions with
      | .ok (.succeeded completed) =>
        require (completed.value == .product (.word (Word.ofNatModulo 11)) (.bool flag))
          "generalized retained-session Source value changed"
        session := completed.session
        heaps := heaps ++ [session.heapSize]
      | _ => throw (IO.userError "generalized retained-session invocation failed")
    require (heaps == [2,23,44,65]) "generalized exact native heaps changed"
    IO.println "GENERALIZED_LOCAL_COMPLETE_PROFILE: originals1/cache1/profile1"
    IO.println "GENERALIZED_LOCAL_SOURCE_FIRST: original typed body to actual initial public output"
    IO.println s!"GENERALIZED_LOCAL_REUSE_NATIVE_HEAPS: {heaps}"
    IO.println "GENERALIZED_LOCAL_COMPILER_PROFILE_FORWARD_PASS"
  else throw (IO.userError "generalized actual callable catalog disabled")

end Tests.SourceCoreSelectedGeneralizedLocal
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedNamedBuiltinDirectReceipts
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedNamedBuiltinDirect
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreInitialLexicalFailure
open Tests.SourceCoreCertifiedLexicalFailure (FreshIdentity)
open Tests.SourceCoreDirectIssued (ObservedNamed ObservedBuiltin observeNamed observeBuiltin)

def integerArgument : Int := 37
def convertedWord : Core.Word := Core.Word.ofIntModulo integerArgument

structure Handles (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (fresh : FreshIdentity fixture observed) where
  identity : ObservedNamed fresh.call.completion.session observed.identityRow.row.key
  builtin : ObservedBuiltin identity.completion.session
  failed : ObservedNamed builtin.completion.session observed.failedRow.row.key
  identityCheckpoint : SourceCoreExecution.Checkpoint fresh.artifact
  identityStarted : failed.completion.session.startHandlePacked identity.handle (.word seed)
    runOptions.inputValidationFuel = .ok identityCheckpoint
  builtinCheckpoint : SourceCoreExecution.Checkpoint fresh.artifact
  builtinStarted : failed.completion.session.startHandlePacked builtin.handle (.integer integerArgument)
    runOptions.inputValidationFuel = .ok builtinCheckpoint
  failedCheckpoint : SourceCoreExecution.Checkpoint fresh.artifact
  failedStarted : failed.completion.session.startHandlePacked failed.handle .unit
    runOptions.inputValidationFuel = .ok failedCheckpoint

def observeHandles {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    (fresh : FreshIdentity fixture observed) : IO (Handles fixture observed fresh) := do
  let identity ← observeNamed fresh.call.completion.session observed.identityRow.row.key
  let builtin ← observeBuiltin identity.completion.session
  let failed ← observeNamed builtin.completion.session observed.failedRow.row.key
  match identityStarted : failed.completion.session.startHandlePacked identity.handle (.word seed)
      runOptions.inputValidationFuel with
  | .error error => throw (IO.userError (reprStr error))
  | .ok identityCheckpoint =>
    match builtinStarted : failed.completion.session.startHandlePacked builtin.handle (.integer integerArgument)
        runOptions.inputValidationFuel with
    | .error error => throw (IO.userError (reprStr error))
    | .ok builtinCheckpoint =>
      match failedStarted : failed.completion.session.startHandlePacked failed.handle .unit
          runOptions.inputValidationFuel with
      | .error error => throw (IO.userError (reprStr error))
      | .ok failedCheckpoint =>
        pure ⟨identity, builtin, failed, identityCheckpoint, identityStarted,
          builtinCheckpoint, builtinStarted, failedCheckpoint, failedStarted⟩

end Tests.SourceCoreSelectedNamedBuiltinDirect
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedNamedBuiltinDirectTraces
/-! Ordinary executions of the existing lexical program are constructed from
its original source nodes and fresh allocations, before any public execution. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreSelectedNamedBuiltinDirectTraces
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreInitialLexicalFailure
open CallableIndexedOwnedFunctionValues (Header NamedSourceAt)
open RecursiveNamedPublicPhysicalSessionState (PlainValue PlainFault)

variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}

def appendWord (before : Dynamic.Heap) (value : Option Dynamic.Value) : Dynamic.Heap :=
  ⟨before.cells ++ [{ type := .word, value := value }]⟩

def nextLocation (before : Dynamic.Heap) : Dynamic.Location := ⟨before.cells.length⟩

theorem ActualHeader.identity_call
    (actual : ActualHeader fixture observed.identityRow.row)
    {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {global : Dynamic.GlobalFunction}
    (sourceAt : NamedSourceAt actual.header rawD global)
    (anchor : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram))
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap) (value : Core.Word) :
    Dynamic.CallableApplies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      anchor.function.context invocation.evidence global.evidence before (.global global)
      [.word value] (.word value) (appendWord before (some (.word value))) := by
  have parameters : actual.header.function.parameters = [observed.identityShape.binder] := by
    rw [actual.header.parameters, ← actual.header.inputs, actual.source, observed.identityShape.inputs]
  have allocated : Dynamic.Heap.Allocates before observed.identityShape.binder.scheme.body
      (some (.word value)) (nextLocation before) (appendWord before (some (.word value))) := by
    rw [observed.identityShape.binderScheme]
    exact .append
  have bound : Dynamic.BindersAllocate [] before actual.header.function.parameters [.word value]
      [(observed.identityShape.binder.id, nextLocation before)] (appendWord before (some (.word value))) := by
    rw [parameters]
    exact .cons allocated (.nil _ _)
  have read : Dynamic.ExpressionEvaluates (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      actual.header.context actual.header.function.evidence actual.header.function.source
      [(observed.identityShape.binder.id, nextLocation before)] (appendWord before (some (.word value)))
      observed.identityShape.read.id (.word value) (appendWord before (some (.word value))) := by
    apply Dynamic.ExpressionEvaluates.intro
      (lookupExpression?_sound (actual.source.symm ▸ observed.identityShape.readFound))
    · rw [observed.identityShape.readForm]
      exact .local (by rw [observed.identityShape.readRequirements, observed.identityShape.readCoercions]; rfl)
        .head allocated.reads_new rfl rfl
    · rw [observed.identityShape.readCoercions]; exact .nil
  have executed : Dynamic.FunctionStatementsExecute (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      actual.header.context actual.header.function.evidence actual.header.function.source
      [(observed.identityShape.binder.id, nextLocation before)] (appendWord before (some (.word value)))
      actual.header.function.body actual.header.context (.returned (.word value))
      (appendWord before (some (.word value))) := by
    rw [actual.identity_statements]
    have found := lookupStatement?_sound (actual.source.symm ▸ observed.identityShape.statementFound)
    exact .singleton found (by rw [observed.identityShape.statementForm]; intro expression impossible; cases impossible)
      (.returnValue found observed.identityShape.statementForm read)
  have body := sourceAt.frame.body_of_trace actual.header.extended bound
    (FunctionCallBody.Trace.returned executed)
  cases body with
  | value invoked =>
    refine .global sourceAt.frame.instantiated rfl ?_ ?_
    · exact sourceAt.dictionary ▸ sourceAt.frame.covers
    · exact sourceAt.dictionary ▸ invoked

private theorem failed_extension (actual : ActualHeader fixture observed.failedRow.row) :
    ∃ finalContext, BinderExtends actual.header.function.source.owner actual.header.context
      observed.failedShape.binder finalContext := by
  obtain ⟨facts, final, typed, roots, complete⟩ := actual.aligned.bodyTyped
  rw [actual.source, observed.failedShape.roots] at typed
  simp only [List.filterMap_cons, List.filterMap_nil] at typed
  have unique : NodeOccurrencesUnique observed.failedRow.row.function.typedBody := actual.source ▸ actual.header.unique
  cases typed with
  | cons head tail =>
    cases head with
    | letUninitialized contains form mono generalized extended type =>
      have same := Option.some.inj ((lookupStatement?_complete unique contains).symm.trans observed.failedShape.declaredFound)
      cases same
      rw [observed.failedShape.declaredForm] at form
      cases (StatementForm.letDecl.inj form).1
      exact ⟨_, actual.source.symm ▸ extended⟩
    | _ =>
      have same := Option.some.inj ((lookupStatement?_complete unique (by assumption)).symm.trans observed.failedShape.declaredFound)
      cases same
      simp_all [observed.failedShape.declaredForm]

theorem ActualHeader.failed_call
    (actual : ActualHeader fixture observed.failedRow.row)
    {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {global : Dynamic.GlobalFunction}
    (sourceAt : NamedSourceAt actual.header rawD global)
    (anchor : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram))
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap) :
    Dynamic.CallableFaults (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      anchor.function.context invocation.evidence global.evidence before (.global global) []
      (.uninitializedLocation (nextLocation before)) (appendWord before none) := by
  have parameters : actual.header.function.parameters = [] := by
    rw [actual.header.parameters, ← actual.header.inputs, actual.source, observed.failedShape.inputs]
  have bound : Dynamic.BindersAllocate [] before actual.header.function.parameters [] [] before := by
    rw [parameters]; exact .nil _ _
  have allocated : Dynamic.Heap.Allocates before observed.failedShape.binder.scheme.body none
      (nextLocation before) (appendWord before none) := by
    rw [observed.failedShape.binderScheme]; exact .append
  obtain ⟨finalContext, extension⟩ := failed_extension actual
  have read : Dynamic.ExpressionFaults (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      finalContext actual.header.function.evidence actual.header.function.source
      [(observed.failedShape.binder.id, nextLocation before)] (appendWord before none)
      observed.failedShape.read.id (.uninitializedLocation (nextLocation before)) (appendWord before none) := by
    apply Dynamic.ExpressionFaults.form
      (lookupExpression?_sound (actual.source.symm ▸ observed.failedShape.readFound))
    rw [observed.failedShape.readForm]
    apply Dynamic.ExpressionFormFaults.localUninitialized (owned := [])
      (cell := {type := observed.failedShape.binder.scheme.body, value := none})
      (by rw [observed.failedShape.readRequirements, observed.failedShape.readCoercions]; rfl)
      .head allocated.reads_new rfl rfl
    rw [observed.failedShape.binderScheme]
    intro ⟨key, value, impossible⟩
    cases impossible
  have executed : Dynamic.FunctionStatementsFault (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      actual.header.context actual.header.function.evidence actual.header.function.source [] before
      actual.header.function.body finalContext (.uninitializedLocation (nextLocation before)) (appendWord before none) := by
    rw [actual.failed_statements]
    exact .tail
      (.letUninitialized (lookupStatement?_sound (actual.source.symm ▸ observed.failedShape.declaredFound))
        observed.failedShape.declaredForm (by rw [observed.failedShape.binderScheme]; rfl) extension allocated)
      (.singleton (.returnValue (lookupStatement?_sound (actual.source.symm ▸ observed.failedShape.statementFound))
        observed.failedShape.statementForm read))
  have body := sourceAt.frame.body_of_trace actual.header.extended bound
    (FunctionCallBody.Trace.fault executed)
  cases body with
  | fault failed =>
    exact .globalBody sourceAt.frame.instantiated rfl (sourceAt.dictionary ▸ failed)

end Tests.SourceCoreSelectedNamedBuiltinDirectTraces
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedNamedBuiltinDirectSourceFirst
/-! Genuine issuance authenticates three retained handles in one physical
history. The earlier completed identity call supplies that starting state.
Every direct ordinary trace below is built independently from Source nodes,
allocation, reads, and the builtin relation before any direct call completes. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 6000000
namespace Tests.SourceCoreSelectedNamedBuiltinDirect
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreInitialLexicalFailure
open Tests.SourceCoreSelectedNamedBuiltinDirectTraces
open Tests.SourceCoreCertifiedLexicalFailure (FreshIdentity)
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Issued Inventory headers)
open RecursiveNamedPublicFunctionHistory (Entry)
open SelectedCompilationCertifiedPublicSession (Profiled)

variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}

def ValueConclusion (issued : Profiled fixture.recipe)
    {anchor : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry} (state : issued.toIssued.State anchor session entries) (entry : Entry)
    (checkpoint : SourceCoreExecution.Checkpoint artifact) (invocation : Staging.Recursive.Scope)
    (arguments : List Dynamic.Value) (value : RecursiveNamedPublicScalarResults.ScalarOutput) (after : Dynamic.Heap) : Prop :=
  (Staging.Recursive.Applies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
    (SelectedCompilationPhysicalProgramSupport.stages fixture.recipe.compiled) invocation anchor.function.context
    state.heap entry.source arguments (.value value.source) after ∧
    SelectedCompilationPublicSessionDirectScalarForward.ForwardAt issued.catalog.rows anchor issued.initial
      issued.support.profile fixture.recipe entries value checkpoint after) ∨
  SelectedCompilationStageClosedDirectForward.StageStopped issued state entry checkpoint invocation arguments

def FaultConclusion (issued : Profiled fixture.recipe)
    {anchor : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry} (state : issued.toIssued.State anchor session entries) (entry : Entry)
    (checkpoint : SourceCoreExecution.Checkpoint artifact) (invocation : Staging.Recursive.Scope)
    (arguments : List Dynamic.Value) (reason : Dynamic.SemanticFault) (after : Dynamic.Heap) : Prop :=
  (Staging.Recursive.Applies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
    (SelectedCompilationPhysicalProgramSupport.stages fixture.recipe.compiled) invocation anchor.function.context
    state.heap entry.source arguments (.fault (.semantic reason)) after ∧
    SelectedCompilationPublicSessionDirectFailureForward.FailureForwardAt issued.catalog.rows anchor issued.initial
      issued.support.profile fixture.recipe entries (.semantic reason) checkpoint after) ∨
  SelectedCompilationStageClosedDirectForward.StageStopped issued state entry checkpoint invocation arguments

structure Meaning (stages : ObservedStages fixture observed.identityRow)
    (fresh : FreshIdentity fixture observed) (calls : Handles fixture observed fresh) where
  issued : Profiled fixture.recipe
  anchor : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)
  identity : Entry
  builtin : Entry
  failed : Entry
  identityHandle : identity.handle = calls.identity.handle
  builtinHandle : builtin.handle = calls.builtin.handle
  failedHandle : failed.handle = calls.failed.handle
  identityType : identity.sourceType = .function .word .word
  builtinType : builtin.sourceType = .function .integer .word
  failedType : failed.sourceType = .function .unit .word
  builtinSource : builtin.source = .builtin ⟨.wordFromInteger⟩
  state : issued.toIssued.State anchor calls.failed.completion.session [identity, builtin, failed]
  identityPlain : Dynamic.CallableApplies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
    anchor.function.context (RecursiveStageRegistry.scope stages.sidecar [] anchor.function).evidence
    (Staging.Recursive.callableEvidence identity.source) state.heap identity.source [.word seed] (.word seed)
    (appendWord state.heap (some (.word seed)))
  builtinPlain : Dynamic.CallableApplies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
    anchor.function.context (RecursiveStageRegistry.scope stages.sidecar [] anchor.function).evidence
    (Staging.Recursive.callableEvidence builtin.source) state.heap builtin.source [.integer integerArgument]
    (.word convertedWord) state.heap
  failedPlain : Dynamic.CallableFaults (Program.ofChecked fixture.recipe.compiled.sourceProgram)
    anchor.function.context (RecursiveStageRegistry.scope stages.sidecar [] anchor.function).evidence
    (Staging.Recursive.callableEvidence failed.source) state.heap failed.source []
    (.uninitializedLocation (nextLocation state.heap)) (appendWord state.heap none)
  identityForward : ValueConclusion issued state identity calls.identityCheckpoint
    (RecursiveStageRegistry.scope stages.sidecar [] anchor.function) [.word seed] (.word seed)
    (appendWord state.heap (some (.word seed)))
  builtinForward : ValueConclusion issued state builtin calls.builtinCheckpoint
    (RecursiveStageRegistry.scope stages.sidecar [] anchor.function) [.integer integerArgument]
    (.word convertedWord) state.heap
  failedForward : FaultConclusion issued state failed calls.failedCheckpoint
    (RecursiveStageRegistry.scope stages.sidecar [] anchor.function) []
    (.uninitializedLocation (nextLocation state.heap)) (appendWord state.heap none)
  builtinOutput :
    (Staging.Recursive.Applies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      (SelectedCompilationPhysicalProgramSupport.stages fixture.recipe.compiled)
      (RecursiveStageRegistry.scope stages.sidecar [] anchor.function) anchor.function.context
      state.heap builtin.source [.integer integerArgument] (.value (.word convertedWord)) state.heap ∧
      SelectedCompilationStageClosedDirectForward.Output.ForwardAt issued.catalog.rows anchor issued.initial
        issued.support.profile fixture.recipe [identity, builtin, failed] .word calls.builtinCheckpoint
        (.word convertedWord) state.heap) ∨
    SelectedCompilationStageClosedDirectForward.StageStopped issued state builtin calls.builtinCheckpoint
      (RecursiveStageRegistry.scope stages.sidecar [] anchor.function) [.integer integerArgument]

private theorem packet_type (issued : Profiled fixture.recipe) {input : Input fixture.recipe.compiled}
    (packet : Issued input) :
    packet.header.named.specialized.function.type =
      .function (TypeSystem.Ty.productMany packet.header.types) packet.header.function.resultType := by
  obtain ⟨facts, certificate⟩ := SelectedCompilationNamedArgumentRows.certified_at packet.sourceAt
    issued.support.bodyTyping
    (CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued input.prepared packet.selected) packet.aligned
  have shape := certificate.callable_type
  change packet.header.named.specialized.function.type = _ at shape
  rw [← packet.sourceAt.frame.result] at shape
  exact shape

private theorem packet_at (issued : Profiled fixture.recipe) {signature : ProgramFunctionSignature}
    (row : ObservedRow fixture signature) :
    ∃ input : Input fixture.recipe.compiled, ∃ packet : Issued input,
      Inventory.HasRow packet issued.catalog.rows ∧
      ∃ actual : ActualHeader fixture row.row, actual.header = packet.header := by
  obtain ⟨selected, same⟩ := Tests.SourceCoreCertifiedLexicalFailure.eligible_row row
  obtain ⟨input, packet, member, _row, _index, named⟩ := issued.catalog.packet_at selected.cached selected.eligible
  obtain ⟨actual, equality⟩ := Tests.SourceCoreCertifiedLexicalFailure.header_of_member row issued.catalog.rows
    (Inventory.header_member member) ((congrArg (·.specialized) (packet.aligned.named.trans named)).trans same)
  exact ⟨input, packet, member, actual, equality⟩

theorem meaning (profile : CompilerProgramStaticProfile.StaticProfile fixture.recipe.compiled)
    (stages : ObservedStages fixture observed.identityRow)
    (fresh : FreshIdentity fixture observed) (calls : Handles fixture observed fresh) :
    Nonempty (Meaning stages fresh calls) := by
  obtain ⟨issued, ⟨before⟩⟩ := Tests.SourceCoreSelectedLexicalFailure.fresh_meaning profile stages fresh
  obtain ⟨identityInput, identityPacket, identityMember, identityActual, identityEq⟩ := packet_at issued observed.identityRow
  obtain ⟨failedInput, failedPacket, failedMember, failedActual, failedEq⟩ := packet_at issued observed.failedRow
  have identityKey : identityPacket.header.named.signature.key = observed.identityRow.row.key := by
    rw [← identityEq]; exact identityActual.key
  have failedKey : failedPacket.header.named.signature.key = observed.failedRow.row.key := by
    rw [← failedEq]; exact failedActual.key
  have identityType : identityPacket.header.named.specialized.function.type = .function .word .word := by
    rw [packet_type issued identityPacket, ← identityEq,
      Tests.SourceCoreSelectedLexicalSourceStart.identity_types identityActual, identityActual.identity_result_type]
    rfl
  have failedType : failedPacket.header.named.specialized.function.type = .function .unit .word := by
    rw [packet_type issued failedPacket, ← failedEq,
      Tests.SourceCoreSelectedLexicalSourceStart.failed_types failedActual, failedActual.failed_result_type]
    rfl
  obtain ⟨identity, identityTyped, identitySource, identityHandle, identityHandleType, namedState, _namedHeap⟩ :=
    SelectedCompilationPublicSessionIssuance.State.remember_named issued.support issued.prepared before.after
      identityPacket identityMember (by simpa only [identityKey] using calls.identity.issued) calls.identity.returned
  obtain ⟨builtin, builtinTyped, builtinSource, builtinHandle, builtinHandleType, builtinState, _builtinHeap⟩ :=
    SelectedCompilationPublicSessionIssuance.State.remember_builtin issued.prepared namedState
      .wordFromInteger calls.builtin.issued calls.builtin.returned
  obtain ⟨failed, failedTyped, failedSource, failedHandle, failedHandleType, state, _failedHeap⟩ :=
    SelectedCompilationPublicSessionIssuance.State.remember_named issued.support issued.prepared builtinState
      failedPacket failedMember (by simpa only [failedKey] using calls.failed.issued) calls.failed.returned
  have identityTyped := identityTyped.trans identityType
  have failedTyped := failedTyped.trans failedType
  have ready := calls.failed.issued.exportsReady (calls.builtin.issued.exportsReady
    (calls.identity.issued.exportsReady (fresh.call.executed.exportsReady
      ((SourceCoreExecution.Bootstrap.ReadyAt.single fresh.ready).exportsReady fresh.authority))))
  let invocation := RecursiveStageRegistry.scope stages.sidecar [] before.initial.header.function
  have identityPlain := Tests.SourceCoreSelectedNamedBuiltinDirectTraces.ActualHeader.identity_call identityActual (identityEq.symm ▸ identityPacket.sourceAt)
    before.initial.header invocation state.heap seed
  have failedPlain := Tests.SourceCoreSelectedNamedBuiltinDirectTraces.ActualHeader.failed_call failedActual (failedEq.symm ▸ failedPacket.sourceAt)
    before.initial.header invocation state.heap
  rw [identityEq] at identityPlain
  rw [failedEq] at failedPlain
  change Dynamic.CallableApplies _ _ _ (Staging.Recursive.callableEvidence (.global _)) _ _ _ _ _ at identityPlain
  change Dynamic.CallableFaults _ _ _ (Staging.Recursive.callableEvidence (.global _)) _ _ _ _ _ at failedPlain
  rw [← identitySource] at identityPlain
  rw [← failedSource] at failedPlain
  have builtinPlain : Dynamic.CallableApplies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      before.initial.header.function.context invocation.evidence
      (Staging.Recursive.callableEvidence builtin.source) state.heap builtin.source [.integer integerArgument]
      (.word convertedWord) state.heap := by
    rw [builtinSource]
    exact .builtin (.wordFromInteger integerArgument)
  have identityInput : RecursiveNamedPublicFunctionHistoryInputs.Input [identity, builtin, failed]
      before.initial.header.function.context .word (.word seed) (.word seed) :=
    .data ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩
      ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩
  have builtinInput : RecursiveNamedPublicFunctionHistoryInputs.Input [identity, builtin, failed]
      before.initial.header.function.context .integer (.integer integerArgument) (.integer integerArgument) :=
    .data ⟨.integer integerArgument, by simp [SourceCoreIndexedSession.DataInput.publicValue], .integer integerArgument⟩
      ⟨.integer integerArgument, by simp [SourceCoreIndexedSession.DataInput.publicValue], .integer integerArgument⟩
  have failedInput : RecursiveNamedPublicFunctionHistoryInputs.Input [identity, builtin, failed]
      before.initial.header.function.context .unit .unit .unit :=
    .data ⟨.unit, by simp [SourceCoreIndexedSession.DataInput.publicValue], .unit⟩
      ⟨.unit, by simp [SourceCoreIndexedSession.DataInput.publicValue], .unit⟩
  have identityStarted := identityHandle.symm ▸ calls.identityStarted
  have builtinStarted := builtinHandle.symm ▸ calls.builtinStarted
  have failedStarted := failedHandle.symm ▸ calls.failedStarted
  have faultArity : RecursivePublicCallableArity.Arity (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      failed.source 0 := by
    rw [failedSource]
    have actual := RecursivePublicCallableArity.Arity.global failedPacket.sourceAt.frame.instantiated
    have inputs : failedPacket.header.sourceBody.source.inputs = [] := by
      rw [← failedPacket.sourceAt.frame.source, ← failedEq, failedActual.source, observed.failedShape.inputs]
    simpa only [inputs, List.length_nil] using actual
  refine ⟨{
    issued := issued, anchor := before.initial.header,
    identity := identity, builtin := builtin, failed := failed,
    identityHandle := identityHandle, builtinHandle := builtinHandle, failedHandle := failedHandle,
    identityType := identityTyped, builtinType := builtinTyped, failedType := failedTyped,
    builtinSource := builtinSource, state := state,
    identityPlain := identityPlain, builtinPlain := builtinPlain, failedPlain := failedPlain,
    identityForward := ?_, builtinForward := ?_, failedForward := ?_, builtinOutput := ?_ }⟩
  · exact SelectedCompilationStageClosedDirectForward.scalar issued state identity (by simp)
      identityTyped identityInput identityStarted ready (Dynamic.ValuesPack.singleton (.word seed))
      (.word seed) rfl (by rw [identityHandle]; exact identityHandleType.trans identityType) identityPlain
  · exact SelectedCompilationStageClosedDirectForward.scalar issued state builtin (by simp)
      builtinTyped builtinInput builtinStarted ready (Dynamic.ValuesPack.singleton (.integer integerArgument))
      (.word convertedWord) rfl (by rw [builtinHandle]; exact builtinHandleType) builtinPlain
  · exact SelectedCompilationStageClosedDirectForward.fault issued state failed (by simp)
      failedTyped failedInput failedStarted ready Dynamic.ValuesPack.nil faultArity
      (.uninitializedLocation (nextLocation state.heap)) failedPlain
  · exact SelectedCompilationStageClosedDirectForward.output issued state builtin (by simp)
      builtinTyped builtinInput builtinStarted ready (Dynamic.ValuesPack.singleton (.integer integerArgument)) builtinPlain

end Tests.SourceCoreSelectedNamedBuiltinDirect
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedNamedBuiltinDirectRuntime
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedNamedBuiltinDirect
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreInitialLexicalFailure

private def require (condition : Bool) (message : String) : IO Unit :=
  if condition then pure () else throw (IO.userError message)

def run : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeProgram fixture
  let profile ← Tests.SourceCoreSelectedLexicalFailure.observeProfile fixture
  let stages ← observeStages fixture observed.identityRow
  let fresh ← Tests.SourceCoreCertifiedLexicalFailure.observeFreshIdentity fixture observed
  let calls ← observeHandles observed fresh
  have _sourceFirst := meaning profile stages fresh calls
  let .outOfFuel namedSuspended ← calls.identityCheckpoint.resume 0 0
    | throw (IO.userError "named direct call did not suspend at zero fuel")
  let .succeeded named ← namedSuspended.resume 100000 1000
    | throw (IO.userError "named direct Source identity did not complete")
  require (named.value == .word seed) "named direct Source identity result changed"
  let .outOfFuel builtinSuspended ← calls.builtinCheckpoint.resume 0 0
    | throw (IO.userError "builtin direct call did not suspend at zero fuel")
  let .succeeded builtin ← builtinSuspended.resume 100000 1000
    | throw (IO.userError "builtin direct Source conversion did not complete")
  require (builtin.value == .word convertedWord) "builtin direct Source conversion result changed"
  let .outOfFuel failedSuspended ← calls.failedCheckpoint.resume 0 0
    | throw (IO.userError "named direct failure did not suspend at zero fuel")
  let .failed reason after ← failedSuspended.resume 100000 0
    | throw (IO.userError "named direct absent read did not fail")
  let .ok (some diagnostic) := after.diagnostic observed.failedRow.row.key reason
    | throw (IO.userError "named direct absent-read diagnostic missing")
  require (match diagnostic.error with | .uninitializedLocal _ => true | _ => false)
    "named direct semantic fault changed"
  let .ok continuedCheckpoint := after.startHandlePacked calls.identity.handle (.word seed)
      runOptions.inputValidationFuel
    | throw (IO.userError "failed direct session lost the earlier named handle")
  let .succeeded continued ← continuedCheckpoint.resume 100000 1000
    | throw (IO.userError "earlier named handle could not continue after failure")
  require (continued.value == .word seed) "retained named continuation changed"
  let .ok convertedCheckpoint := continued.session.startHandlePacked calls.builtin.handle (.integer integerArgument)
      runOptions.inputValidationFuel
    | throw (IO.userError "continuation lost the earlier builtin handle")
  let .succeeded converted ← convertedCheckpoint.resume 100000 1000
    | throw (IO.userError "earlier builtin handle could not continue after failure")
  require (converted.value == .word convertedWord) "retained builtin continuation changed"
  require (calls.identity.completion.session.heapSize == fresh.call.completion.session.heapSize &&
    calls.builtin.completion.session.heapSize == calls.identity.completion.session.heapSize &&
    calls.failed.completion.session.heapSize == calls.builtin.completion.session.heapSize)
    "genuine handle issuance changed the existing runtime heap"
  require ([fresh.call.completion.session.heapSize, named.session.heapSize,
    builtin.session.heapSize, after.heapSize, continued.session.heapSize, converted.session.heapSize]
    == [6, 9, 6, 9, 12, 12]) "direct Source-first exact heap sizes changed"
  require (fixture.recipe.compiled.indexed.base.functions.length == 2)
    "original lexical cache changed"
  IO.println s!"SOURCE_FIRST_DIRECT_NAMED_BUILTIN_PASS: original checker1000/compiler100; retained named identity37, builtin integer37-to-word37 and named absent-cell semantic fault; ordinary traces precede direct execution; closed scalar/full-output/fault alternatives; zero-fuel resume; retained named+builtin reuse after failure; heaps{[fresh.call.completion.session.heapSize, named.session.heapSize, builtin.session.heapSize, after.heapSize, continued.session.heapSize, converted.session.heapSize]}"

end Tests.SourceCoreSelectedNamedBuiltinDirect
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedOrdinaryStageLift
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedOrdinaryStageLift
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering

def workspace : Workspace.RawWorkspace := {
  entry := "main.solc"
  externalLibraries := []
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "function stagedFactory() returns (function(Word) returns (Word)) { return lam(comptime item: Word) -> Word { return item; }; }",
    "function ordinaryFactory() returns (function(Word) returns (Word)) { return lam(item: Word) -> Word { return item; }; }",
    "function touch(value: Word) returns (Word) { let copy = value; return copy; }",
    "function invoke(f: function(Word) returns (Word), value: Word) returns (Word) { return f(touch(value)); }"
  ] }]
}

def options : SourceCompiler.Options := {
  checkingFuel := 1000, compilationFuel := 1000, specializationBudget := 512
}

private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue

private def success {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreExecution.Key)
    (arguments : List SourceCorePublicValues.Value) : IO (SourceCoreExecution.Completion artifact) := do
  let outcome ← get "ordinary stage public startup" (← session.run key arguments { executionFuel := 100000 })
  match outcome with
  | .succeeded completed => pure completed
  | _ => throw (IO.userError "ordinary stage public success missing")

private def reject {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreExecution.Key)
    (handle : SourceCorePublicValues.Handle) (seed : Word) : IO (SourceCoreExecution.Session artifact) := do
  let started ← get "ordinary stage rejection startup" (session.start key [.function handle, .word seed])
  let .outOfFuel suspended ← started.resume 0 0
    | throw (IO.userError "ordinary stage zero fuel did not suspend")
  let .failed reason after ← suspended.resume 100000 0
    | throw (IO.userError "ordinary stage rejection did not retain a session")
  let some diagnostic ← get "ordinary stage diagnostic" (after.diagnostic key reason)
    | throw (IO.userError "ordinary stage rejection diagnostic missing")
  require (match diagnostic.error with
    | .comptimeArgumentStageMismatch _ _ 0 _ _ => true
    | _ => false) "ordinary stage rejection changed its guard reason"
  pure after

def run : IO Unit := do
  match checked : checkProgram workspace options.checkingFuel with
  | .error errors => throw (IO.userError s!"ordinary stage checking: {reprStr errors}")
  | .ok program =>
    let roots ← ["stagedFactory", "ordinaryFactory", "invoke"].mapM (SourceCoreUnifiedCorpusSupport.key program)
    match generated : SourceCoreCompiler.compileChecked program
        (roots.map (fun key => .declaration key.declaration)) options with
    | .error error => throw (IO.userError s!"ordinary stage compilation: {reprStr error}")
    | .ok source =>
      match present : source.artifact? with
      | none => throw (IO.userError "ordinary stage artifact missing")
      | some cached =>
        have sameProgram : cached.sourceProgram = program :=
          (source.artifact_fields present).1.trans
            (SourceCoreCompiler.compileChecked_program generated)
        have original : checkProgram workspace options.checkingFuel = .ok cached.sourceProgram := by
          rw [sameProgram]
          exact checked
        let some profile := SelectedCompilationCompilerStaticProfile.validateCheckedProfile cached original
          | throw (IO.userError "ordinary stage selected profile rejected")
        have _bodyTyping := SelectedCompilationCheckedBodyTyping.of_checked original profile
        let [stagedKey, ordinaryKey, invokeKey] := roots
          | throw (IO.userError "ordinary stage root order changed")
        let prepared ← get "ordinary stage public preparation" (SourceCoreExecution.prepare source)
        let artifact ← prepared.open
        let bootstrap ← artifact.bootstrap
        let .ready initial := bootstrap.resume 100000
          | throw (IO.userError "ordinary stage bootstrap did not complete")
        let staged ← success initial stagedKey []
        let .function stagedHandle := staged.value
          | throw (IO.userError "ordinary stage closure handle missing")
        let failed ← reject staged.session invokeKey stagedHandle (Word.ofNatModulo 17)
        let ordinary ← success failed ordinaryKey []
        let .function ordinaryHandle := ordinary.value
          | throw (IO.userError "ordinary closure handle missing")
        let accepted ← success ordinary.session invokeKey [.function ordinaryHandle, .word (Word.ofNatModulo 37)]
        require (accepted.value == .word (Word.ofNatModulo 37)) "ordinary closure returned the wrong result"
        let repeated ← reject accepted.session invokeKey stagedHandle (Word.ofNatModulo 61)
        let continued ← success repeated invokeKey [.function ordinaryHandle, .word (Word.ofNatModulo 89)]
        require (continued.value == .word (Word.ofNatModulo 89)) "ordinary closure lost after repeated rejection"
        require (cached.indexed.base.functions.length == 4) "ordinary stage selected cache changed"
        require ([initial.heapSize, staged.session.heapSize, failed.heapSize, ordinary.session.heapSize,
          accepted.session.heapSize, repeated.heapSize, continued.session.heapSize] == [5, 5, 11, 11, 26, 32, 47])
          "ordinary stage guard ran argument effects or changed the retained heap"
        IO.println "ORDINARY_STAGE_PROFILE_PASS: checked profile, closure guard rejection, exact heaps, zero-fuel resume, retained handles and continuation"

end Tests.SourceCoreSelectedOrdinaryStageLift
end
