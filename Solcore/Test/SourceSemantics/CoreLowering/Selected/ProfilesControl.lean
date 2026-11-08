import Solcore.SourceSemantics.CoreLowering.PublicOutputs
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.NamedAdmission
import Solcore.SourceSemantics.CoreLowering.PublicSessions
import Solcore.SourceSemantics.CoreLowering.PublicSupport
import Solcore.Test.SourceSemantics.CoreLowering.UnifiedCorpusSupport
import Solcore.SourceSemantics.CoreLowering.Internal.Accepted.ScopedSourceBodies
import Solcore.Test.SourceSemantics.CoreLowering.Named.Branches

/-!
# Selected control profile tests

Selected profiles of loops, matches and primitives.
-/

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedLoopSource
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreSelectedLoop
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedFunctionValues (Header NamedSourceAt)

structure Shape (source : TypedSource) where
  binder : TypedBinder
  copy : TypedBinder
  first : ExpressionNode
  condition : ExpressionNode
  breaking : StatementNode
  loop : StatementNode
  second : ExpressionNode
  returned : StatementNode
  inputs : source.inputs = [binder]
  binderType : binder.scheme = .mono .word
  copyType : copy.scheme = .mono .word
  roots : source.roots = [.statement loop.id, .statement returned.id]
  firstFound : source.lookupExpression? first.id = some first
  firstForm : first.form = .reference binder.name (.local binder.id)
  firstRequirements : first.requirements = []
  firstCoercions : first.coercions = []
  conditionFound : source.lookupExpression? condition.id = some condition
  conditionForm : condition.form = .reference "true" (.builtinBoolean true)
  conditionRequirements : condition.requirements = []
  conditionCoercions : condition.coercions = []
  breakingFound : source.lookupStatement? breaking.id = some breaking
  breakingForm : breaking.form = .breakStmt
  loopFound : source.lookupStatement? loop.id = some loop
  loopForm : loop.form = .forLoop [.letDecl copy (some first.id)] condition.id [] [breaking.id]
  secondFound : source.lookupExpression? second.id = some second
  secondForm : second.form = .reference binder.name (.local binder.id)
  secondRequirements : second.requirements = []
  secondCoercions : second.coercions = []
  returnedFound : source.lookupStatement? returned.id = some returned
  returnedForm : returned.form = .returnStmt (some second.id)

def inputHeap (word : Word) : Dynamic.Heap := ⟨[{type := .word, value := some (.word word)}]⟩
def sourceHeap (word : Word) : Dynamic.Heap := ⟨[{type := .word, value := some (.word word)}, {type := .word, value := some (.word word)}]⟩

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

/-- The loop's original Source typing supplies its genuine lexical extension. -/
private theorem header_extension (certified : SelectedCompilationNamedSourceTyping.Certified header) :
    ∃ loopContext, BinderExtends header.function.source.owner header.context shape.copy loopContext := by
  obtain ⟨final, facts, typed, completes⟩ := certified.statements
  have roots : header.function.body = [shape.loop.id, shape.returned.id] :=
    roots_injective (header.agreement.roots.symm.trans shape.roots)
  rw [roots] at typed
  cases typed with
  | cons head tail =>
    obtain ⟨node, contains, formTyped⟩ := Dynamic.StatementHasType.formTyping head
    cases Option.some.inj ((lookupStatement?_complete header.unique contains).symm.trans shape.loopFound)
    rw [shape.loopForm] at formTyped
    cases formTyped with
    | forLoop init condition body post =>
      cases init with
      | cons head tail =>
        cases head with
        | letInitialized _ _ _ extension => exact ⟨_, extension⟩
        | letInitializedGeneralized poly _ _ _ _ => exact False.elim (poly (by rw [shape.copyType]; rfl))

include shape in
/-- Evaluate the initializer, enter a true for-loop, break, restore the outer
scope and return its original parameter. No public execution is a premise. -/
theorem ordinary_call (certified : SelectedCompilationNamedSourceTyping.Certified header)
    {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {global : Dynamic.GlobalFunction}
    (sourceAt : NamedSourceAt header rawD global) (invocation : Staging.Recursive.Scope) (word : Word) :
    RecursiveNamedPublicPhysicalSessionState.PlainValue header header invocation ⟨[]⟩ [.word word]
      (.word word) (sourceHeap word) := by
  have params : header.function.parameters = [shape.binder] :=
    header.parameters.trans (header.inputs.symm.trans shape.inputs)
  have allocated : Dynamic.Heap.Allocates ⟨[]⟩ shape.binder.scheme.body
      (some (.word word)) ⟨0⟩ (inputHeap word) := by
    rw [shape.binderType]
    exact .append
  have bound : Dynamic.BindersAllocate [] ⟨[]⟩ header.function.parameters [.word word]
      [(shape.binder.id, ⟨0⟩)] (inputHeap word) := by
    rw [params]
    exact .cons allocated (.nil _ _)
  have roots : header.function.body = [shape.loop.id, shape.returned.id] :=
    roots_injective (header.agreement.roots.symm.trans shape.roots)
  have read (node : ExpressionNode) (found : header.function.source.lookupExpression? node.id = some node)
      (form : node.form = .reference shape.binder.name (.local shape.binder.id))
      (requirements : node.requirements = []) (coercions : node.coercions = [])
      (heap : Dynamic.Heap) (reads : Dynamic.Heap.Reads heap ⟨0⟩ ⟨.word, some (.word word), none⟩) :
      Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram)
        header.context header.function.evidence header.function.source [(shape.binder.id, ⟨0⟩)]
        heap node.id (.word word) heap := by
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound found)
    · rw [form]
      exact .local (by rw [requirements, coercions]; rfl) .head reads rfl rfl
    · rw [coercions]; exact .nil
  obtain ⟨loopContext, extension⟩ := header_extension header shape certified
  have initial : Dynamic.ForItemsExecute (Program.ofChecked compiled.sourceProgram) header.context
      header.function.evidence header.function.source [(shape.binder.id, ⟨0⟩)] (inputHeap word)
      [.letDecl shape.copy (some shape.first.id)] loopContext
      [(shape.copy.id, ⟨1⟩), (shape.binder.id, ⟨0⟩)] (sourceHeap word) := by
    exact .cons (.letInitialized
      (read shape.first shape.firstFound shape.firstForm shape.firstRequirements shape.firstCoercions
        (inputHeap word) (by exact .intro .head))
      (by rw [shape.copyType]; rfl) extension (by rw [shape.copyType]; exact .append)) .nil
  have condition : Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram)
      loopContext header.function.evidence header.function.source
      [(shape.copy.id, ⟨1⟩), (shape.binder.id, ⟨0⟩)] (sourceHeap word) shape.condition.id (.bool true) (sourceHeap word) := by
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound shape.conditionFound)
    · rw [shape.conditionForm]
      exact .builtinBoolean (by rw [shape.conditionRequirements, shape.conditionCoercions]; rfl)
    · rw [shape.conditionCoercions]; exact .nil
  have body : Dynamic.FunctionStatementsExecute (Program.ofChecked compiled.sourceProgram)
      header.context header.function.evidence header.function.source [(shape.binder.id, ⟨0⟩)] (inputHeap word)
      header.function.body header.context (.returned (.word word)) (sourceHeap word) := by
    rw [roots]
    apply Dynamic.FunctionStatementsExecute.cons
    · exact .forLoop (lookupStatement?_sound shape.loopFound) shape.loopForm initial
        (.breaks condition (.terminal (.breakStmt (lookupStatement?_sound shape.breakingFound) shape.breakingForm) (.breaking _)))
    · exact .singleton (lookupStatement?_sound shape.returnedFound)
        (by rw [shape.returnedForm]; intro id impossible; cases impossible)
        (.returnValue (lookupStatement?_sound shape.returnedFound) shape.returnedForm
          (read shape.second shape.secondFound shape.secondForm shape.secondRequirements shape.secondCoercions
            (sourceHeap word) (by exact .intro .head)))
  have invoked := sourceAt.frame.body_of_trace header.extended bound (FunctionCallBody.Trace.returned body)
  cases invoked with
  | value invoked =>
    exact ⟨rawD, global, sourceAt, .global sourceAt.frame.instantiated rfl
      (sourceAt.dictionary ▸ sourceAt.frame.covers) (sourceAt.dictionary ▸ invoked)⟩

end Tests.SourceCoreSelectedLoop
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedLoopFixture
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreSelectedLoop
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open SelectedCompilationCertifiedPublicSession (Profiled Initial)
open RecursiveNamedPublicPhysicalSessionState (StartedCall PlainValue SourceCall)

def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content :=
    "function stop(value: Word) returns (Word) { for (let copy: Word = value; true; ) { break; } return value; }"}] }

def options : SourceCompiler.Options := {checkingFuel := 1000, compilationFuel := 1000, specializationBudget := 128}
def runOptions : SourceCoreExecution.RunOptions := {executionFuel := 100000, outputValidationFuel := 1000}
def seed : Word := Word.ofNatModulo 37

private def observed (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
  if witness : p then pure ⟨witness⟩ else throw (IO.userError message)

def observeShape (source : TypedSource) : IO (Shape source) := do
  let [binder] := source.inputs | throw (IO.userError "loop control source input shape")
  let [.expression first, .expression condition, .statement breaking, .statement loop, .expression second, .statement returned] := source.nodes
    | throw (IO.userError s!"loop control occurrence shape: {reprStr source.nodes}")
  let .forLoop [.letDecl copy (some _)] _ [] [_] := loop.form
    | throw (IO.userError "loop control header shape")
  let ⟨inputs⟩ ← observed (source.inputs = [binder]) "loop control inputs"
  let ⟨binderType⟩ ← observed (binder.scheme = .mono .word) "loop control binderType"
  let ⟨copyType⟩ ← observed (copy.scheme = .mono .word) "loop control copyType"
  let ⟨roots⟩ ← observed (source.roots = [.statement loop.id, .statement returned.id]) "loop control roots"
  let ⟨firstFound⟩ ← observed (source.lookupExpression? first.id = some first) "loop control firstFound"
  let ⟨firstForm⟩ ← observed (first.form = .reference binder.name (.local binder.id)) "loop control firstForm"
  let ⟨firstRequirements⟩ ← observed (first.requirements = []) "loop control firstRequirements"
  let ⟨firstCoercions⟩ ← observed (first.coercions = []) "loop control firstCoercions"
  let ⟨conditionFound⟩ ← observed (source.lookupExpression? condition.id = some condition) "loop control conditionFound"
  let ⟨conditionForm⟩ ← observed (condition.form = .reference "true" (.builtinBoolean true)) "loop control conditionForm"
  let ⟨conditionRequirements⟩ ← observed (condition.requirements = []) "loop control conditionRequirements"
  let ⟨conditionCoercions⟩ ← observed (condition.coercions = []) "loop control conditionCoercions"
  let ⟨breakingFound⟩ ← observed (source.lookupStatement? breaking.id = some breaking) "loop control breakingFound"
  let ⟨breakingForm⟩ ← observed (breaking.form = .breakStmt) "loop control breakingForm"
  let ⟨loopFound⟩ ← observed (source.lookupStatement? loop.id = some loop) "loop control loopFound"
  let ⟨loopForm⟩ ← observed (loop.form = .forLoop [.letDecl copy (some first.id)] condition.id [] [breaking.id]) "loop control loopForm"
  let ⟨secondFound⟩ ← observed (source.lookupExpression? second.id = some second) "loop control secondFound"
  let ⟨secondForm⟩ ← observed (second.form = .reference binder.name (.local binder.id)) "loop control secondForm"
  let ⟨secondRequirements⟩ ← observed (second.requirements = []) "loop control secondRequirements"
  let ⟨secondCoercions⟩ ← observed (second.coercions = []) "loop control secondCoercions"
  let ⟨returnedFound⟩ ← observed (source.lookupStatement? returned.id = some returned) "loop control returnedFound"
  let ⟨returnedForm⟩ ← observed (returned.form = .returnStmt (some second.id)) "loop control returnedForm"
  return {
    binder := binder
    copy := copy
    first := first
    condition := condition
    breaking := breaking
    loop := loop
    second := second
    returned := returned
    inputs := inputs
    binderType := binderType
    copyType := copyType
    roots := roots
    firstFound := firstFound
    firstForm := firstForm
    firstRequirements := firstRequirements
    firstCoercions := firstCoercions
    conditionFound := conditionFound
    conditionForm := conditionForm
    conditionRequirements := conditionRequirements
    conditionCoercions := conditionCoercions
    breakingFound := breakingFound
    breakingForm := breakingForm
    loopFound := loopFound
    loopForm := loopForm
    secondFound := secondFound
    secondForm := secondForm
    secondRequirements := secondRequirements
    secondCoercions := secondCoercions
    returnedFound := returnedFound
    returnedForm := returnedForm }

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
  resultType : named.specialized.function.inferredBodyType = .word
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
      | none => throw (IO.userError "loop control artifact absent")
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
              | throw (IO.userError "loop control selected profile rejected")
            match originals : recipe.compiled.validationPlan.specializations with
            | [] => throw (IO.userError "loop control original row absent")
            | originalRow :: rest =>
              match functions : recipe.compiled.indexed.base.functions with
              | [named] =>
                let shape ← observeShape named.specialized.function.typedBody
                let ⟨resultType⟩ ← observed (named.specialized.function.inferredBodyType = .word) "loop control factory result"
                let ⟨substitution⟩ ← observed (named.specialized.parameterSubstitution = []) "loop control substitution"
                let ⟨ordinary⟩ ← observed (named.specialized.function.returnComptime = false) "loop control factory marker"
                let ⟨ordinaryInputs⟩ ← observed (named.specialized.function.typedBody.inputs.all (fun binder => !binder.comptime) = true) "loop control parameter markers"
                let ⟨slot⟩ ← observed (recipe.compiled.indexed.base.globals.zipIdx.filter (fun item => decide (item.1.key = named.signature.key)) = [(named.signature, 0)]) "loop control physical slot"
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
              | _ => throw (IO.userError "loop control cache shape")

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
  | .outOfFuel _ => throw (IO.userError "loop control bootstrap exhausted")
  | .ready session =>
    match started : session.start fixture.named.signature.key [.word seed] runOptions.inputValidationFuel with
    | .error error => throw (IO.userError (reprStr error))
    | .ok checkpoint => return ⟨opened.val, opened.property, bootstrap.val, bootstrap.property.1,
        bootstrap.property.2, session, ready, checkpoint, started⟩

end Tests.SourceCoreSelectedLoop
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedLoopSourceFirst
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreSelectedLoop
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open SelectedCompilationCertifiedPublicSession (Profiled Initial)
open RecursiveNamedPublicPhysicalSessionState (StartedCall PlainValue SourceCall)

/-- Only actual compilation, profile, bootstrap and start receipts precede this
ordinary Source proof. No completed public result is an input. -/
structure InitialMeaning (fixture : Fixture) (started : Started fixture) where
  issued : Profiled fixture.recipe
  initial : Initial issued.toIssued started.call
  shape : Shape initial.header.function.source
  plain : ∀ invocation, PlainValue initial.header initial.header invocation ⟨[]⟩ [.word seed]
    (.word seed) (sourceHeap seed)
  forward : ∀ invocation,
    (SourceCall initial.header initial.header invocation ⟨[]⟩ [.word seed]
      (.value (.word seed)) (sourceHeap seed) ∧
      SelectedCompilationStageClosedDirectForward.Output.ForwardAt issued.catalog.rows initial.header
        issued.initial issued.support.profile fixture.recipe [] initial.header.function.resultType
        started.call.checkpoint (.word seed) (sourceHeap seed)) ∨
    SelectedCompilationStageClosedInitialForward.StageStopped issued started.call initial invocation [.word seed]

theorem from_source (fixture : Fixture) (started : Started fixture) :
    Nonempty (InitialMeaning fixture started) := by
  obtain ⟨row⟩ := fixture.eligible
  obtain ⟨issued, initial, namedEq⟩ := SelectedCompilationCertifiedPublicSession.from_checked_profiled_initial_row
    fixture.checked fixture.accepted fixture.selected fixture.profile started.opened started.call
    started.bootstrap started.fresh started.authority (.single started.ready) row
  have rowSame : row.named = fixture.named := by
    have member := List.mem_of_getElem? row.cached
    rw [fixture.functions] at member
    exact List.mem_singleton.mp member
  have sourceEq := initial.header.agreement.source.trans
    (congrArg (fun named => named.specialized.function.typedBody) (namedEq.trans rowSame))
  let shape : Shape initial.header.function.source := sourceEq.symm ▸ fixture.shape
  obtain ⟨rawD, global, sourceAt⟩ :=
    (CallableIndexedOwnedPreparedFiniteNamedInventories.source_receipts issued.catalog.rows).receipts
      initial.header initial.start.selected.member
  have certified := SelectedCompilationHeaderCertificates.certified
    (SelectedCompilationCheckedBodyTyping.of_checked fixture.checked fixture.profile) initial.header
  have plain := fun invocation => ordinary_call initial.header shape certified sourceAt invocation seed
  have simple : ∀ value ∈ ([.word seed] : List SourceCorePublicValues.Value),
      SourceCoreIndexedSession.SimplePublic value := by
    intro value member
    cases List.mem_singleton.mp member
    exact .word seed
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      initial.header.function.context [.word seed] initial.header.types := by
    rw [input_types initial.header shape]
    exact .cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩ .nil
  have meanings : RecursiveNamedPublicDataInputs.Meanings [.word seed] [.word seed] :=
    .cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩ .nil
  exact ⟨⟨issued, initial, shape, plain, fun invocation =>
    SelectedCompilationStageClosedOutputForward.initial issued started.call initial simple inputTypes meanings
      (plain invocation)⟩⟩

end Tests.SourceCoreSelectedLoop
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedLoopProfile
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedLoop
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering

private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def word (n : Nat) : SourceCorePublicValues.Value := .word (Word.ofNatModulo n)

private def runProgram (workspace : Workspace.RawWorkspace) (names : List String) (cacheSize : Nat)
    (run : ∀ artifact : SourceCoreExecution.Artifact, SourceCoreExecution.Session artifact →
      List SourceCoreExecution.Key → IO Unit) : IO Unit := do
  match checked : checkProgram workspace options.checkingFuel with
  | .error errors => throw (IO.userError s!"loop control checking: {reprStr errors}")
  | .ok program =>
    let roots ← names.mapM (SourceCoreUnifiedCorpusSupport.key program)
    match generated : SourceCoreCompiler.compileChecked program
        (roots.map (fun key => .declaration key.declaration)) options with
    | .error error => throw (IO.userError s!"loop control compilation: {reprStr error}")
    | .ok source =>
      match present : source.artifact? with
      | none => throw (IO.userError "loop control cached artifact missing")
      | some cached =>
        have sameProgram : cached.sourceProgram = program :=
          (source.artifact_fields present).1.trans (SourceCoreCompiler.compileChecked_program generated)
        have original : checkProgram workspace options.checkingFuel = .ok cached.sourceProgram := by
          rw [sameProgram]; exact checked
        let some profile := SelectedCompilationCompilerStaticProfile.validateCheckedProfile cached original
          | throw (IO.userError "loop control selected profile rejected")
        require (cached.indexed.base.functions.length == cacheSize && profile.table.rows.length == cacheSize)
          "loop control actual cache/table size changed"
        match preparedRecipe : SourceCoreIndexedSession.Recipe.prepare cached with
        | .error error => throw (IO.userError s!"loop control recipe: {reprStr error}")
        | .ok recipe =>
          match entries : cached.indexed.entries with
          | [] => throw (IO.userError "loop control root entry missing")
          | entry :: _ =>
            have _issued : Nonempty (SelectedCompilationCertifiedPublicSession.Issued recipe) := by
              have same := SourceCoreIndexedSession.Recipe.prepare_compiled preparedRecipe
              cases same
              exact SelectedCompilationCertifiedPublicSession.of_checked_profile profile preparedRecipe
                (entry := entry) (by rw [entries]; simp) original
            let prepared ← get "loop control public preparation" (SourceCoreExecution.prepare source)
            let artifact ← prepared.open
            let bootstrap ← artifact.bootstrap
            let .ready initial := bootstrap.resume 100000
              | throw (IO.userError "loop control bootstrap missing")
            IO.println s!"BODY_CACHE: {names}; cache{cached.indexed.base.functions.length}/table{profile.table.rows.length}; heap{initial.heapSize}"
            run artifact initial roots

private def success {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreExecution.Key)
    (arguments : List SourceCorePublicValues.Value) (value : SourceCorePublicValues.Value) :
    IO (SourceCoreExecution.Session artifact) := do
  let started ← get "loop control startup" (session.start key arguments)
  let .outOfFuel suspended ← started.resume 0 0
    | throw (IO.userError "loop control zero fuel did not suspend")
  let .succeeded completed ← suspended.resume 100000 1000
    | throw (IO.userError "loop control success missing")
  require (completed.value == value) "loop control result changed"
  pure completed.session

private def failure {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreExecution.Key)
    (arguments : List SourceCorePublicValues.Value) : IO (SourceCoreExecution.Session artifact) := do
  let started ← get "loop control fault startup" (session.start key arguments)
  let .failed reason after ← started.resume 100000 1000
    | throw (IO.userError "loop control absent read did not fail")
  let some diagnostic ← get "loop control diagnostic" (after.diagnostic key reason)
    | throw (IO.userError "loop control diagnostic missing")
  require (match diagnostic.error with | .uninitializedLocal _ => true | _ => false)
    "loop control failure reason changed"
  pure after

def originalWorkspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "function whileCount(start: Word) returns (Word, Word) {",
    "  let remaining: Word = start; let count: Word = 0;",
    "  while (remaining > 0) { let copy: Word = remaining; remaining = remaining - 1; count = count + 1; }",
    "  return (remaining, count);",
    "}",
    "function forOrder(limit: Word) returns (Word, Word) {",
    "  let count: Word = 0;",
    "  for (let i: Word = 0; limit > i; i = i + 1) {",
    "    count = count + 1; if (i == 1) { continue; } count = count + 10;",
    "  } return (count, limit);",
    "}",
    "function forBreak(limit: Word) returns (Word) {",
    "  let count: Word = 0; for (let i: Word = 0; limit > i; i = i + 1) { count = count + 1; break; }",
    "  return count;",
    "}",
    "function initializerScope(limit: Word) returns (Word) {",
    "  let i: Word = 17; for (let i: Word = 0; limit > i; i = i + 1) { } return i;",
    "}",
    "function postScope(limit: Word) returns (Word) {",
    "  let copy: Word = 99;",
    "  for (let i: Word = 0; limit > i; let copy: Word = i, i = copy + 1) { } return copy;",
    "}",
    "function nested() returns (Word, Word) {",
    "  let outer: Word = 2; let count: Word = 0; while (outer > 0) {",
    "    let inner: Word = 2; while (inner > 0) {",
    "      inner = inner - 1; if (inner == 1) { continue; } count = count + 1; break;",
    "    } outer = outer - 1;",
    "  } return (count, outer);",
    "}",
    "function returnInside(limit: Word) returns (Word) {",
    "  let remaining: Word = limit; while (remaining > 0) { return remaining; } return 0;",
    "}",
    "function absentCondition() returns (Word) { let missing: Bool; while (missing) { return 17; } return 0; }",
    "function absentPost() returns (Word) { let missing: Word; for (let i: Word = 0; true; i = missing) { continue; } return 0; }",
    "function absentInitializer() returns (Word) { let missing: Word; for (let i: Word = missing; true; i = i + 1) { break; } return 0; }",
    "function spin() { while (true) { continue; } }",
    "function compound(limit: Word) { for (let i: Word = 0; limit > i; i += 1) { } }"
  ] }]
}

private def checkBoundary (name : String) (acceptedProfile : Bool) : IO Unit := do
  match checked : checkProgram originalWorkspace options.checkingFuel with
  | .error errors => throw (IO.userError (reprStr errors))
  | .ok program =>
    let key ← SourceCoreUnifiedCorpusSupport.key program name
    match generated : SourceCoreCompiler.compileChecked program [.declaration key.declaration] options with
    | .error error => throw (IO.userError (reprStr error))
    | .ok source =>
      match present : source.artifact? with
      | none => throw (IO.userError "loop boundary artifact missing")
      | some cached =>
        have sameProgram : cached.sourceProgram = program :=
          (source.artifact_fields present).1.trans (SourceCoreCompiler.compileChecked_program generated)
        have original : checkProgram originalWorkspace options.checkingFuel = .ok cached.sourceProgram := by
          rw [sameProgram]; exact checked
        require ((SelectedCompilationCompilerStaticProfile.validateCheckedProfile cached original).isSome == acceptedProfile)
          s!"loop profile boundary changed: {name}"
        if name == "compound" then
          let some named := cached.indexed.base.functions.head?
            | throw (IO.userError "compound loop cached row missing")
          require (AcceptedCompilerBodyProfile.validate named.specialized.function.typedBody (fun _ => True)).isSome
            "compound header body profile was not accepted"

private def checkMissingInitializer (fixture : Fixture) : IO Unit := do
  let source := fixture.named.specialized.function.typedBody
  require (AcceptedCompilerBodyProfile.validate source (fun _ => True)).isSome "loop actual source body profile"
  require (AcceptedCompilerBodyProfile.validate source (fun id => id ≠ fixture.shape.first.id)).isNone
    "loop initializer expression coverage was not required"
  let dirty := {source with nodes := source.nodes.map fun
    | .statement node => if node.id == fixture.shape.loop.id then .statement {node with
        form := .forLoop [.letDecl {fixture.shape.copy with scheme := {fixture.shape.copy.scheme with quantified := [⟨999⟩]}}
          (some fixture.shape.first.id)] fixture.shape.condition.id [] [fixture.shape.breaking.id]}
      else .statement node
    | node => node}
  require (AcceptedCompilerBodyProfile.validate dirty (fun _ => True)).isNone "loop polymorphic header was accepted"

def run : IO Unit := do
  checkBoundary "spin" true
  checkBoundary "compound" true
  let fixture ← fixture
  checkMissingInitializer fixture
  let started ← observeStarted fixture
  have _sourceFirst := from_source fixture started
  let .outOfFuel suspended ← started.call.checkpoint.resume 0 0
    | throw (IO.userError "loop initial zero fuel did not suspend")
  let .succeeded stopped ← suspended.resume 100000 1000
    | throw (IO.userError "loop source-first break did not complete")
  require (stopped.value == .word seed) "loop independent Source result changed"
  require ([started.session.heapSize, stopped.session.heapSize] == [2, 9]) "loop Source-first native heap changed"
  IO.println s!"LOOP_SOURCE_HEAPS: {[started.session.heapSize, stopped.session.heapSize]}"
  runProgram originalWorkspace
    ["whileCount", "forOrder", "forBreak", "initializerScope", "postScope", "nested", "returnInside",
      "absentCondition", "absentPost", "absentInitializer"] 10 fun _ initial keys => do
    let [whileKey, order, breaking, initialScope, postScope, nested, returned, missingCondition, missingPost, missingInitial] := keys
      | throw (IO.userError "loop original key order changed")
    let counted ← success initial whileKey [word 3] (.product (word 0) (word 3))
    let ordered ← success counted order [word 3] (.product (word 23) (word 3))
    let broken ← success ordered breaking [word 3] (word 1)
    let restored ← success broken initialScope [word 2] (word 17)
    let postRestored ← success restored postScope [word 3] (word 99)
    let nestedResult ← success postRestored nested [] (.product (word 2) (word 0))
    let early ← success nestedResult returned [word 3] (word 3)
    let conditionFault ← failure early missingCondition []
    let postFault ← failure conditionFault missingPost []
    let initializerFault ← failure postFault missingInitial []
    let continued ← success initializerFault breaking [word 3] (word 1)
    let heaps := [initial.heapSize, counted.heapSize, ordered.heapSize, broken.heapSize,
      restored.heapSize, postRestored.heapSize, nestedResult.heapSize, early.heapSize, conditionFault.heapSize,
      postFault.heapSize, initializerFault.heapSize, continued.heapSize]
    require (heaps == [11, 30, 40, 50, 60, 79, 94, 101, 105, 112, 115, 125]) "loop original native heap sequence changed"
    IO.println s!"LOOP_CORPUS_HEAPS: {heaps}"
  IO.println "LOOP_COMPILER_PROFILE_FORWARD_PASS: original source corpus and cache10/table10; actual initializer/post scopes; break/continue and nested loops; independent Source initializer-break-return trace into the closed public endpoint; exact outcomes, fault prefixes and subsequent session reuse; zero-fuel resumption"

end Tests.SourceCoreSelectedLoop
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedMatchSource
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreSelectedMatch
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedFunctionValues (Header NamedSourceAt)

def inputHeap (previous next : Word) : Dynamic.Heap :=
  ⟨[{type := .word, value := some (.word previous)}, {type := .word, value := some (.word next)}]⟩
def hiddenHeap (previous next : Word) : Dynamic.Heap :=
  ⟨(inputHeap previous next).cells ++ [{type := .word, value := some (.word next)}]⟩
def boundHeap (previous next : Word) : Dynamic.Heap :=
  ⟨(hiddenHeap previous next).cells ++ [{type := .word, value := some (.word next)}]⟩
def sourceHeap (next : Word) : Dynamic.Heap := boundHeap next next

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
  {function : CheckedFunction} {signature : ProgramFunctionSignature}
  (shape : Tests.SourceCoreNamedMatch.FactoryShape function signature)
  (sourceEq : header.function.source = function.typedBody)

include shape sourceEq in
theorem input_types : header.types = [.word, .word] := by
  have params : header.function.parameters = [shape.value, shape.argument] :=
    header.parameters.trans (header.inputs.symm.trans (sourceEq ▸ shape.inputs))
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq header.extended
  simpa only [params, List.map_cons, List.map_nil, shape.valueScheme,
    shape.argumentScheme, TypeSystem.Scheme.mono] using types.symm

include shape sourceEq in
private theorem arm_extension (certified : SelectedCompilationNamedSourceTyping.Certified header) :
    ∃ armContext, BindersExtend function.typedBody.owner header.context [shape.copyBinder] armContext := by
  obtain ⟨final, facts, typed, completes⟩ := certified.statements
  have roots : header.function.body = [shape.matchNode.id, shape.statement.id] :=
    roots_injective (header.agreement.roots.symm.trans (sourceEq ▸ shape.roots))
  rw [roots, sourceEq] at typed
  cases typed with
  | cons head tail =>
    have readFound : function.typedBody.lookupExpression? shape.matching.scrutinee = some shape.initialRead.node := by
      rw [shape.scrutinee]; exact shape.initialRead.found
    obtain ⟨_, caseFacts, _, casesTyped, _⟩ := ScopedSourceMatchAdmission.statement_sites
      (sourceEq ▸ header.unique) shape.matchFound shape.matchForm readFound head
    obtain ⟨binders, arity, armContext, _, _, pattern, extension, _⟩ :=
      ScopedSourceMatchAdmission.case_typing (arm := shape.arm) casesTyped (by rw [shape.arms]; simp)
    have same := CompatiblePatternSourceBinders.pattern_binders pattern
    have sameBinders : [shape.copyBinder] = binders := by
      simpa [SourceCoreDataPlaces.patternBinders, shape.patternResolution,
        SourceCoreDataPlaces.instructionBinders] using same
    exact ⟨armContext, sameBinders ▸ extension⟩

include shape sourceEq in
/-- Allocate the hidden scrutinee and original pattern binder, mutate the outer
parameter, restore its scope, and return it. This trace is independent of Core execution. -/
theorem ordinary_call (certified : SelectedCompilationNamedSourceTyping.Certified header)
    {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {global : Dynamic.GlobalFunction}
    (sourceAt : NamedSourceAt header rawD global) (invocation : Staging.Recursive.Scope)
    (previous next : Word) :
    RecursiveNamedPublicPhysicalSessionState.PlainValue header header invocation ⟨[]⟩
      [.word previous, .word next] (.word next) (sourceHeap next) := by
  let environment : Dynamic.Environment := [(shape.argument.id, ⟨1⟩), (shape.value.id, ⟨0⟩)]
  let armEnvironment : Dynamic.Environment := (shape.copyBinder.id, ⟨3⟩) :: environment
  have params : header.function.parameters = [shape.value, shape.argument] :=
    header.parameters.trans (header.inputs.symm.trans (sourceEq ▸ shape.inputs))
  have bound : Dynamic.BindersAllocate [] ⟨[]⟩ header.function.parameters [.word previous, .word next]
      environment (inputHeap previous next) := by
    rw [params]
    exact .cons (by rw [shape.valueScheme]; exact .append)
      (.cons (by rw [shape.argumentScheme]; exact .append) (.nil _ _))
  have roots : header.function.body = [shape.matchNode.id, shape.statement.id] :=
    roots_injective (header.agreement.roots.symm.trans (sourceEq ▸ shape.roots))
  have read {binder : TypedBinder} (value : Word)
      (node : Tests.SourceCoreNamedMatch.Read function.typedBody binder .word)
      (context : SourceSemantics.Context) (env : Dynamic.Environment) (heap : Dynamic.Heap)
      (location : Dynamic.Location)
      (lookup : Dynamic.Environment.LooksUp env binder.id location)
      (reads : Dynamic.Heap.Reads heap location ⟨.word, some (.word value), none⟩) :
      Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram)
        context header.function.evidence function.typedBody env heap node.node.id (.word value) heap := by
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound node.found)
    · rw [node.form]
      exact .local (by rw [node.requirements, node.coercions]; rfl) lookup reads rfl rfl
    · rw [node.coercions]; exact .nil
  obtain ⟨armContext, extension⟩ := arm_extension header shape sourceEq certified
  have selected : Dynamic.MatchCasesSelect header.context (.word next) shape.matching.cases
      shape.matching.defaultBody (.arm [shape.assignment.id] [(shape.copyBinder, .word next)]) := by
    rw [shape.arms, ← shape.armBody]
    apply Dynamic.MatchCasesSelect.head
    apply Dynamic.PatternMatches.intro (rootArity := 0)
    · rw [shape.patternSource, shape.patternResolution]; exact .binder rfl
    · rw [shape.patternResolution]; exact .binder
  have resolve : Dynamic.SourcePlaceResolves (Program.ofChecked compiled.sourceProgram)
      armContext header.function.evidence function.typedBody armEnvironment (boundHeap previous next)
      shape.resolution.target
      {location := ⟨0⟩, rootType := .word, valueType := shape.resolution.target.type, projections := [], selected := some (.word previous)}
      (boundHeap previous next) := by
    apply Dynamic.SourcePlaceResolves.intro (currentCell := ⟨.word, some (.word previous), none⟩)
      (initialCell := ⟨.word, some (.word previous), none⟩)
    · rw [shape.targetRoot]; exact .tail shape.localValue (.tail shape.argumentValue .head)
    · exact .intro .head
    · rw [shape.targetBare]; exact .nil
    · exact .intro .head
    · exact .initialized
    · exact .nil
  have assigned : Dynamic.StatementExecutes (Program.ofChecked compiled.sourceProgram)
      armContext header.function.evidence function.typedBody armEnvironment (boundHeap previous next)
      shape.assignment.id armContext (.fallthrough armEnvironment) (sourceHeap next) := by
    apply Dynamic.StatementExecutes.assignValue (lookupStatement?_sound shape.assignmentFound) shape.assignmentForm
    apply Dynamic.SourcePlaceAssignment.intro resolve
    · exact read next shape.localRead armContext armEnvironment (boundHeap previous next) ⟨3⟩ .head
        (.intro (.tail (.tail (.tail .head))))
    · exact .intro (.intro .head) rfl .initialized (.leaf (.equal _ _)) (.intro (.intro .head) .head)
  have matched : Dynamic.StatementExecutes (Program.ofChecked compiled.sourceProgram)
      header.context header.function.evidence function.typedBody environment (inputHeap previous next)
      shape.matchNode.id header.context (.fallthrough environment) (sourceHeap next) := by
    apply Dynamic.StatementExecutes.matchArm (outcome := .fallthrough armEnvironment)
      (scrutineeNode := shape.initialRead.node) (armEnvironment := armEnvironment)
      (hiddenHeap := hiddenHeap previous next) (bound := boundHeap previous next)
      (lookupStatement?_sound shape.matchFound) shape.matchForm
      (shape.scrutinee ▸ lookupExpression?_sound shape.initialRead.found)
    · rw [shape.scrutinee]
      exact read next shape.initialRead header.context environment (inputHeap previous next) ⟨1⟩ .head (.intro (.tail .head))
    · rw [shape.initialRead.type]; exact .append
    · exact selected
    · rfl
    · rfl
    · exact extension
    · exact .cons (by rw [shape.localScheme]; exact .append) (.nil _ _)
    · exact .cons assigned .nil
  have body : Dynamic.FunctionStatementsExecute (Program.ofChecked compiled.sourceProgram)
      header.context header.function.evidence header.function.source environment (inputHeap previous next)
      header.function.body header.context (.returned (.word next)) (sourceHeap next) := by
    rw [roots, sourceEq]
    apply Dynamic.FunctionStatementsExecute.cons matched
    exact .singleton (lookupStatement?_sound shape.statementFound)
      (by rw [shape.statementForm]; intro id impossible; cases impossible)
      (.returnValue (lookupStatement?_sound shape.statementFound) shape.statementForm
        (read next shape.finalRead header.context environment (sourceHeap next) ⟨0⟩
          (.tail shape.argumentValue .head) (.intro .head)))
  have invoked := sourceAt.frame.body_of_trace header.extended bound (FunctionCallBody.Trace.returned body)
  cases invoked with
  | value invoked =>
    exact ⟨rawD, global, sourceAt, .global sourceAt.frame.instantiated rfl
      (sourceAt.dictionary ▸ sourceAt.frame.covers) (sourceAt.dictionary ▸ invoked)⟩

end Tests.SourceCoreSelectedMatch
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedMatchFixture
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreSelectedMatch
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open SelectedCompilationCertifiedPublicSession (Profiled Initial)
open RecursiveNamedPublicPhysicalSessionState (StartedCall PlainValue SourceCall)

def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content :=
    "function update(value: Word, next: Word) returns (Word) { match (next) { case copy { value = copy; } } return value; }"}] }

def options : SourceCompiler.Options := {checkingFuel := 1000, compilationFuel := 1000, specializationBudget := 128}
def runOptions : SourceCoreExecution.RunOptions := {executionFuel := 100000, outputValidationFuel := 1000}
def previous : Word := Word.ofNatModulo 11
def seed : Word := Word.ofNatModulo 12

private def observed (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
  if witness : p then pure ⟨witness⟩ else throw (IO.userError message)

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
  signature : ProgramFunctionSignature
  shape : Tests.SourceCoreNamedMatch.FactoryShape named.specialized.function signature
  resultType : named.specialized.function.inferredBodyType = .word
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
      | none => throw (IO.userError "match artifact absent")
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
              | throw (IO.userError "match selected profile rejected")
            match originals : recipe.compiled.validationPlan.specializations with
            | [] => throw (IO.userError "match original row absent")
            | originalRow :: rest =>
              match functions : recipe.compiled.indexed.base.functions with
              | [named] =>
                let [signature] := recipe.compiled.sourceProgram.signatures.functions
                  | throw (IO.userError "match original signature")
                let shape ← Tests.SourceCoreNamedMatch.observeShape named.specialized.function signature
                let ⟨resultType⟩ ← observed (named.specialized.function.inferredBodyType = .word) "match factory result"
                let ⟨substitution⟩ ← observed (named.specialized.parameterSubstitution = []) "match substitution"
                let ⟨ordinary⟩ ← observed (named.specialized.function.returnComptime = false) "match factory marker"
                let ⟨ordinaryInputs⟩ ← observed (named.specialized.function.typedBody.inputs.all (fun binder => !binder.comptime) = true) "match parameter markers"
                let ⟨slot⟩ ← observed (recipe.compiled.indexed.base.globals.zipIdx.filter (fun item => decide (item.1.key = named.signature.key)) = [(named.signature, 0)]) "match physical slot"
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
                  signature := signature
                  shape := shape
                  resultType := resultType
                  substitution := substitution
                  ordinary := ordinary
                  ordinaryInputs := by
                    intro binder member
                    have same := List.all_eq_true.mp ordinaryInputs binder member
                    cases marker : binder.comptime <;> simp_all
                  slot := slot }
              | _ => throw (IO.userError "match cache shape")

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
  call : StartedCall session fixture.named.signature.key [.word previous, .word seed] runOptions

def observeStarted (fixture : Fixture) : IO (Started fixture) := do
  let opened ← fixture.facade.openWithReceipt
  let bootstrap ← opened.val.bootstrapWithExportReceipt
  match ready : bootstrap.val.resume 100000 with
  | .error error => throw (IO.userError (reprStr error))
  | .outOfFuel _ => throw (IO.userError "match bootstrap exhausted")
  | .ready session =>
    match started : session.start fixture.named.signature.key [.word previous, .word seed] runOptions.inputValidationFuel with
    | .error error => throw (IO.userError (reprStr error))
    | .ok checkpoint => return ⟨opened.val, opened.property, bootstrap.val, bootstrap.property.1,
        bootstrap.property.2, session, ready, checkpoint, started⟩

end Tests.SourceCoreSelectedMatch
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedMatchSourceFirst
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreSelectedMatch
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open SelectedCompilationCertifiedPublicSession (Profiled Initial)
open RecursiveNamedPublicPhysicalSessionState (StartedCall PlainValue SourceCall)

/-- Only actual compilation, profile, bootstrap and start receipts precede this
ordinary Source proof. No completed public result is an input. -/
structure InitialMeaning (fixture : Fixture) (started : Started fixture) where
  issued : Profiled fixture.recipe
  initial : Initial issued.toIssued started.call
  sourceEq : initial.header.function.source = fixture.named.specialized.function.typedBody
  plain : ∀ invocation, PlainValue initial.header initial.header invocation ⟨[]⟩ [.word previous, .word seed]
    (.word seed) (sourceHeap seed)
  forward : ∀ invocation,
    (SourceCall initial.header initial.header invocation ⟨[]⟩ [.word previous, .word seed]
      (.value (.word seed)) (sourceHeap seed) ∧
      SelectedCompilationStageClosedDirectForward.Output.ForwardAt issued.catalog.rows initial.header
        issued.initial issued.support.profile fixture.recipe [] initial.header.function.resultType
        started.call.checkpoint (.word seed) (sourceHeap seed)) ∨
    SelectedCompilationStageClosedInitialForward.StageStopped issued started.call initial invocation [.word previous, .word seed]

theorem from_source (fixture : Fixture) (started : Started fixture) :
    Nonempty (InitialMeaning fixture started) := by
  obtain ⟨row⟩ := fixture.eligible
  obtain ⟨issued, initial, namedEq⟩ := SelectedCompilationCertifiedPublicSession.from_checked_profiled_initial_row
    fixture.checked fixture.accepted fixture.selected fixture.profile started.opened started.call
    started.bootstrap started.fresh started.authority (.single started.ready) row
  have rowSame : row.named = fixture.named := by
    have member := List.mem_of_getElem? row.cached
    rw [fixture.functions] at member
    exact List.mem_singleton.mp member
  have sourceEq := initial.header.agreement.source.trans
    (congrArg (fun named => named.specialized.function.typedBody) (namedEq.trans rowSame))
  obtain ⟨rawD, global, sourceAt⟩ :=
    (CallableIndexedOwnedPreparedFiniteNamedInventories.source_receipts issued.catalog.rows).receipts
      initial.header initial.start.selected.member
  have certified := SelectedCompilationHeaderCertificates.certified
    (SelectedCompilationCheckedBodyTyping.of_checked fixture.checked fixture.profile) initial.header
  have plain := fun invocation => ordinary_call initial.header fixture.shape sourceEq certified sourceAt invocation previous seed
  have simple : ∀ value ∈ ([.word previous, .word seed] : List SourceCorePublicValues.Value),
      SourceCoreIndexedSession.SimplePublic value := by
    intro value member
    rcases List.mem_cons.mp member with rfl | member
    · exact .word previous
    · cases List.mem_singleton.mp member; exact .word seed
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      initial.header.function.context [.word previous, .word seed] initial.header.types := by
    rw [input_types initial.header fixture.shape sourceEq]
    exact .cons ⟨.word previous, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word previous⟩
      (.cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩ .nil)
  have meanings : RecursiveNamedPublicDataInputs.Meanings [.word previous, .word seed] [.word previous, .word seed] :=
    .cons ⟨.word previous, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word previous⟩
      (.cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩ .nil)
  exact ⟨⟨issued, initial, sourceEq, plain, fun invocation =>
    SelectedCompilationStageClosedOutputForward.initial issued started.call initial simple inputTypes meanings
      (plain invocation)⟩⟩

end Tests.SourceCoreSelectedMatch
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedMatchProfile
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedMatch
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering

private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def word (n : Nat) : SourceCorePublicValues.Value := .word (Word.ofNatModulo n)

private def runProgram (workspace : Workspace.RawWorkspace) (names : List String) (cacheSize : Nat)
    (run : ∀ artifact : SourceCoreExecution.Artifact, SourceCoreExecution.Session artifact →
      List SourceCoreExecution.Key → IO Unit) : IO Unit := do
  match checked : checkProgram workspace options.checkingFuel with
  | .error errors => throw (IO.userError s!"match checking: {reprStr errors}")
  | .ok program =>
    let roots ← names.mapM (SourceCoreUnifiedCorpusSupport.key program)
    match generated : SourceCoreCompiler.compileChecked program
        (roots.map (fun key => .declaration key.declaration)) options with
    | .error error => throw (IO.userError s!"match compilation: {reprStr error}")
    | .ok source =>
      match present : source.artifact? with
      | none => throw (IO.userError "match cached artifact missing")
      | some cached =>
        have sameProgram : cached.sourceProgram = program :=
          (source.artifact_fields present).1.trans (SourceCoreCompiler.compileChecked_program generated)
        have original : checkProgram workspace options.checkingFuel = .ok cached.sourceProgram := by
          rw [sameProgram]; exact checked
        let some profile := SelectedCompilationCompilerStaticProfile.validateCheckedProfile cached original
          | throw (IO.userError "match selected profile rejected")
        require (cached.indexed.base.functions.length == cacheSize && profile.table.rows.length == cacheSize)
          "match actual cache/table size changed"
        if names.contains "early" then
          let earlyKey ← SourceCoreUnifiedCorpusSupport.key program "early"
          let some row := cached.indexed.base.functions.find? (fun row => row.signature.key == earlyKey)
            | throw (IO.userError "match early row missing")
          require (row.specialized.function.typedBody.nodes.any fun
            | .statement node => match node.form with | .matchWith _ => node.type == .word | _ => false
            | _ => false) "match genuine result-valued annotation changed"
        match preparedRecipe : SourceCoreIndexedSession.Recipe.prepare cached with
        | .error error => throw (IO.userError s!"match recipe: {reprStr error}")
        | .ok recipe =>
          match entries : cached.indexed.entries with
          | [] => throw (IO.userError "match root entry missing")
          | entry :: _ =>
            have _issued : Nonempty (SelectedCompilationCertifiedPublicSession.Issued recipe) := by
              have same := SourceCoreIndexedSession.Recipe.prepare_compiled preparedRecipe
              cases same
              exact SelectedCompilationCertifiedPublicSession.of_checked_profile profile preparedRecipe
                (entry := entry) (by rw [entries]; simp) original
            let prepared ← get "match public preparation" (SourceCoreExecution.prepare source)
            let artifact ← prepared.open
            let bootstrap ← artifact.bootstrap
            let .ready initial := bootstrap.resume 100000
              | throw (IO.userError "match bootstrap missing")
            IO.println s!"BODY_CACHE: {names}; cache{cached.indexed.base.functions.length}/table{profile.table.rows.length}; heap{initial.heapSize}"
            run artifact initial roots

private def success {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreExecution.Key)
    (arguments : List SourceCorePublicValues.Value) (value : SourceCorePublicValues.Value) :
    IO (SourceCoreExecution.Session artifact) := do
  let started ← get "match startup" (session.start key arguments)
  let .outOfFuel suspended ← started.resume 0 0
    | throw (IO.userError "match zero fuel did not suspend")
  let .succeeded completed ← suspended.resume 100000 1000
    | throw (IO.userError "match success missing")
  require (completed.value == value) "match result changed"
  pure completed.session

private def failure {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreExecution.Key)
    (arguments : List SourceCorePublicValues.Value) : IO (SourceCoreExecution.Session artifact) := do
  let started ← get "match fault startup" (session.start key arguments)
  let .failed reason after ← started.resume 100000 1000
    | throw (IO.userError "match absent read did not fail")
  let some diagnostic ← get "match diagnostic" (after.diagnostic key reason)
    | throw (IO.userError "match diagnostic missing")
  require (match diagnostic.error with | .uninitializedLocal _ => true | _ => false)
    "match failure reason changed"
  pure after

def casesWorkspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function select(value: Word) returns (Word) { let result: Word = 99; match (value) { case 0 { result = 5; } case 1 { result = 6; } default { result = 7; } } return result; }",
    "function early(value: Word) returns (Word) { match (value) { case 0 { return 5; } default { return 6; } } return 9; }",
    "function tuple(value: (Word, Word)) returns (Word) { let result: Word = 0; match (value) { case (left, right) { result = left + right; } } return result; }",
    "function scrutineeFault() returns (Word) { let missing: Word; match (missing) { case _ {} } return 0; }",
    "function armFault(value: Word) returns (Word) { match (value) { case 0 { let missing: Word; return missing; } default {} } return 7; }",
    "function control(limit: Word) returns (Word) { for (let i: Word = 0; i < limit; i = i + 1) { match (i) { case 0 { continue; } default { break; } } } return limit; }"
  ]}]
}

def factoryWorkspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{path := "main.solc", content :=
    "function make(value: Word) returns (function(Word) returns (Word)) { return lam(next: Word) -> Word { match (next) { case copy { value = copy; } } return value; }; }"}]
}

private def boundaries (fixture : Fixture) : IO Unit := do
  let source := fixture.named.specialized.function.typedBody
  let expected := fixture.named.specialized.function.inferredBodyType
  require (AcceptedCompilerBodyProfile.validate source (fun _ => True)).isSome "match original body profile"
  require (AcceptedCompilerBodyProfile.validate source (fun id => id ≠ fixture.shape.initialRead.node.id)).isNone
    "match scrutinee coverage omitted"
  let expressions := source.nodes.filterMap fun | .expression node => some node.id | _ => none
  let roots := [fixture.shape.matchNode.id, fixture.shape.statement.id]
  require (AcceptedCompilerBodySubsetProfile.validate source expressions roots expected).isSome "match original subset profile"
  require (AcceptedCompilerBodySubsetProfile.validate source
      (expressions.filter (fun id => id != fixture.shape.localRead.node.id)) roots expected).isNone
    "match actual arm coverage omitted"
  let missing := {fixture.shape.assignment.id with occurrence := {fixture.shape.assignment.id.occurrence with index := 1000000}}
  let missingArm := {source with nodes := source.nodes.map fun
    | .statement node => if node.id == fixture.shape.matchNode.id then .statement {node with
        form := .matchWith {fixture.shape.matching with cases := [{fixture.shape.arm with body := [missing]}]}}
      else .statement node
    | node => node}
  require (AcceptedCompilerBodySubsetProfile.validate missingArm expressions roots expected).isNone
    "match nonexistent arm statement accepted"
  let missingDefault := {source with nodes := source.nodes.map fun
    | .statement node => if node.id == fixture.shape.matchNode.id then .statement {node with
        form := .matchWith {fixture.shape.matching with defaultBody := some [missing]}}
      else .statement node
    | node => node}
  require (AcceptedCompilerBodySubsetProfile.validate missingDefault expressions roots expected).isNone
    "match nonexistent default statement accepted"

def run : IO Unit := do
  let fixture ← fixture
  boundaries fixture
  require (fixture.recipe.compiled.indexed.base.functions.length == 1 && fixture.profile.table.rows.length == 1)
    "match original cache/table changed"
  let started ← observeStarted fixture
  have _sourceFirst := from_source fixture started
  let .outOfFuel suspended ← started.call.checkpoint.resume 0 0
    | throw (IO.userError "match initial zero fuel did not suspend")
  let .succeeded first ← suspended.resume 100000 1000
    | throw (IO.userError "match Source-first update failed")
  require (first.value == .word seed) "match Source-first result changed"
  let second ← success first.session fixture.named.signature.key [word 22, word 23] (word 23)
  require ([started.session.heapSize, first.session.heapSize, second.heapSize] == [2, 14, 26])
    "match Source-first native heap changed"
  IO.println s!"MATCH_SOURCE_HEAPS: {[started.session.heapSize, first.session.heapSize, second.heapSize]}"
  runProgram casesWorkspace ["select", "early", "tuple", "scrutineeFault", "armFault", "control"] 6 fun _ initial keys => do
    let [select, early, tuple, scrutineeFault, armFault, control] := keys
      | throw (IO.userError "match corpus keys changed")
    let zero ← success initial select [word 0] (word 5)
    let one ← success zero select [word 1] (word 6)
    let fallback ← success one select [word 2] (word 7)
    let returned ← success fallback early [word 0] (word 5)
    let defaultReturned ← success returned early [word 3] (word 6)
    let unpacked ← success defaultReturned tuple [.product (word 8) (word 9)] (word 17)
    let missing ← failure unpacked scrutineeFault []
    let armMissing ← failure missing armFault [word 0]
    let reused ← success armMissing armFault [word 1] (word 7)
    let controlled ← success reused control [word 3] (word 3)
    require ([initial.heapSize, zero.heapSize, one.heapSize, fallback.heapSize, returned.heapSize, defaultReturned.heapSize, unpacked.heapSize, missing.heapSize, armMissing.heapSize, reused.heapSize, controlled.heapSize] == [7, 16, 25, 34, 40, 46, 61, 64, 73, 79, 92])
      "match corpus native heap changed"
    IO.println s!"MATCH_CASE_HEAPS: {[initial.heapSize, zero.heapSize, one.heapSize, fallback.heapSize, returned.heapSize, defaultReturned.heapSize, unpacked.heapSize, missing.heapSize, armMissing.heapSize, reused.heapSize, controlled.heapSize]}"
  runProgram factoryWorkspace ["make"] 1 fun _ initial keys => do
    let [key] := keys | throw (IO.userError "match factory key")
    let checkpoint ← get "match factory startup" (initial.start key [word 11])
    let .succeeded made ← checkpoint.resume 100000 1000
      | throw (IO.userError "match factory failed")
    let .function handle := made.value | throw (IO.userError "match factory handle missing")
    let firstCheckpoint ← get "match captured startup" (made.session.startHandlePacked handle (word 12))
    let .succeeded first ← firstCheckpoint.resume 100000 1000
      | throw (IO.userError "match captured invocation failed")
    require (first.value == word 12) "match captured mutation changed"
    let nextCheckpoint ← get "match captured reuse" (first.session.startHandlePacked handle (word 23))
    let .succeeded next ← nextCheckpoint.resume 100000 1000
      | throw (IO.userError "match captured reuse failed")
    require (next.value == word 23) "match captured reuse result changed"
    require ([initial.heapSize, made.session.heapSize, first.session.heapSize, next.session.heapSize] == [2, 8, 20, 32])
      "match captured native heap changed"
    IO.println s!"MATCH_CAPTURE_HEAPS: {[initial.heapSize, made.session.heapSize, first.session.heapSize, next.session.heapSize]}"
  IO.println "MATCH_COMPILER_PROFILE_FORWARD_PASS"

end Tests.SourceCoreSelectedMatch
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedPrimitiveFixture
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedPrimitiveFixture
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering

def wordOperators : List (String × String) := [
  ("mul", "*"), ("divide", "/"), ("modulo", "%"), ("add", "+"), ("sub", "-"),
  ("band", "&"), ("bxor", "^"), ("bor", "|")]
def comparisons : List (String × String) := [
  ("gt", ">"), ("eq", "==")]

def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" (
    (wordOperators.map fun (name, operator) =>
      s!"function {name}(left: Word, right: Word) returns (Word)" ++ " { return left " ++ operator ++ " right; }") ++
    (comparisons.map fun (name, operator) =>
      s!"function {name}(left: Word, right: Word) returns (Bool)" ++ " { return left " ++ operator ++ " right; }") ++ [
    "function conjunction(left: Bool, right: Bool) returns (Bool) { return left && right; }",
    "function disjunction(left: Bool, right: Bool) returns (Bool) { return left || right; }",
    "function negation(input: Bool) returns (Bool) { return !input; }",
    "function complement(input: Word) returns (Word) { return ~input; }",
    "function literal() returns (Word) { return 17; }",
    "function hugeLiteral() returns (Word) { return " ++ toString (Core.wordModulus + 5) ++ "; }",
    "function nested(flag: Bool, value: Word) returns (Word, Bool) {",
    "  return ((flag ? value + 2 : value * 3), (!flag || (value > 0)));",
    "}",
    "function builtin() returns (Word) { return wordFromInteger(1); }",
    "function lt(left: Word, right: Word) returns (Bool) { return right > left; }",
    "function lessCall(left: Word, right: Word) returns (Bool) { return left < right; }"
  ]) }]
}

def options : SourceCompiler.Options := {checkingFuel := 1000, compilationFuel := 1000, specializationBudget := 512}
def runOptions : SourceCoreExecution.RunOptions := {inputValidationFuel := 1000, executionFuel := 100000}

def observed (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
  if witness : p then pure ⟨witness⟩ else throw (IO.userError message)

/-- Only original checking, compilation and preparation receipts are retained. -/
structure Fixture where
  program : CheckedProgram
  checked : checkProgram workspace options.checkingFuel = .ok program
  seeds : List SourceCompiler.Seed
  facade : SourceCompiler.Compiled
  accepted : SourceCompiler.compileChecked program seeds options = .ok facade
  recipe : SourceCoreIndexedSession.Recipe
  issued : RecursiveNamedPreparedStageContracts.PublicRecipe facade recipe
  sameProgram : recipe.compiled.sourceProgram = program

def fixture (names : List String) : IO Fixture := do
  match checked : checkProgram workspace options.checkingFuel with
  | .error errors => throw (IO.userError (reprStr errors))
  | .ok program =>
    let keys ← names.mapM (SourceCoreUnifiedCorpusSupport.key program)
    let seeds := keys.map (fun key => SourceCompiler.Seed.declaration key.declaration)
    match generated : SourceCoreCompiler.compileChecked program seeds options with
    | .error error => throw (IO.userError (reprStr error))
    | .ok source =>
      match selected : source.artifact? with
      | none => throw (IO.userError "primitive artifact missing")
      | some cached =>
        match prepared : SourceCoreIndexedSession.Recipe.prepare cached with
        | .error error => throw (IO.userError (reprStr error))
        | .ok recipe =>
          match facade : SourceCoreExecution.prepare source with
          | .error error => throw (IO.userError (reprStr error))
          | .ok result =>
            have accepted : SourceCompiler.compileChecked program seeds options = .ok result := by
              simpa only [SourceCoreExecution.compileChecked, generated, Except.mapError, bind, Except.bind] using facade
            return ⟨program, checked, seeds, result, accepted, recipe,
              RecursiveNamedPreparedStageContracts.public_preparation selected prepared facade,
              (congrArg (·.sourceProgram) (SourceCoreIndexedSession.Recipe.prepare_compiled prepared)).trans
                ((source.artifact_fields selected).1.trans (SourceCoreCompiler.compileChecked_program generated))⟩

structure Row (fixture : Fixture) where
  row : SourceSpecialization.SpecializedFunction
  member : row ∈ fixture.recipe.compiled.validationPlan.specializations
  parameters : row.parameterSubstitution = []
  ordinary : row.function.returnComptime = false
  inputsOrdinary : ∀ binder ∈ row.function.typedBody.inputs, binder.comptime = false
  global : SourceCoreCalls.Signature
  index : Nat
  slot : CallableNamedMetadata.Slot fixture.recipe.compiled.indexed.base.globals index global
  globalKey : global.key = row.key

def row (fixture : Fixture) (name : String) : IO (Row fixture) := do
  let key ← SourceCoreUnifiedCorpusSupport.key fixture.program name
  match found : fixture.recipe.compiled.validationPlan.specializations.find? (fun row => decide (row.key = key)) with
  | none => throw (IO.userError "primitive row missing")
  | some row =>
    let ⟨parameters⟩ ← observed (row.parameterSubstitution = []) "primitive substitution changed"
    let ⟨ordinary⟩ ← observed (row.function.returnComptime = false) "primitive return changed"
    let ⟨inputs⟩ ← observed (row.function.typedBody.inputs.all (fun binder => !binder.comptime) = true) "primitive input changed"
    match slot : fixture.recipe.compiled.indexed.base.globals.zipIdx.filter (fun item => decide (item.1.key = row.key)) with
    | [(global, index)] =>
      let ⟨keyEq⟩ ← observed (global.key = row.key) "primitive physical key changed"
      return ⟨row, List.mem_of_find?_eq_some found, parameters, ordinary,
        by intro binder member; have h := List.all_eq_true.mp inputs binder member; cases h' : binder.comptime <;> simp_all,
        global, index, by unfold CallableNamedMetadata.Slot; rw [keyEq]; exact slot, keyEq⟩
    | _ => throw (IO.userError "primitive slot is not unique")

theorem Row.eligible {fixture : Fixture} (row : Row fixture) :
    ∃ selected : CertifiedPublicSession.EligibleRow fixture.recipe.compiled row.row.key,
      selected.named.specialized = row.row ∧ selected.named.signature = row.global := by
  obtain ⟨prepared⟩ := RecursiveNamedPublicSpecializationMeaning.of_public_compile fixture.accepted fixture.issued row.member
  have cached := CallableIndexedPreparedInventories.cached_global_at fixture.recipe.compiled prepared.selected
  have member : (prepared.named.signature, prepared.index) ∈ fixture.recipe.compiled.indexed.base.globals.zipIdx.filter
      (fun item => decide (item.1.key = row.global.key)) := by
    refine List.mem_filter.mpr ⟨List.mk_mem_zipIdx_iff_getElem?.mpr cached, ?_⟩
    simp only [row.globalKey, RecursiveNamedPreparedCallEvidence.Prepared.signature_key prepared, decide_true]
  rw [row.slot] at member
  obtain ⟨signatureEq, indexEq⟩ := Prod.mk.inj (List.mem_singleton.mp member)
  have eligible : CallableIndexedOwnedPreparedOrdinaryCatalogReceipts.Eligible fixture.recipe.compiled prepared.named.specialized := by
    rw [prepared.same]
    refine ⟨prepared.origin, ?_, row.ordinary, row.inputsOrdinary⟩
    simp only [row.parameters, ParameterSubstitution.RangeWellFormed, List.not_mem_nil, false_implies, implies_true]
  exact ⟨⟨prepared.named, prepared.index, row.global, prepared.selected,
    by rw [indexEq]; exact row.slot, row.globalKey, eligible⟩, prepared.same, signatureEq⟩

structure Started (fixture : Fixture) (key : SourceCoreIndexedSession.Key)
    (arguments : List SourceCorePublicValues.Value) where
  artifact : SourceCoreExecution.Artifact
  opened : artifact.CompiledAt fixture.facade
  bootstrap : SourceCoreExecution.Bootstrap artifact
  fresh : bootstrap.FreshAt
  authority : bootstrap.ExportAuthorityAt
  session : SourceCoreExecution.Session artifact
  ready : bootstrap.resume 100000 = .ready session
  call : RecursiveNamedPublicPhysicalSessionState.StartedCall session key arguments runOptions

def start (fixture : Fixture) (key : SourceCoreIndexedSession.Key)
    (arguments : List SourceCorePublicValues.Value) : IO (Started fixture key arguments) := do
  let opened ← fixture.facade.openWithReceipt
  let fresh ← opened.val.bootstrapWithExportReceipt
  match ready : fresh.val.resume 100000 with
  | .error error => throw (IO.userError (reprStr error))
  | .outOfFuel _ => throw (IO.userError "primitive bootstrap exhausted")
  | .ready session =>
    match started : session.start key arguments runOptions.inputValidationFuel with
    | .error error => throw (IO.userError (reprStr error))
    | .ok checkpoint => return ⟨opened.val, opened.property, fresh.val, fresh.property.1,
        fresh.property.2, session, ready, checkpoint, started⟩

theorem initial {fixture : Fixture}
    (profile : CompilerProgramStaticProfile.StaticProfile fixture.recipe.compiled)
    (row : Row fixture) {arguments : List SourceCorePublicValues.Value}
    (started : Started fixture row.row.key arguments) :
    ∃ issued : SelectedCompilationCertifiedPublicSession.Profiled fixture.recipe,
      ∃ first : SelectedCompilationCertifiedPublicSession.Initial issued.toIssued started.call,
        first.header.named.specialized = row.row ∧ first.header.named.signature = row.global := by
  obtain ⟨selected, sameRow, sameSignature⟩ := row.eligible
  obtain ⟨issued, first, namedEq⟩ := SelectedCompilationCertifiedPublicSession.from_checked_profiled_initial_row
    (by rw [fixture.sameProgram]; exact fixture.checked)
    (by rw [fixture.sameProgram]; exact fixture.accepted)
    fixture.issued profile started.opened started.call started.bootstrap started.fresh started.authority
    (show started.bootstrap.ReadyAt 100000 started.session from .single started.ready) selected
  exact ⟨issued, first, (congrArg (·.specialized) namedEq).trans sameRow,
    (congrArg (·.signature) namedEq).trans sameSignature⟩

end Tests.SourceCoreSelectedPrimitiveFixture
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedPrimitiveSource
/-! The ordinary complement trace is built from the original checked nodes and
one fresh input cell. No completed public run or reflected trace is an input. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreSelectedPrimitiveSource
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreSelectedPrimitiveFixture
open CallableIndexedOwnedFunctionValues (Header NamedSourceAt)
open SelectedCompilationCertifiedPublicSession (Profiled Initial)
open RecursiveNamedPublicPhysicalSessionState (PlainValue SourceCall)

structure ComplementShape {fixture : Fixture} (row : Row fixture) where
  binder : TypedBinder
  read : ExpressionNode
  unary : ExpressionNode
  statement : StatementNode
  inputs : row.row.function.typedBody.inputs = [binder]
  scheme : binder.scheme = .mono .word
  roots : row.row.function.typedBody.roots = [.statement statement.id]
  readFound : row.row.function.typedBody.lookupExpression? read.id = some read
  readForm : read.form = .reference binder.name (.local binder.id)
  readRequirements : read.requirements = []
  readCoercions : read.coercions = []
  unaryFound : row.row.function.typedBody.lookupExpression? unary.id = some unary
  unaryForm : unary.form = .unary .bitNot read.id
  unaryRequirements : unary.requirements = []
  unaryCoercions : unary.coercions = []
  found : row.row.function.typedBody.lookupStatement? statement.id = some statement
  form : statement.form = .returnStmt (some unary.id)
  result : row.row.function.inferredBodyType = .word
  native : row.global.resultType = .word

def observeComplement {fixture : Fixture} (row : Row fixture) : IO (ComplementShape row) := do
  let source := row.row.function.typedBody
  match inputs : source.inputs, roots : source.roots with
  | [binder], [.statement statementId] =>
    match found : source.lookupStatement? statementId with
    | none => throw (IO.userError "primitive return node missing")
    | some statement =>
      match form : statement.form with
      | .returnStmt (some unaryId) =>
        match unaryFound : source.lookupExpression? unaryId with
        | none => throw (IO.userError "primitive operator node missing")
        | some unary =>
          match unaryForm : unary.form with
          | .unary .bitNot readId =>
            match readFound : source.lookupExpression? readId with
            | none => throw (IO.userError "primitive operand missing")
            | some read =>
              let ⟨scheme⟩ ← observed (binder.scheme = .mono .word) "primitive binder scheme"
              let ⟨readForm⟩ ← observed (read.form = .reference binder.name (.local binder.id)) "primitive read form"
              let ⟨readRequirements⟩ ← observed (read.requirements = []) "primitive read requirements"
              let ⟨readCoercions⟩ ← observed (read.coercions = []) "primitive read coercions"
              let ⟨unaryRequirements⟩ ← observed (unary.requirements = []) "primitive operator requirements"
              let ⟨unaryCoercions⟩ ← observed (unary.coercions = []) "primitive operator coercions"
              let ⟨result⟩ ← observed (row.row.function.inferredBodyType = .word) "primitive result"
              let ⟨native⟩ ← observed (row.global.resultType = .word) "primitive native result"
              have readIdEq := (lookupExpression?_sound readFound).2
              have unaryIdEq := (lookupExpression?_sound unaryFound).2
              have statementIdEq := (lookupStatement?_sound found).2
              return ⟨binder, read, unary, statement, inputs, scheme,
                by simpa only [statementIdEq] using roots,
                by simpa only [readIdEq] using readFound, readForm, readRequirements, readCoercions,
                by simpa only [unaryIdEq] using unaryFound,
                by simpa only [readIdEq] using unaryForm, unaryRequirements, unaryCoercions,
                by simpa only [statementIdEq] using found,
                by simpa only [unaryIdEq] using form, result, native⟩
          | _ => throw (IO.userError "primitive complement form changed")
      | _ => throw (IO.userError "primitive return form changed")
  | _, _ => throw (IO.userError "primitive input/body shape changed")

def appendWord (before : Dynamic.Heap) (value : Word) : Dynamic.Heap :=
  ⟨before.cells ++ [{type := .word, value := some (.word value)}]⟩

private theorem roots_injective {left right : List StatementId}
    (same : left.map NodeId.statement = right.map NodeId.statement) : left = right := by
  induction left generalizing right with
  | nil => cases right <;> simp_all
  | cons head rest ih =>
    cases right with
    | nil => simp_all
    | cons other tail =>
      simp only [List.map_cons, List.cons.injEq] at same
      obtain ⟨same, tails⟩ := same
      cases same
      simp only [ih tails]

variable {fixture : Fixture} {row : Row fixture}
  (shape : ComplementShape row)
  (header : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram))
  (same : header.named.specialized = row.row)

include shape same in
theorem complement_plain
    {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {global : Dynamic.GlobalFunction}
    (sourceAt : NamedSourceAt header rawD global)
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap) (value : Word) :
    PlainValue header header invocation before [.word value] (.word value.bitNot) (appendWord before value) := by
  have source : header.function.source = row.row.function.typedBody := by rw [header.agreement.source, same]
  have parameters : header.function.parameters = [shape.binder] := by
    rw [header.parameters, ← header.inputs, source, shape.inputs]
  have statements : header.function.body = [shape.statement.id] :=
    roots_injective (header.agreement.roots.symm.trans (by rw [source, shape.roots]; rfl))
  have allocated : Dynamic.Heap.Allocates before shape.binder.scheme.body (some (.word value))
      ⟨before.cells.length⟩ (appendWord before value) := by rw [shape.scheme]; exact .append
  have bound : Dynamic.BindersAllocate [] before header.function.parameters [.word value]
      [(shape.binder.id, ⟨before.cells.length⟩)] (appendWord before value) := by
    rw [parameters]; exact .cons allocated (.nil _ _)
  have read : Dynamic.ExpressionEvaluates (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      header.context header.function.evidence header.function.source
      [(shape.binder.id, ⟨before.cells.length⟩)] (appendWord before value)
      shape.read.id (.word value) (appendWord before value) := by
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound (source.symm ▸ shape.readFound))
    · rw [shape.readForm]
      exact .local (by rw [shape.readRequirements, shape.readCoercions]; rfl) .head allocated.reads_new rfl rfl
    · rw [shape.readCoercions]; exact .nil
  have unary : Dynamic.ExpressionEvaluates (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      header.context header.function.evidence header.function.source
      [(shape.binder.id, ⟨before.cells.length⟩)] (appendWord before value)
      shape.unary.id (.word value.bitNot) (appendWord before value) := by
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound (source.symm ▸ shape.unaryFound))
    · rw [shape.unaryForm]
      exact .unary (owned := []) (by rw [shape.unaryRequirements, shape.unaryCoercions]; rfl)
        read (.primitive (.wordBitNot value))
    · rw [shape.unaryCoercions]; exact .nil
  have executed : Dynamic.FunctionStatementsExecute (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      header.context header.function.evidence header.function.source
      [(shape.binder.id, ⟨before.cells.length⟩)] (appendWord before value)
      header.function.body header.context (.returned (.word value.bitNot)) (appendWord before value) := by
    rw [statements]
    have found := lookupStatement?_sound (source.symm ▸ shape.found)
    exact .singleton found (by rw [shape.form]; intro expression impossible; cases impossible)
      (.returnValue found shape.form unary)
  have body := sourceAt.frame.body_of_trace header.extended bound (FunctionCallBody.Trace.returned executed)
  cases body with
  | value invoked =>
    exact ⟨rawD, global, sourceAt, .global sourceAt.frame.instantiated rfl
      (sourceAt.dictionary ▸ sourceAt.frame.covers) (sourceAt.dictionary ▸ invoked)⟩

structure Conclusion (issued : Profiled fixture.recipe)
    {value : Word} (started : Started fixture row.row.key [.word value])
    (invocation : Staging.Recursive.Scope) where
  initial : Initial issued.toIssued started.call
  plain : PlainValue initial.header initial.header invocation ⟨[]⟩ [.word value]
    (.word value.bitNot) (appendWord ⟨[]⟩ value)
  forward :
    (SourceCall initial.header initial.header invocation ⟨[]⟩ [.word value] (.value (.word value.bitNot))
      (appendWord ⟨[]⟩ value) ∧
      SelectedCompilationPublicSessionScalarForward.ForwardAt (entries := []) issued.catalog.rows
        initial.header issued.initial issued.support.profile fixture.recipe (.word value.bitNot) started.call
        (appendWord ⟨[]⟩ value)) ∨
    SelectedCompilationStageClosedInitialForward.StageStopped issued started.call initial invocation [.word value]

include shape in
/-- Checking, the executable profile, finite source shape and a startup receipt
produce the independent ordinary trace and the closed sufficient-fuel theorem. -/
theorem from_source (profile : CompilerProgramStaticProfile.StaticProfile fixture.recipe.compiled)
    {value : Word} (started : Started fixture row.row.key [.word value])
    (invocation : Staging.Recursive.Scope) :
    ∃ issued : Profiled fixture.recipe, Nonempty (Conclusion issued started invocation) := by
  obtain ⟨issued, initial, same, signature⟩ := Tests.SourceCoreSelectedPrimitiveFixture.initial profile row started
  obtain ⟨rawD, function, sourceAt⟩ :=
    (CallableIndexedOwnedPreparedFiniteNamedInventories.source_receipts issued.catalog.rows).receipts
      initial.header initial.start.selected.member
  have plain := complement_plain shape initial.header same sourceAt invocation ⟨[]⟩ value
  have simple : ∀ v ∈ ([.word value] : List SourceCorePublicValues.Value), SourceCoreIndexedSession.SimplePublic v := by
    intro v member; cases List.mem_singleton.mp member; exact .word value
  have types : initial.header.types = [.word] := by
    have eq := Dynamic.MonoBindersExtend.bodyTypes_eq initial.header.extended
    have parameters : initial.header.function.parameters = [shape.binder] := by
      rw [initial.header.parameters, ← initial.header.inputs, initial.header.agreement.source, same, shape.inputs]
    simpa only [parameters, List.map_cons, List.map_nil, shape.scheme, TypeSystem.Scheme.mono] using eq.symm
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      initial.header.function.context [.word value] initial.header.types := by
    rw [types]
    exact .cons ⟨.word value, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word value⟩ .nil
  have meanings : RecursiveNamedPublicDataInputs.Meanings [.word value] [.word value] :=
    .cons ⟨.word value, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word value⟩ .nil
  have raw : initial.header.function.resultType = .word := by rw [initial.header.agreement.result, same, shape.result]
  have native : initial.header.output = .word := by rw [← initial.header.resultType, signature, shape.native]
  exact ⟨issued, ⟨⟨initial, plain, SelectedCompilationStageClosedInitialForward.scalar issued started.call
    initial simple inputTypes meanings (.word value.bitNot) raw native plain⟩⟩⟩

end Tests.SourceCoreSelectedPrimitiveSource
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedPrimitiveProfile
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedPrimitiveProfile
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreSelectedPrimitiveFixture
open Tests.SourceCoreSelectedPrimitiveSource

private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def word (n : Nat) : SourceCorePublicValues.Value := .word (Word.ofNatModulo n)

theorem primitive_forms (left right : ExpressionId) (function : BuiltinFunctionId) (callee : ExpressionId) :
    AcceptedCompilerExpressionProfile.supportedForm false false false (.unary .bitNot left) = true ∧
    AcceptedCompilerExpressionProfile.supportedForm false false false (.binary left .add right) = true ∧
    AcceptedCompilerExpressionProfile.supportedForm false false false (.call callee [left, right] (.builtinFunction function)) = true :=
  ⟨rfl, rfl, rfl⟩

theorem narrow_forms (left right : ExpressionId) (function : BuiltinFunctionId) (callee : ExpressionId) :
    AcceptedCompilerExpressionProfile.supportedForm true false false (.unary .bitNot left) = false ∧
    AcceptedCompilerExpressionProfile.supportedForm true false false (.binary left .add right) = false ∧
    AcceptedCompilerExpressionProfile.supportedForm true false false (.call callee [left, right] (.builtinFunction function)) = false :=
  ⟨rfl, rfl, rfl⟩

private def success {artifact : SourceCoreExecution.Artifact}
    (fixture : Fixture) (session : SourceCoreExecution.Session artifact) (name : String)
    (arguments : List SourceCorePublicValues.Value) (expected : SourceCorePublicValues.Value) :
    IO (SourceCoreExecution.Session artifact) := do
  let key ← SourceCoreUnifiedCorpusSupport.key fixture.program name
  let started ← get "primitive call" (session.start key arguments)
  let .outOfFuel suspended ← started.resume 0 0 | throw (IO.userError "primitive zero fuel did not suspend")
  let .succeeded result ← suspended.resume 100000 1000 | throw (IO.userError s!"primitive {name} failed")
  require (result.value == expected) s!"primitive {name} result changed: {reprStr result.value}"
  pure result.session

private def rawGuards (fixture : Fixture)
    (profile : CompilerProgramStaticProfile.StaticProfile fixture.recipe.compiled) : IO Unit := do
  for name in ["complement", "add", "builtin"] do
    let key ← SourceCoreUnifiedCorpusSupport.key fixture.program name
    let some named := fixture.recipe.compiled.indexed.base.functions.find? (fun named => decide (named.specialized.key = key))
      | throw (IO.userError "primitive raw guard row missing")
    let source := named.specialized.function.typedBody
    let some node := source.nodes.findSome? (fun
      | .expression node => match node.form with
        | .unary _ _ | .binary _ _ _ | .call _ _ (.builtinFunction _) => some node
        | _ => none
      | _ => none) | throw (IO.userError "primitive raw guard node missing")
    let certify := fun source => AcceptedCompilerExpressionProfile.certify fixture.recipe.compiled.indexed named source profile.table.rows
    require (certify source).isSome "primitive genuine expression profile failed"
    let dirty := {source with nodes := source.nodes.map (fun
      | .expression original => if original.id == node.id then .expression {original with coercions :=
          [{requirement := ⟨0⟩, source := original.rawType, target := original.type}]} else .expression original
      | other => other)}
    require (certify dirty).isNone "primitive output coercion bypassed metadata"
    let first :: _ := AcceptedCompilerExpressionProfile.operands node.form
      | throw (IO.userError "primitive actual ordered operand missing")
    let missing := {source with nodes := source.nodes.filter (fun
      | .expression original => original.id != first
      | _ => true)}
    require (certify missing).isNone "primitive missing operand accepted"
    if name == "builtin" then
      let dirty := {source with nodes := source.nodes.map (fun
        | .expression original => if original.id == node.id then .expression {original with requirements := [⟨0⟩]} else .expression original
        | other => other)}
      require (certify dirty).isNone "builtin requirement bypassed metadata"
  IO.println "PRIMITIVE_RAW_GUARDS_PASS: original nodes accepted; missing operands3, output coercions3, builtin requirements1 rejected"

def run : IO Unit := do
  let names := wordOperators.map (·.1) ++ comparisons.map (·.1) ++
    ["conjunction", "disjunction", "negation", "complement", "literal", "hugeLiteral", "nested", "builtin", "lt", "lessCall"]
  let compiled ← fixture names
  have checked : checkProgram workspace options.checkingFuel = .ok compiled.recipe.compiled.sourceProgram := by
    rw [compiled.sameProgram]; exact compiled.checked
  let some profile := SelectedCompilationCompilerStaticProfile.validateCheckedProfile compiled.recipe.compiled checked
    | throw (IO.userError "primitive selected profile rejected")
  IO.println s!"PRIMITIVE_CACHE: cache{compiled.recipe.compiled.indexed.base.functions.length}/table{profile.table.rows.length}"
  require (compiled.recipe.compiled.indexed.base.functions.length == 20 && profile.table.rows.length == 20)
    "primitive original cache/table changed"
  rawGuards compiled profile
  let complement ← row compiled "complement"
  let shape ← observeComplement complement
  let value := Word.ofNatModulo 37
  let started ← start compiled complement.row.key [.word value]
  have _sourceFirst : ∀ invocation, ∃ issued : SelectedCompilationCertifiedPublicSession.Profiled compiled.recipe,
      Nonempty (Conclusion issued started invocation) := fun invocation => from_source shape profile started invocation
  let .outOfFuel suspended ← started.call.checkpoint.resume 0 0
    | throw (IO.userError "primitive initial zero fuel did not suspend")
  let .succeeded first ← suspended.resume 100000 1000
    | throw (IO.userError "primitive source-first complement failed")
  require (first.value == .word value.bitNot) "primitive source-first complement result changed"
  let after ← success compiled first.session "add" [word 17, word 25] (word 42)
  let after ← success compiled after "sub" [word 17, word 25] (.word ((Word.ofNatModulo 17).sub (Word.ofNatModulo 25)))
  let after ← success compiled after "mul" [word 6, word 7] (word 42)
  let after ← success compiled after "divide" [word 43, word 7] (word 6)
  let after ← success compiled after "modulo" [word 43, word 7] (word 1)
  let after ← success compiled after "band" [word 13, word 6] (word 4)
  let after ← success compiled after "bxor" [word 13, word 6] (word 11)
  let after ← success compiled after "bor" [word 13, word 6] (word 15)
  let after ← success compiled after "gt" [word 8, word 3] (.bool true)
  let after ← success compiled after "eq" [word 8, word 3] (.bool false)
  let after ← success compiled after "conjunction" [.bool true, .bool false] (.bool false)
  let after ← success compiled after "disjunction" [.bool false, .bool true] (.bool true)
  let after ← success compiled after "negation" [.bool true] (.bool false)
  let after ← success compiled after "literal" [] (word 17)
  let after ← success compiled after "hugeLiteral" [] (word 5)
  let after ← success compiled after "nested" [.bool true, word 5] (.product (word 7) (.bool true))
  let after ← success compiled after "nested" [.bool false, word 5] (.product (word 15) (.bool true))
  let after ← success compiled after "builtin" [] (word 1)
  let after ← success compiled after "lessCall" [word 3, word 8] (.bool true)
  require ([started.session.heapSize, first.session.heapSize, after.heapSize] == [21, 24, 123]) "primitive exact public heaps changed"
  IO.println s!"PRIMITIVE_HEAPS: initial{started.session.heapSize}; complement{first.session.heapSize}; final{after.heapSize}"
  IO.println "PRIMITIVE_COMPILER_PROFILE_FORWARD_PASS: unchanged original primitive program; actual whole profile and automatic startup; independent ordinary complement trace to closed public forward; exact builtin and ordered binary operands; zero-fuel resume"

end Tests.SourceCoreSelectedPrimitiveProfile
end
