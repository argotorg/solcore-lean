import Solcore.Test.SourceSemantics.CoreLowering.Accepted.Fixture
import Solcore.Test.SourceSemantics.CoreLowering.Direct.Calls

/-!
# One direct call at the accepted-body public root

`relay` returns `identity(value)`, a direct call of the program's other
function, at a `Word` parameter. Runtime checks place every expression node of
both rows among the extended roots that call `identity`'s instantiation, and
each statement list in the supported shape. With the complete inventory the
rows make a family, and the call root's theorems apply at `relay`'s first
public call.

Main declarations: `Tests.SourceCoreAcceptedOneCall.accepted_call` and the
runtime check `Tests.SourceCoreAcceptedOneCall.AcceptedCallRuntime.run`.
-/

section
/-! The program and the declarative typing of both functions, constructed from
checked source observations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreAcceptedOneCall
open Solcore Frontend SourceInference SourceSemantics
open Tests.SourceCoreAcceptedFixture (observed)

def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function identity(value: Word) returns (Word) { return value; }",
    "function relay(value: Word) returns (Word) { return identity(value); }" ]}] }

def options : SourceCoreCompiler.Options :=
  {checkingFuel := 1000, compilationFuel := 1000, specializationBudget := 128}

private theorem statementRoots_injective {left right : List StatementId}
    (equal : left.map NodeId.statement = right.map NodeId.statement) : left = right := by
  induction left generalizing right with
  | nil => cases right <;> simp at equal ⊢
  | cons head rest ih =>
    cases right with
    | nil => simp at equal
    | cons other tail =>
      simp only [List.map_cons, List.cons.injEq] at equal
      obtain ⟨same, tails⟩ := equal
      cases same
      simp only [ih tails]

/-- `relay`'s body: the read of its parameter, the direct call of `identity`
with it and the return of the call. -/
structure RelayShape (function : CheckedFunction) (signature identity : ProgramFunctionSignature) where
  binder : TypedBinder
  read : Tests.SourceCoreNamedBranch.Read function.typedBody binder .word
  call : Tests.SourceCoreDirectCalls.DirectCall function.typedBody identity read.node.id .word
  statement : StatementNode
  parameters : signature.scheme.parameters = []
  inputTypes : signature.parameterTypes = [.word]
  returns : signature.returnTypes = [.word]
  inputs : function.typedBody.inputs = [binder]
  binderScheme : binder.scheme = .mono .word
  binderRequirements : binder.schemeRequirements = []
  binderOrdinary : binder.comptime = false
  roots : function.typedBody.roots = [.statement statement.id]
  statementFound : function.typedBody.lookupStatement? statement.id = some statement
  statementForm : statement.form = .returnStmt (some call.value.node.id)
  statementType : statement.type = .word

theorem RelayShape.statementTyping {function : CheckedFunction} {signature identity : ProgramFunctionSignature}
    (shape : RelayShape function signature identity) (signatures : ProgramSignatures)
    (identityMember : identity ∈ signatures.functions) :
    CheckedBodyStatementsHaveType signatures signature function := by
  intro statements roots
  have same : statements = [shape.statement.id] := statementRoots_injective (roots.symm.trans shape.roots)
  subst statements
  rw [shape.returns]
  let facts : StatementFacts := {type := .word, hasValue := true, sawReturn := true, control := .returned}
  refine ⟨BodyFacts.singleton facts, rfl, ?_⟩
  intro lexical extension
  rw [shape.inputs, shape.inputTypes] at extension
  cases extension with
  | cons scheme head tail =>
    cases tail
    have binders : TypeParameterBindersWellFormed lexical := by
      rw [TypeParameterBindersWellFormed, head.context_fields.2.2.1]
      simp [checkedBodyContext, declarationContext, Context.ofSignatures, Context.forDeclaration,
        Context.withAssumptions, Context.withSolvedRequirements, Context.withResidualTypeVariables, shape.parameters]
    have fields : lexical.signatures = signatures := by
      rw [head.context_fields.1]
      rfl
    have word : TypeAdmissible lexical .word := ⟨binders, .builtin .word⟩
    have read := shape.read.typed scheme shape.binderRequirements word head.local_self head.local_scheme_requirements_self
    have called := shape.call.typed (fields ▸ identityMember) word read
    exact ⟨_, .singleton (.returnValue (lookupStatement?_sound shape.statementFound)
      shape.statementForm called shape.statementType)⟩

def observeRelay (function : CheckedFunction) (signature identity : ProgramFunctionSignature) :
    IO (RelayShape function signature identity) := do
  let [binder] := function.typedBody.inputs | throw (IO.userError "relay input")
  let [.expression read, .expression callee, .expression value, .statement statement] := function.typedBody.nodes
    | throw (IO.userError "relay original nodes")
  let read ← Tests.SourceCoreNamedBranch.observeRead function.typedBody binder read .word
  let call ← Tests.SourceCoreDirectCalls.observeDirect function.typedBody identity read.node.id callee value .word
  let ⟨parameters⟩ ← observed (signature.scheme.parameters = []) "relay parameters"
  let ⟨inputTypes⟩ ← observed (signature.parameterTypes = [.word]) "relay inputTypes"
  let ⟨returns⟩ ← observed (signature.returnTypes = [.word]) "relay returns"
  let ⟨inputs⟩ ← observed (function.typedBody.inputs = [binder]) "relay inputs"
  let ⟨binderScheme⟩ ← observed (binder.scheme = .mono .word) "relay binderScheme"
  let ⟨binderRequirements⟩ ← observed (binder.schemeRequirements = []) "relay binderRequirements"
  let ⟨binderOrdinary⟩ ← observed (binder.comptime = false) "relay binderOrdinary"
  let ⟨roots⟩ ← observed (function.typedBody.roots = [.statement statement.id]) "relay roots"
  let ⟨statementFound⟩ ← observed (function.typedBody.lookupStatement? statement.id = some statement)
    "relay statementFound"
  let ⟨statementForm⟩ ← observed (statement.form = .returnStmt (some call.value.node.id)) "relay statementForm"
  let ⟨statementType⟩ ← observed (statement.type = .word) "relay statementType"
  return ⟨binder, read, call, statement, parameters, inputTypes, returns, inputs, binderScheme, binderRequirements,
    binderOrdinary, roots, statementFound, statementForm, statementType⟩

/-- The declarative typing of the complete checked program. -/
def observeWellFormed {program : CheckedProgram}
    (checked : checkProgram workspace options.checkingFuel = .ok program) :
    IO (PLift (ProgramWellFormed (Program.ofChecked program))) := do
  match functions : program.functions, signatures : program.signatures.functions with
  | [identityFunction, relayFunction], [identitySignature, relaySignature] =>
    let identityShape ← Tests.SourceCoreOperatorCalls.observeIdentity identityFunction identitySignature
    let relayShape ← observeRelay relayFunction relaySignature identitySignature
    let ⟨methods⟩ ← observed (program.methods = []) "one call methods"
    let ⟨identityDeclaration⟩ ← observed (identityFunction.declaration = identitySignature.id)
      "one call identityDeclaration"
    let ⟨relayDeclaration⟩ ← observed (relayFunction.declaration = relaySignature.id) "one call relayDeclaration"
    let ⟨identityRelay⟩ ← observed (identitySignature.id ≠ relaySignature.id) "one call identityRelay"
    let deep : CheckedProgramBodiesHaveStatementTyping program options.checkingFuel := {
      functions := by
        intro actual member candidate candidateMember accepted
        have identity := checkFunctionBody_success_declaration accepted
        simp only [functions, List.mem_cons, List.not_mem_nil, or_false] at member
        simp only [signatures, List.mem_cons, List.not_mem_nil, or_false] at candidateMember
        rcases member with rfl | rfl <;> rcases candidateMember with rfl | rfl
        · exact identityShape.statementTyping program.signatures
        · exact False.elim (identityRelay (identityDeclaration.symm.trans identity))
        · exact False.elim (identityRelay (identity.symm.trans relayDeclaration))
        · exact relayShape.statementTyping program.signatures (by simp [signatures])
      methods := by intro method member; simp only [methods, List.not_mem_nil] at member }
    return ⟨programWellFormed_ofCheckProgram_statements checked deep⟩
  | _, _ => throw (IO.userError "one call declaration count")

/-- A row's only parameter is a `Word`. -/
structure WordInput (source : TypedSource) where
  binder : TypedBinder
  inputs : source.inputs = [binder]
  scheme : binder.scheme = .mono .word

def observeWordInput (source : TypedSource) : IO (WordInput source) := do
  let [binder] := source.inputs | throw (IO.userError "one call row input")
  let ⟨inputs⟩ ← observed (source.inputs = [binder]) "one call row inputs"
  let ⟨scheme⟩ ← observed (binder.scheme = .mono .word) "one call row scheme"
  return ⟨binder, inputs, scheme⟩

end Tests.SourceCoreAcceptedOneCall
end

section
/-! The accepted-body public theorems at the call root. Runtime checks place
every expression node of both rows among the extended roots and each statement
list in the supported shape; the complete inventory turns them into the rows
of a family, and with the existing start receipts they meet every premise of
the call root's checkpoint reflection theorem at `relay`'s first public call. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreAcceptedOneCall
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreAcceptedFixture
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys owner)

variable {fixture : CompiledFixture workspace options} {whole : WholeInventory fixture} {row : Row fixture}

theorem word_types (selected : SelectedInventory whole row)
    (input : WordInput row.original.function.typedBody) :
    selected.packet.header.types = [.word] := by
  have sourceInputs : selected.packet.header.function.source.inputs = [input.binder] := by
    rw [selected.source_eq]
    exact input.inputs
  have parameters : selected.packet.header.function.parameters = [input.binder] :=
    selected.packet.header.parameters.trans (selected.packet.header.inputs.symm.trans sourceInputs)
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq selected.packet.header.extended
  simpa only [parameters, List.map_cons, List.map_nil, input.scheme, TypeSystem.Scheme.mono] using types.symm

/-- The first public call of the row, with the conclusion of the call root's
checkpoint reflection theorem. -/
structure AcceptedCall (selected : SelectedInventory whole row) (word : Word)
    (started : Started fixture row.original.key [.word word]) where
  start : SelectedCompilationPublicSessionInitial.Started whole.rows fixture.ready selected.packet.header started.call
  reflects : ∀ fuel (value : Value) (finalStore : Store), start.checkpoint.NativeDone fuel value finalStore →
    ∃ (sidecar : SourceCoreStageContracts.Sidecar) (size : Nat) (environment : Dynamic.Environment)
      (bound : Dynamic.Heap) (finalContext : SourceSemantics.Context) (outcome : Staging.Recursive.BodyOutcome)
      (after : Dynamic.Heap),
      Dynamic.BindersAllocate [] ⟨[]⟩ selected.packet.header.function.parameters [.word word] environment bound ∧
      Staging.Recursive.Size.Statements (Program.ofChecked fixture.recipe.compiled.sourceProgram)
        (SelectedCompilationPhysicalProgramSupport.stages fixture.recipe.compiled) size
        (RecursiveStageRegistry.scope sidecar [] selected.packet.header.function) selected.packet.header.context
        environment bound selected.packet.header.function.body finalContext outcome after ∧
      Staging.Recursive.BodyResult selected.packet.header.function.resultType outcome
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome)

/-- Every premise is an original checked or static observation, a runtime check
of the program's rows, or an actual public start. The body's
accepted-expression meaning comes from the family of the checked rows. -/
theorem accepted_call (selected : SelectedInventory whole row) {called : DeclarationInstantiation → Prop}
    (calls : CallRows fixture called fixture.recipe.compiled.indexed.base.functions)
    (input : WordInput row.original.function.typedBody) (word : Word)
    (wellFormed : ProgramWellFormed (Program.ofChecked fixture.recipe.compiled.sourceProgram))
    (started : Started fixture row.original.key [.word word])
    (callableProfile : fixture.recipe.compiled.compatible.checked.catalog.callableContracts = true) :
    Nonempty (AcceptedCall selected word started) := by
  have support := SelectedCompilationNamedSupport.Support.of_program wellFormed
  obtain ⟨start⟩ := CellAwarePublicInitialSelectedStart.from_selected_call
    (rows := whole.rows) (prepared := fixture.ready) (header := selected.packet.header) (call := started.call)
    fixture.accepted fixture.selected started.opened started.bootstrap started.fresh
    started.authority (.single started.ready) (fun _ member key => selected.root_selection member key)
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      selected.packet.header.function.context [.word word] selected.packet.header.types := by
    rw [word_types selected input]
    exact .cons ⟨.word word, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word word⟩ .nil
  have inputMeanings : RecursiveNamedPublicDataInputs.Meanings [.word word] [.word word] :=
    .cons ⟨.word word, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word word⟩ .nil
  obtain ⟨origin, _contextAt, _issued, _extension⟩ := CellAwarePublicInitialStart.receiver start
  obtain ⟨initial⟩ := CellAwarePublicInitialStart.of_started whole.distinct callableProfile
    origin.result.context.registry (CallableIndexedOwnedPublicDecodedCallFaults.faults origin.result.diagnostics)
    support.bodyTyping start inputTypes inputMeanings
  let prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued selected.input.prepared selected.packet.selected
  have diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared :=
    ⟨selected.packet.selected.diagnostics, selected.packet.selected.found, rfl⟩
  obtain ⟨sidecar, _sidecarIssued, bodySelected⟩ := whole.invocation selected.packet selected.retained
  obtain ⟨body, covered, closed, ports⟩ := whole.call_inputs calls selected.packet
  obtain ⟨sourceCompiled, artifact, checked⟩ := CellAwarePublicAcceptedNamedRoot.compilation_receipts
    fixture.checked fixture.accepted fixture.selected
  obtain ⟨_entry, entryMember, _shape, _first⟩ := start.selected.2
  let rows : ∀ header, header ∈ headers whole.rows → called header.instantiation →
      CellAwareInvocationAcceptedCallFamily.Row (headers := headers whole.rows) called header :=
    fun _header member _ => Classical.choice (whole.family_row calls support entryMember member)
  refine ⟨⟨start, ?_⟩⟩
  intro fuel completedValue completedStore completed
  obtain ⟨_capture, size, environment, bound, finalContext, outcome, after, _finalMap, _finalWorld,
      allocated, staged, result, _named⟩ :=
    CellAwarePublicAcceptedCallRoot.checkpoint_reflects_selected callableProfile initial.issued prepared
      selected.packet.aligned fixture.ready diagnostic support start.selected (owner fixture.recipe.compiled)
      initial.caller.base.val initial.globalReference initial.keyPhysical initial.caller.physical initial.stable
      initial.heapTyped initial.argumentsTyped bodySelected artifact checked body covered initial.represented
      initial.heaps rfl start.started completed
      (CellAwarePublicAcceptedCallRoot.expressions_of_family callableProfile initial.issued prepared
        selected.packet.aligned diagnostic support artifact checked closed ports wellFormed rows)
  exact ⟨sidecar, size, environment, bound, finalContext, outcome, after, allocated, staged, result⟩

namespace AcceptedCallRuntime

def run : IO Unit := do
  let fixture ← compileFixture workspace options
  let cache ← observeCache fixture fixture.recipe.compiled.indexed.base.functions
  let identity ← observeRow fixture "identity"
  let target := CallableNamedCanonicalOrder.retainedInstantiation identity.original
  let calls ← observeCallRows fixture (fun instantiation => instantiation = target)
    fixture.recipe.compiled.indexed.base.functions
  let ⟨wellFormed⟩ ← observeWellFormed fixture.checked
  let relay ← observeRow fixture "relay"
  let input ← observeWordInput relay.original.function.typedBody
  let ⟨callableProfile⟩ ← observed (fixture.recipe.compiled.compatible.checked.catalog.callableContracts = true)
    "one call actual callable profile"
  for word in [Word.zero, Word.ofNatModulo 7] do
    let started ← observeStarted fixture relay.original.key [.word word]
    have _plan : ∃ (whole : WholeInventory fixture) (selected : SelectedInventory whole relay),
        Nonempty (AcceptedCall selected word started) := by
      obtain ⟨whole⟩ := fixture.inventory cache wellFormed
      obtain ⟨selected⟩ := whole.select relay
      exact ⟨whole, selected, accepted_call selected calls input word wellFormed started callableProfile⟩
    let result ← started.call.checkpoint.resumeWithReceipt runOptions.executionFuel runOptions.outputValidationFuel
    match result.val with
    | .succeeded returned =>
      unless returned.value == .word word do throw (IO.userError "accepted call output changed")
    | _ => throw (IO.userError "accepted call did not succeed")
  IO.println "ACCEPTED_CALL_PUBLIC_PASS"

end AcceptedCallRuntime

end Tests.SourceCoreAcceptedOneCall
end
