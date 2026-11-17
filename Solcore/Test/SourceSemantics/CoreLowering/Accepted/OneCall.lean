import Solcore.Test.SourceSemantics.CoreLowering.Accepted.Fixture
import Solcore.Test.SourceSemantics.CoreLowering.Direct.Calls

/-!
# One direct call at the accepted-body public root

`relay` returns `identity(value)`, a direct call of the program's other
function, at a `Word` parameter. Runtime checks place every expression node of
both rows among the extended roots that call `identity`'s instantiation, and
each statement list in the supported shape. With the complete inventory the
rows make a family and give the admitted callee's static receipts. `relay`'s
original Source execution, which runs `identity`'s body instance, is lifted to
a staged trace, and the call root's theorems apply at `relay`'s first public
call in both directions: the actual resumption succeeds, and actual native
completion reconstructs a staged Source execution.

Main declarations: `Tests.SourceCoreAcceptedOneCall.relay_source`,
`Tests.SourceCoreAcceptedOneCall.accepted_call` and the runtime check
`Tests.SourceCoreAcceptedOneCall.AcceptedCallRuntime.run`.
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
    "pragma solcore;",
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

end Tests.SourceCoreAcceptedOneCall
end

section
/-! The cache rows of both functions and their original Source executions:
`identity` returns its parameter, and `relay` returns the direct call of
`identity` with its parameter, whose global application runs a given body
invocation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreAcceptedOneCall
open Solcore Frontend SourceInference SourceSemantics
open Tests.SourceCoreAcceptedFixture (observed CompiledFixture)

/-- A heap with one more initialized `Word` cell. -/
def wordHeap (before : Dynamic.Heap) (word : Core.Word) : Dynamic.Heap :=
  ⟨before.cells ++ [{type := .word, value := some (.word word)}]⟩

/-- A binder at the next cell of a heap. -/
def wordEnvironment (binder : TypedBinder) (before : Dynamic.Heap) : Dynamic.Environment :=
  [(binder.id, ⟨before.cells.length⟩)]

/-- `identity`'s cache row: its `Word` parameter, the read of it and the return
of the read. -/
structure IdentityBody (source : TypedSource) where
  binder : TypedBinder
  read : Tests.SourceCoreNamedBranch.Read source binder .word
  statement : StatementNode
  inputs : source.inputs = [binder]
  binderScheme : binder.scheme = .mono .word
  roots : source.roots = [.statement statement.id]
  statementFound : source.lookupStatement? statement.id = some statement
  statementForm : statement.form = .returnStmt (some read.node.id)

def observeIdentityBody (source : TypedSource) : IO (IdentityBody source) := do
  let [binder] := source.inputs | throw (IO.userError "identity row input")
  let [.expression read, .statement statement] := source.nodes | throw (IO.userError "identity row nodes")
  let read ← Tests.SourceCoreNamedBranch.observeRead source binder read .word
  let ⟨inputs⟩ ← observed (source.inputs = [binder]) "identity row inputs"
  let ⟨binderScheme⟩ ← observed (binder.scheme = .mono .word) "identity row binderScheme"
  let ⟨roots⟩ ← observed (source.roots = [.statement statement.id]) "identity row roots"
  let ⟨statementFound⟩ ← observed (source.lookupStatement? statement.id = some statement)
    "identity row statementFound"
  let ⟨statementForm⟩ ← observed (statement.form = .returnStmt (some read.node.id)) "identity row statementForm"
  return ⟨binder, read, statement, inputs, binderScheme, roots, statementFound, statementForm⟩

/-- `relay`'s cache row: its `Word` parameter, the read of it, the direct call
of `identity` with the read at the instantiation `target`, and the return of
the call. -/
structure RelayBody (fixture : CompiledFixture workspace options) (target : DeclarationInstantiation)
    (source : TypedSource) where
  identity : ProgramFunctionSignature
  member : identity ∈ fixture.recipe.compiled.sourceProgram.signatures.functions
  binder : TypedBinder
  read : Tests.SourceCoreNamedBranch.Read source binder .word
  call : Tests.SourceCoreDirectCalls.DirectCall source identity read.node.id .word
  selects : call.instantiation = target
  statement : StatementNode
  inputs : source.inputs = [binder]
  binderScheme : binder.scheme = .mono .word
  roots : source.roots = [.statement statement.id]
  statementFound : source.lookupStatement? statement.id = some statement
  statementForm : statement.form = .returnStmt (some call.value.node.id)

def observeRelayBody (fixture : CompiledFixture workspace options) (target : DeclarationInstantiation)
    (source : TypedSource) : IO (RelayBody fixture target source) := do
  match found : fixture.recipe.compiled.sourceProgram.signatures.functions.find?
      (fun signature => signature.name == "identity") with
  | none => throw (IO.userError "relay row callee signature")
  | some identity =>
    let [binder] := source.inputs | throw (IO.userError "relay row input")
    let [.expression read, .expression callee, .expression value, .statement statement] := source.nodes
      | throw (IO.userError "relay row nodes")
    let read ← Tests.SourceCoreNamedBranch.observeRead source binder read .word
    let call ← Tests.SourceCoreDirectCalls.observeDirect source identity read.node.id callee value .word
    let ⟨selects⟩ ← observed (call.instantiation = target) "relay row call target"
    let ⟨inputs⟩ ← observed (source.inputs = [binder]) "relay row inputs"
    let ⟨binderScheme⟩ ← observed (binder.scheme = .mono .word) "relay row binderScheme"
    let ⟨roots⟩ ← observed (source.roots = [.statement statement.id]) "relay row roots"
    let ⟨statementFound⟩ ← observed (source.lookupStatement? statement.id = some statement)
      "relay row statementFound"
    let ⟨statementForm⟩ ← observed (statement.form = .returnStmt (some call.value.node.id))
      "relay row statementForm"
    return ⟨identity, List.mem_of_find?_eq_some found, binder, read, call, selects, statement, inputs,
      binderScheme, roots, statementFound, statementForm⟩

/-- The read of a parameter at the next cell of a heap. -/
theorem read_value {source : TypedSource} {binder : TypedBinder}
    (read : Tests.SourceCoreNamedBranch.Read source binder .word) {program : SourceSemantics.Program}
    {context : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment) (before : Dynamic.Heap)
    (word : Core.Word) :
    Dynamic.ExpressionEvaluates program context evidence source (wordEnvironment binder before)
      (wordHeap before word) read.node.id (.word word) (wordHeap before word) := by
  have allocation : Dynamic.Heap.Allocates before .word (some (.word word)) ⟨before.cells.length⟩
      (wordHeap before word) := .append
  apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound read.found)
  · rw [read.form]
    exact .local (by rw [read.requirements, read.coercions]; rfl) Dynamic.Environment.LooksUp.head
      allocation.reads_new rfl rfl
  · rw [read.coercions]
    exact .nil

/-- `identity`'s body returns its parameter's value. -/
theorem IdentityBody.trace {source : TypedSource} (body : IdentityBody source) {program : SourceSemantics.Program}
    {context : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment) (before : Dynamic.Heap)
    (word : Core.Word) :
    Dynamic.FunctionStatementsExecute program context evidence source (wordEnvironment body.binder before)
      (wordHeap before word) [body.statement.id] context (.returned (.word word)) (wordHeap before word) := by
  apply Dynamic.FunctionStatementsExecute.singleton (lookupStatement?_sound body.statementFound)
  · intro expression impossible
    rw [body.statementForm] at impossible
    cases impossible
  · exact .returnValue (lookupStatement?_sound body.statementFound) body.statementForm
      (read_value body.read evidence before word)

/-- `relay`'s body returns the value of its direct call, given the call's
validity and its global application. -/
theorem RelayBody.trace {fixture : CompiledFixture workspace options} {target : DeclarationInstantiation}
    {source : TypedSource} (body : RelayBody fixture target source) {program : SourceSemantics.Program}
    {context : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment) (before : Dynamic.Heap)
    (word : Core.Word) (valid : SourceSemantics.DeclarationInstantiation.Valid context body.call.instantiation)
    {after : Dynamic.Heap}
    (applies : Dynamic.CallableApplies program context evidence [] (wordHeap before word)
      (.global ⟨body.call.instantiation, []⟩) [.word word] (.word word) after) :
    Dynamic.FunctionStatementsExecute program context evidence source (wordEnvironment body.binder before)
      (wordHeap before word) [body.statement.id] context (.returned (.word word)) after := by
  have predicates : body.call.instantiation.predicates = [] := by
    simp [body.call.exact]
  have called : Dynamic.ExpressionEvaluates program context evidence source (wordEnvironment body.binder before)
      (wordHeap before word) body.call.value.node.id (.word word) after := by
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound body.call.value.found)
    · rw [body.call.form, body.call.value.requirements, body.call.value.coercions]
      exact .directCall (lookupExpression?_sound body.call.callee.found) body.call.calleeForm
        body.call.callee.requirements body.call.callee.coercions valid
        (.cons (read_value body.read evidence before word) .nil)
        (by
          rw [predicates]
          exact .intro (selected := []) (contextual := []) (signatureRequirements := []) rfl rfl .nil)
        applies
    · rw [body.call.value.coercions]
      exact .nil
  apply Dynamic.FunctionStatementsExecute.singleton (lookupStatement?_sound body.statementFound)
  · intro expression impossible
    rw [body.statementForm] at impossible
    cases impossible
  · exact .returnValue (lookupStatement?_sound body.statementFound) body.statementForm called

/-- The call's validity at any context with the program's signatures. -/
theorem RelayBody.valid {fixture : CompiledFixture workspace options} {target : DeclarationInstantiation}
    {source : TypedSource} (body : RelayBody fixture target source) {context : SourceSemantics.Context}
    (signatures : context.signatures = fixture.recipe.compiled.sourceProgram.signatures) :
    SourceSemantics.DeclarationInstantiation.Valid context body.call.instantiation := by
  rw [body.call.exact]
  refine .intro body.identity ?_ rfl ?_ ?_ ?_ ?_ rfl rfl
  · rw [signatures]
    exact body.member
  · simpa only [body.call.scheme] using SourceSemantics.ParameterSubstitution.exact_empty
  · intro name value found
    cases found
  · simp [body.call.scheme]
  · simp [body.call.scheme]

end Tests.SourceCoreAcceptedOneCall
end

section
/-! The accepted-body public theorems at the call root. Runtime checks place
every expression node of both rows among the extended roots and each statement
list in the supported shape; the complete inventory turns them into the rows
of a family and gives the admitted callee's static receipts. `relay`'s
original Source execution, which runs `identity`'s body instance, is lifted
through the checked shape, and with the existing start receipts the call root's
theorems apply at `relay`'s first public call in both directions. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreAcceptedOneCall
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreAcceptedFixture
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys owner)

variable {fixture : CompiledFixture workspace options} {whole : WholeInventory fixture} {row : Row fixture}

private theorem mono_signatures {owner : Resolved.DeclarationId} {context final : SourceSemantics.Context}
    {binders : List TypedBinder} {types : List TypeSystem.Ty}
    (extension : MonoBindersExtend owner context binders types final) : final.signatures = context.signatures := by
  induction extension with
  | nil => rfl
  | cons _ head _ ih => exact ih.trans head.context_fields.1

/-- A header's lexical context has the program's signatures. -/
theorem header_signatures
    (header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram)) :
    header.context.signatures = fixture.recipe.compiled.sourceProgram.signatures := by
  rw [mono_signatures header.extended, header.frame.context]
  cases header.frame.instantiated with
  | intro _ _ _ _ _ _ _ contextEq =>
    rw [contextEq]
    rfl

theorem word_types (selected : SelectedInventory whole row) {target : DeclarationInstantiation}
    (body : RelayBody fixture target row.original.function.typedBody) :
    selected.packet.header.types = [.word] := by
  have sourceInputs : selected.packet.header.function.source.inputs = [body.binder] := by
    rw [selected.source_eq]
    exact body.inputs
  have parameters : selected.packet.header.function.parameters = [body.binder] :=
    selected.packet.header.parameters.trans (selected.packet.header.inputs.symm.trans sourceInputs)
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq selected.packet.header.extended
  simpa only [parameters, List.map_cons, List.map_nil, body.binderScheme, TypeSystem.Scheme.mono] using types.symm

/-- The original Source execution of `relay`'s body at its header, after the
allocation of its parameter: the direct call's global application runs
`identity`'s body instance, its header's Source body, at the empty
dictionary. -/
theorem relay_source (selected : SelectedInventory whole row) {identity : Row fixture}
    (identitySelected : SelectedInventory whole identity) {called : DeclarationInstantiation → Prop}
    (calls : CallRows fixture called fixture.recipe.compiled.indexed.base.functions)
    (identityBody : IdentityBody identity.original.function.typedBody)
    (relayBody : RelayBody fixture (CallableNamedCanonicalOrder.retainedInstantiation identity.original)
      row.original.function.typedBody)
    (word : Word) :
    Dynamic.BindersAllocate [] ⟨[]⟩ selected.packet.header.function.parameters [.word word]
      (wordEnvironment relayBody.binder ⟨[]⟩) (wordHeap ⟨[]⟩ word) ∧
    Dynamic.FunctionStatementsExecute (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      selected.packet.header.context selected.packet.header.function.evidence selected.packet.header.function.source
      (wordEnvironment relayBody.binder ⟨[]⟩) (wordHeap ⟨[]⟩ word) selected.packet.header.function.body
      selected.packet.header.context (.returned (.word word)) (wordHeap (wordHeap ⟨[]⟩ word) word) := by
  have parameters : selected.packet.header.function.parameters = [relayBody.binder] := by
    have sourceInputs : selected.packet.header.function.source.inputs = [relayBody.binder] := by
      rw [selected.source_eq]
      exact relayBody.inputs
    exact selected.packet.header.parameters.trans (selected.packet.header.inputs.symm.trans sourceInputs)
  have allocation : Dynamic.Heap.Allocates ⟨[]⟩ .word (some (.word word))
      ⟨(⟨[]⟩ : Dynamic.Heap).cells.length⟩ (wordHeap ⟨[]⟩ word) := .append
  have allocated : Dynamic.BindersAllocate [] ⟨[]⟩ selected.packet.header.function.parameters [.word word]
      (wordEnvironment relayBody.binder ⟨[]⟩) (wordHeap ⟨[]⟩ word) := by
    rw [parameters]
    exact .cons (by simpa only [relayBody.binderScheme, TypeSystem.Scheme.mono] using allocation) (.nil _ _)
  have bodyEq : selected.packet.header.function.body = [relayBody.statement.id] := by
    have roots : selected.packet.header.function.source.roots = [relayBody.statement.id].map NodeId.statement := by
      rw [selected.source_eq]
      exact relayBody.roots
    exact statementRoots_injective (selected.packet.header.agreement.roots.symm.trans roots)
  have calleeSource : identitySelected.packet.header.sourceBody.source = identity.original.function.typedBody :=
    identitySelected.packet.header.frame.source.symm.trans identitySelected.source_eq
  have covers : Dynamic.EvidenceEnvironment.Covers identitySelected.packet.header.sourceBody.context [] := by
    have frameCovers := identitySelected.packet.header.frame.covers
    rw [calls.header_evidence identitySelected.packet] at frameCovers
    exact frameCovers
  have extended := identitySelected.packet.header.extended
  rw [identitySelected.packet.header.frame.parameters, identitySelected.packet.header.frame.source,
    identitySelected.packet.header.frame.context] at extended
  have rootsEq : Dynamic.StatementRoots identitySelected.packet.header.sourceBody.source.roots
      [identityBody.statement.id] := by
    rw [calleeSource, identityBody.roots]
    exact .cons .nil
  have calleeAllocation : Dynamic.Heap.Allocates (wordHeap ⟨[]⟩ word) .word (some (.word word))
      ⟨(wordHeap ⟨[]⟩ word).cells.length⟩ (wordHeap (wordHeap ⟨[]⟩ word) word) := .append
  have calleeAllocated : Dynamic.BindersAllocate [] (wordHeap ⟨[]⟩ word)
      identitySelected.packet.header.sourceBody.source.inputs [.word word]
      (wordEnvironment identityBody.binder (wordHeap ⟨[]⟩ word)) (wordHeap (wordHeap ⟨[]⟩ word) word) := by
    rw [calleeSource, identityBody.inputs]
    exact .cons (by simpa only [identityBody.binderScheme, TypeSystem.Scheme.mono] using calleeAllocation)
      (.nil _ _)
  have execute : Dynamic.FunctionStatementsExecute (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      identitySelected.packet.header.context [] identitySelected.packet.header.sourceBody.source
      (wordEnvironment identityBody.binder (wordHeap ⟨[]⟩ word)) (wordHeap (wordHeap ⟨[]⟩ word) word)
      [identityBody.statement.id] identitySelected.packet.header.context (.returned (.word word))
      (wordHeap (wordHeap ⟨[]⟩ word) word) := by
    rw [calleeSource]
    exact identityBody.trace [] (wordHeap ⟨[]⟩ word) word
  have instantiates := identitySelected.packet.header.frame.instantiated
  rw [identitySelected.packet.aligned.metadata, identitySelected.original, ← relayBody.selects] at instantiates
  have applies : Dynamic.CallableApplies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      selected.packet.header.context selected.packet.header.function.evidence [] (wordHeap ⟨[]⟩ word)
      (.global ⟨relayBody.call.instantiation, []⟩) [.word word] (.word word)
      (wordHeap (wordHeap ⟨[]⟩ word) word) :=
    .global instantiates rfl covers (.returned covers rootsEq extended calleeAllocated execute rfl)
  refine ⟨allocated, ?_⟩
  rw [bodyEq, selected.source_eq]
  exact relayBody.trace selected.packet.header.function.evidence ⟨[]⟩ word
    (relayBody.valid (header_signatures selected.packet.header)) applies

/-- The first public call of the row, with the conclusions of the call root's
output theorem, its checkpoint sufficiency theorem and its checkpoint
reflection theorem. -/
structure AcceptedCall (selected : SelectedInventory whole row) (word : Word)
    (started : Started fixture row.original.key [.word word]) where
  start : SelectedCompilationPublicSessionInitial.Started whole.rows fixture.ready selected.packet.header started.call
  output : ∃ requiredExecution requiredOutput, ∀ executionFuel outputFuel
      (outcome : SourceCoreExecution.Outcome started.artifact),
    requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
    started.call.checkpoint.ResumeAt executionFuel outputFuel outcome →
    ∃ (returned : SourceCoreExecution.Completion started.artifact)
      (actual : SourceCoreIndexedSession.Completion start.artifact)
      (generation : SourceCorePublicValues.ExportGeneration) (value : Value) (finalStore : Store),
      outcome = .succeeded returned ∧
      start.checkpoint.SucceededResultAt executionFuel outputFuel generation value finalStore actual ∧
      returned.IndexedAt actual
  native : ∃ (value : Value) (finalStore : Store) (required : Nat),
    ∀ fuel, required ≤ fuel → start.checkpoint.NativeDone fuel value finalStore
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
accepted-expression meaning comes from the family of the checked rows, and the
staged Source trace is lifted from `relay`'s original execution through the
checked shape, with the admitted callee's static receipts from the inventory. -/
theorem accepted_call (selected : SelectedInventory whole row) {identity : Row fixture}
    (identitySelected : SelectedInventory whole identity) {called : DeclarationInstantiation → Prop}
    (calls : CallRows fixture called fixture.recipe.compiled.indexed.base.functions)
    (admitted : ∀ {instantiation}, called instantiation →
      ∃ callee : Row fixture, instantiation = CallableNamedCanonicalOrder.retainedInstantiation callee.original)
    (identityBody : IdentityBody identity.original.function.typedBody)
    (relayBody : RelayBody fixture (CallableNamedCanonicalOrder.retainedInstantiation identity.original)
      row.original.function.typedBody)
    (word : Word)
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
    rw [word_types selected relayBody]
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
  obtain ⟨allocated, sourceTrace⟩ := relay_source selected identitySelected calls identityBody relayBody word
  obtain ⟨size, trace⟩ := CellAwareInvocationAcceptedCallLifting.body fixture.recipe.compiled.indexed
    (registry := SelectedCompilationPhysicalProgramSupport.stages fixture.recipe.compiled)
    ((SelectedCompilationPhysicalProgramSupport.stages fixture.recipe.compiled).source bodySelected)
    ((SelectedCompilationPhysicalProgramSupport.stages fixture.recipe.compiled).evidence bodySelected)
    selected.packet.header.unique (whole.callees calls wellFormed admitted) (calls.header_shape selected.packet)
    sourceTrace
  obtain ⟨_capture, _value, _finalStore, _finalMap, _finalWorld, requiredExecution, requiredOutput, _result, output⟩ :=
    CellAwarePublicAcceptedCallForward.first_value_selected callableProfile initial.issued prepared
      selected.packet.aligned fixture.ready diagnostic support start.selected (owner fixture.recipe.compiled)
      initial.caller.base.val initial.globalReference initial.keyPhysical initial.caller.physical initial.stable
      initial.heapTyped initial.argumentsTyped bodySelected artifact checked body covered initial.represented
      initial.heaps rfl start.started start.atCheckpoint
      (congrArg SourceCoreCompatibleValues.Context.registry initial.contextAt) initial.exportsReady allocated trace
      (CellAwarePublicAcceptedCallRoot.expressions_of_family callableProfile initial.issued prepared
        selected.packet.aligned diagnostic support artifact checked closed ports wellFormed rows size)
  obtain ⟨_capture, value, finalStore, _finalMap, _finalWorld, required, run, _result⟩ :=
    CellAwarePublicAcceptedCallRoot.checkpoint_has_sufficient_fuel_selected callableProfile initial.issued prepared
      selected.packet.aligned fixture.ready diagnostic support start.selected (owner fixture.recipe.compiled)
      initial.caller.base.val initial.globalReference initial.keyPhysical initial.caller.physical initial.stable
      initial.heapTyped initial.argumentsTyped bodySelected artifact checked body covered initial.represented
      initial.heaps rfl start.started allocated trace
      (CellAwarePublicAcceptedCallRoot.expressions_of_family callableProfile initial.issued prepared
        selected.packet.aligned diagnostic support artifact checked closed ports wellFormed rows size)
  refine ⟨⟨start, ⟨requiredExecution, requiredOutput, ?_⟩, ⟨value, finalStore, required, run⟩, ?_⟩⟩
  · intro executionFuel outputFuel outcome enoughExecution enoughOutput resumed
    obtain ⟨returned, actual, generation, _reached, same, succeeded, indexed, _⟩ :=
      output executionFuel outputFuel outcome enoughExecution enoughOutput resumed
    exact ⟨returned, actual, generation, _, _, same, succeeded, indexed⟩
  · intro fuel completedValue completedStore completed
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

/-- Each call starts a fresh actual session. The plan is kernel-checked against
whatever the observed compile, check, row and start receipts are; the resume
runs the real compiled code. -/
def run : IO Unit := do
  let fixture ← compileFixture workspace options
  let cache ← observeCache fixture fixture.recipe.compiled.indexed.base.functions
  let identity ← observeRow fixture "identity"
  let calls ← observeCallRows fixture
    (fun instantiation => instantiation = CallableNamedCanonicalOrder.retainedInstantiation identity.original)
    fixture.recipe.compiled.indexed.base.functions
  let ⟨wellFormed⟩ ← observeWellFormed fixture.checked
  let relay ← observeRow fixture "relay"
  let identityBody ← observeIdentityBody identity.original.function.typedBody
  let relayBody ← observeRelayBody fixture (CallableNamedCanonicalOrder.retainedInstantiation identity.original)
    relay.original.function.typedBody
  let ⟨callableProfile⟩ ← observed (fixture.recipe.compiled.compatible.checked.catalog.callableContracts = true)
    "one call actual callable profile"
  for word in [Word.zero, Word.ofNatModulo 7] do
    let started ← observeStarted fixture relay.original.key [.word word]
    have _plan : ∃ (whole : WholeInventory fixture) (selected : SelectedInventory whole relay),
        Nonempty (AcceptedCall selected word started) := by
      obtain ⟨whole⟩ := fixture.inventory cache wellFormed
      obtain ⟨selected⟩ := whole.select relay
      obtain ⟨identitySelected⟩ := whole.select identity
      exact ⟨whole, selected, accepted_call selected identitySelected calls (fun admits => ⟨identity, admits⟩)
        identityBody relayBody word wellFormed started callableProfile⟩
    let result ← started.call.checkpoint.resumeWithReceipt runOptions.executionFuel runOptions.outputValidationFuel
    match result.val with
    | .succeeded returned =>
      unless returned.value == .word word do throw (IO.userError "accepted call output changed")
    | _ => throw (IO.userError "accepted call did not succeed")
  IO.println "ACCEPTED_CALL_PUBLIC_PASS"

end AcceptedCallRuntime

end Tests.SourceCoreAcceptedOneCall
end
