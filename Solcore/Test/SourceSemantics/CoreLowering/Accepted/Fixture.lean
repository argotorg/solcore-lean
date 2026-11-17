import Solcore.SourceSemantics.CoreLowering

/-!
# Accepted-body fixtures

A compiled program of any workspace, with what the accepted-body public
theorems take from it: the cache rows and their original observations, a
complete inventory of issued headers, the selection of one row, a public start,
and the checks of every cache row that make the rows of a family of direct
calls.

Main declarations:
- `Tests.SourceCoreAcceptedFixture.CompiledFixture` and `compileFixture`;
- `Tests.SourceCoreAcceptedFixture.WholeInventory` and its `complete`;
- `Tests.SourceCoreAcceptedFixture.SelectedInventory` and its `root_selection`;
- `Tests.SourceCoreAcceptedFixture.CallRows` and `WholeInventory.family_row`, the
  rows of a family of direct calls;
- `Tests.SourceCoreAcceptedFixture.WholeInventory.callees`, the static receipts
  of the family's admitted callees.
-/

section
/-! The compiled program and its original rows. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreAcceptedFixture
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering

def observed (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
  if witness : p then pure ⟨witness⟩ else throw (IO.userError message)

def runOptions : SourceCoreExecution.RunOptions :=
  {executionFuel := 300000, outputValidationFuel := 1000}

structure CompiledFixture (workspace : Workspace.RawWorkspace) (options : SourceCoreCompiler.Options) where
  recipe : SourceCoreIndexedSession.Recipe
  checked : checkProgram workspace options.checkingFuel = .ok recipe.compiled.sourceProgram
  seeds : List SourceCompiler.Seed
  facade : SourceCoreExecution.Compiled
  accepted : SourceCompiler.compileChecked recipe.compiled.sourceProgram seeds options = .ok facade
  selected : RecursiveNamedPreparedStageContracts.PublicRecipe facade recipe

def compileFixture (workspace : Workspace.RawWorkspace) (options : SourceCoreCompiler.Options) :
    IO (CompiledFixture workspace options) := do
  match checked : checkProgram workspace options.checkingFuel with
  | .error errors => throw (IO.userError (reprStr errors))
  | .ok program =>
    let seeds := program.signatures.functions.map (fun signature => SourceCompiler.Seed.declaration signature.id)
    match generated : SourceCoreCompiler.compileChecked program seeds options with
    | .error error => throw (IO.userError (reprStr error))
    | .ok source =>
      match present : source.artifact? with
      | none => throw (IO.userError "accepted fixture artifact absent")
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

variable {workspace : Workspace.RawWorkspace} {options : SourceCoreCompiler.Options}

theorem CompiledFixture.ready (fixture : CompiledFixture workspace options) :
    SourceCoreIndexedSession.Recipe.prepare fixture.recipe.compiled = .ok fixture.recipe := by
  obtain ⟨_, _, _, ready⟩ := RecursiveNamedPreparedStageContracts.public_compilation fixture.accepted fixture.selected
  exact ready

structure Row (fixture : CompiledFixture workspace options) where
  original : SourceSpecialization.SpecializedFunction
  member : original ∈ fixture.recipe.compiled.validationPlan.specializations
  global : SourceCoreCalls.Signature
  index : Nat
  slot : CallableNamedMetadata.Slot fixture.recipe.compiled.indexed.base.globals index global
  globalKey : global.key = original.key
  substitution : original.parameterSubstitution = []
  ordinary : original.function.returnComptime = false
  ordinaryInputs : ∀ binder ∈ original.function.typedBody.inputs, binder.comptime = false

def observeRow (fixture : CompiledFixture workspace options) (name : String) : IO (Row fixture) := do
  let some signature := fixture.recipe.compiled.sourceProgram.signatures.functions.find? (fun signature => signature.name == name)
    | throw (IO.userError "accepted fixture original signature")
  match found : fixture.recipe.compiled.validationPlan.specializations.find?
      (fun row => decide (row.function.typedBody.owner = signature.id)) with
  | none => throw (IO.userError "accepted fixture original row")
  | some original =>
    match slot : fixture.recipe.compiled.indexed.base.globals.zipIdx.filter
        (fun pair => decide (pair.1.key = original.key)) with
    | [(global, index)] =>
      let ⟨globalKey⟩ ← observed (global.key = original.key) "accepted fixture global key"
      let ⟨substitution⟩ ← observed (original.parameterSubstitution = []) "accepted fixture substitution"
      let ⟨ordinary⟩ ← observed (original.function.returnComptime = false) "accepted fixture ordinary return"
      let ⟨ordinaryInputs⟩ ← observed (original.function.typedBody.inputs.all (fun binder => !binder.comptime) = true)
        "accepted fixture ordinary parameters"
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
    | _ => throw (IO.userError "accepted fixture unique physical slot")

end Tests.SourceCoreAcceptedFixture
end

section
/-! Every actual cached position receives its original static input and issued
Header. The ordered inventory is complete; selection never removes other rows. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreAcceptedFixture
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Issued Inventory headers)

variable {workspace : Workspace.RawWorkspace} {options : SourceCoreCompiler.Options}

structure CachedObservation (fixture : CompiledFixture workspace options) (named : SourceCoreGeneralFunctions.Function) where
  signature : ProgramFunctionSignature
  member : signature ∈ fixture.recipe.compiled.sourceProgram.signatures.functions
  declaration : named.specialized.declaration = signature.id
  substitution : named.specialized.parameterSubstitution = []
  ordinary : named.specialized.function.returnComptime = false
  parameters : ∀ binder ∈ named.specialized.function.typedBody.inputs, binder.comptime = false

def observeCached (fixture : CompiledFixture workspace options) (named : SourceCoreGeneralFunctions.Function) :
    IO (CachedObservation fixture named) := do
  match found : fixture.recipe.compiled.sourceProgram.signatures.functions.find?
      (fun signature => decide (named.specialized.declaration = signature.id)) with
  | none => throw (IO.userError "accepted fixture cached original signature")
  | some signature =>
    let ⟨substitution⟩ ← observed (named.specialized.parameterSubstitution = []) "accepted fixture cached substitution"
    let ⟨ordinary⟩ ← observed (named.specialized.function.returnComptime = false) "accepted fixture cached return"
    let ⟨parameters⟩ ← observed (named.specialized.function.typedBody.inputs.all (fun binder => !binder.comptime) = true)
      "accepted fixture cached parameters"
    return ⟨signature, List.mem_of_find?_eq_some found,
      by simpa only [decide_eq_true_eq] using List.find?_some found,
      substitution, ordinary, by
        intro binder member
        have admitted := List.all_eq_true.mp parameters binder member
        cases marker : binder.comptime <;> simp_all⟩

inductive ObservedCache (fixture : CompiledFixture workspace options) : List SourceCoreGeneralFunctions.Function → Type where
  | nil : ObservedCache fixture []
  | cons {named rest} (observation : CachedObservation fixture named) (tail : ObservedCache fixture rest) :
      ObservedCache fixture (named :: rest)

def observeCache (fixture : CompiledFixture workspace options) :
    (functions : List SourceCoreGeneralFunctions.Function) → IO (ObservedCache fixture functions)
  | [] => pure .nil
  | named :: rest => return .cons (← observeCached fixture named) (← observeCache fixture rest)

theorem ObservedCache.at_slot {fixture : CompiledFixture workspace options} {functions : List SourceCoreGeneralFunctions.Function}
    (cache : ObservedCache fixture functions) {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : functions[index]? = some named) : Nonempty (CachedObservation fixture named) := by
  induction cache generalizing index with
  | nil => cases selected
  | cons observation tail ih =>
    cases index with
    | zero => simp only [List.getElem?_cons_zero] at selected; cases selected; exact ⟨observation⟩
    | succ index => exact ih selected

structure WholeInventory (fixture : CompiledFixture workspace options) where
  inputs : List (Input fixture.recipe.compiled)
  rows : Inventory inputs
  positions : inputs.map (fun input => input.prepared.index) =
    (List.finRange fixture.recipe.compiled.indexed.base.functions.length).map Fin.val

theorem WholeInventory.distinct {fixture : CompiledFixture workspace options} (whole : WholeInventory fixture) :
    (whole.inputs.map (fun input => input.prepared.index)).Nodup := by
  rw [whole.positions]
  apply List.pairwise_map.mpr
  exact List.Pairwise.imp (fun different equal => different (Fin.ext equal)) (List.nodup_finRange _)

theorem WholeInventory.complete {fixture : CompiledFixture workspace options} (whole : WholeInventory fixture)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : fixture.recipe.compiled.indexed.base.functions[index]? = some named) :
    ∃ input ∈ whole.inputs, input.prepared.index = index ∧ input.prepared.named = named := by
  have bound := (List.getElem?_eq_some_iff.mp selected).1
  have member : index ∈ whole.inputs.map (fun input => input.prepared.index) := by
    rw [whole.positions]
    exact List.mem_map.mpr ⟨⟨index, bound⟩, List.mem_finRange _, rfl⟩
  obtain ⟨input, present, same⟩ := List.mem_map.mp member
  have found := input.prepared.selected
  rw [same] at found
  exact ⟨input, present, same, Option.some.inj (found.symm.trans selected)⟩

/-- The full list of actual slots is traversed directly. All ordinary source
facts are finite observations, while origin and Header issuance come from the
real preparation and original declarative program typing. -/
theorem CompiledFixture.inventory (fixture : CompiledFixture workspace options)
    (cache : ObservedCache fixture fixture.recipe.compiled.indexed.base.functions)
    (wellFormed : ProgramWellFormed (Program.ofChecked fixture.recipe.compiled.sourceProgram)) :
    Nonempty (WholeInventory fixture) := by
  classical
  let functions := fixture.recipe.compiled.indexed.base.functions
  have available : ∀ position : Fin functions.length, ∃ input : Input fixture.recipe.compiled,
      input.prepared.index = position.val ∧ input.prepared.named = functions[position.val] := by
    intro position
    have selected : functions[position.val]? = some functions[position.val] := List.getElem?_eq_getElem position.isLt
    obtain ⟨observation⟩ := cache.at_slot selected
    have origin := SelectedCompilationCatalog.ordinary_origin fixture.recipe.compiled
      wellFormed.signatures (RecursiveNamedPreparedFinalPlanOrigins.final_member _ selected rfl)
      observation.member observation.declaration
    have range : SourceSemantics.ParameterSubstitution.RangeWellFormed
        (Context.ofSignatures fixture.recipe.compiled.sourceProgram.signatures)
        functions[position.val].specialized.parameterSubstitution := by
      rw [observation.substitution]
      intro name value found
      cases found
    obtain ⟨input, _row, slot, named⟩ := SelectedCompilationCatalog.of_cached fixture.recipe.compiled
      wellFormed.signatures selected origin range observation.ordinary observation.parameters
    exact ⟨input, slot, named⟩
  let choose := fun position => Classical.choose (available position)
  have chosen := fun position => Classical.choose_spec (available position)
  let inputs := (List.finRange functions.length).map choose
  obtain ⟨rows⟩ := CallableIndexedOwnedPreparedFiniteNamedInventories.inventory wellFormed inputs
  refine ⟨⟨inputs, rows, ?_⟩⟩
  simp only [inputs, List.map_map]
  exact List.map_congr_left (fun position _ => (chosen position).1)

structure SelectedInventory {fixture : CompiledFixture workspace options} (whole : WholeInventory fixture)
    (row : Row fixture) where
  input : Input fixture.recipe.compiled
  original : input.row = row.original
  packet : Issued input
  retained : Inventory.HasRow packet whole.rows

theorem WholeInventory.select {fixture : CompiledFixture workspace options} (whole : WholeInventory fixture)
    (row : Row fixture) : Nonempty (SelectedInventory whole row) := by
  obtain ⟨index, named, selected, same⟩ := RecursiveNamedPublicSpecializationMeaning.cached_row
    fixture.recipe.compiled row.member
  obtain ⟨input, present, _slot, selectedNamed⟩ := whole.complete selected
  obtain ⟨packet, retained⟩ := whole.rows.row_at input present
  exact ⟨⟨input, input.prepared.same.symm.trans ((congrArg (·.specialized) selectedNamed).trans same), packet, retained⟩⟩

theorem SelectedInventory.header_original {fixture : CompiledFixture workspace options} {whole : WholeInventory fixture}
    {row : Row fixture} (selected : SelectedInventory whole row) :
    selected.packet.header.named.specialized = row.original :=
  (congrArg (·.specialized) selected.packet.aligned.named).trans
    (selected.input.prepared.same.trans selected.original)

theorem SelectedInventory.root_selection {fixture : CompiledFixture workspace options} {whole : WholeInventory fixture}
    {row : Row fixture} (selected : SelectedInventory whole row)
    {root : SourceCoreIndexedSession.Root fixture.recipe.compiled}
    (member : root ∈ fixture.recipe.roots) (key : root.key = row.original.key) :
    RecursiveNamedPublicRootMeaning.RootSelection
      (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      (program := Program.ofChecked fixture.recipe.compiled.sourceProgram)
      (headers whole.rows) root selected.packet.header := by
  obtain ⟨entry, present, shape⟩ := SourceCoreIndexedSession.Recipe.prepare_roots fixture.ready member
  obtain ⟨named, index, found, namedKey, rootKey, rest⟩ := shape
  have atIndex : fixture.recipe.compiled.indexed.base.functions[index]? = some named :=
    List.mk_mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some found)
  have selectedKey : selected.input.prepared.named.signature.key = row.original.key := by
    rw [CallableIndexedOwnedPreparedOrdinaryCachedInputs.cached_key _ selected.input.prepared.selected,
      selected.input.prepared.same, selected.original]
  have keyEq : named.signature.key = selected.input.prepared.named.signature.key :=
    namedKey.trans (rootKey.symm.trans (key.trans selectedKey.symm))
  have actualSlot := CallableIndexedOwnedPreparedOrdinaryCachedInputs.cached_slot _ atIndex
  have selectedSlot := selected.input.slot
  unfold CallableNamedMetadata.Slot at actualSlot selectedSlot
  rw [keyEq] at actualSlot
  have sameSlot := congrArg (fun entries => entries.head?) (selectedSlot.symm.trans actualSlot)
  have indexEq : selected.input.prepared.index = index := congrArg Prod.snd (Option.some.inj sameSlot)
  have actualNamed := selected.input.prepared.selected
  rw [indexEq] at actualNamed
  have same : selected.input.prepared.named = named := Option.some.inj (actualNamed.symm.trans atIndex)
  refine ⟨Inventory.header_member selected.retained, entry, present,
    ⟨named, index, found, namedKey, rootKey, rest⟩, ?_⟩
  rw [selected.packet.aligned.named, selected.packet.aligned.slot]
  change _ = some (selected.input.prepared.named, selected.input.prepared.index)
  simpa only [same, indexEq] using found

theorem SelectedInventory.source_eq {fixture : CompiledFixture workspace options} {whole : WholeInventory fixture}
    {row : Row fixture} (selected : SelectedInventory whole row) :
    selected.packet.header.function.source = row.original.function.typedBody :=
  selected.packet.header.agreement.source.trans
    (congrArg (fun named => named.function.typedBody) selected.header_original)

theorem SelectedInventory.result_eq {fixture : CompiledFixture workspace options} {whole : WholeInventory fixture}
    {row : Row fixture} (selected : SelectedInventory whole row) :
    selected.packet.header.function.resultType = row.original.function.inferredBodyType :=
  selected.packet.header.agreement.result.trans
    (congrArg (fun named => named.function.inferredBodyType) selected.header_original)

/-- An issued packet of the inventory selects its header's own registry
scope. -/
theorem WholeInventory.invocation {fixture : CompiledFixture workspace options} (whole : WholeInventory fixture)
    {input : Input fixture.recipe.compiled} (packet : Issued input) (retained : Inventory.HasRow packet whole.rows) :
    ∃ sidecar : SourceCoreStageContracts.Sidecar,
      SourceCoreStageContracts.prepareSidecar fixture.recipe.compiled.indexed.base.plan
        packet.header.named.signature.key = .ok sidecar ∧
      (SelectedCompilationPhysicalProgramSupport.stages fixture.recipe.compiled).Closure
        packet.header.function (RecursiveStageRegistry.scope sidecar [] packet.header.function) := by
  obtain ⟨rawD, function, sourceAt⟩ :=
    (CallableIndexedOwnedPreparedFiniteNamedInventories.source_receipts whole.rows).receipts
      packet.header (CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory.header_member retained)
  obtain ⟨descriptor⟩ := SelectedCompilationCertifiedPublicSession.header_descriptor packet.header
  obtain ⟨sidecar, issued, _same, globalSelected, _declaration, _local, _evidence, _return, _analysis⟩ :=
    CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts.selected sourceAt
      (CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued input.prepared packet.selected)
      packet.aligned (SelectedCompilationPhysicalProgramSupport.stagePrepared fixture.recipe.compiled) descriptor
  refine ⟨sidecar, ?_, ?_⟩
  · simpa only [packet.aligned.named, CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued,
      RecursiveNamedPreparedCallEvidence.Prepared.signature_key input.prepared] using issued
  · rw [CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts.global_view sourceAt] at globalSelected
    exact globalSelected

end Tests.SourceCoreAcceptedFixture
end

section
/-! Actual opening, export-aware bootstrap and public input receipt, recorded
before resuming a selected function. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreAcceptedFixture
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open SelectedCompilationPublicSessionState (StartedCall)

variable {workspace : Workspace.RawWorkspace} {options : SourceCoreCompiler.Options}

structure Started (fixture : CompiledFixture workspace options) (key : SourceCoreIndexedSession.Key)
    (arguments : List SourceCorePublicValues.Value) where
  artifact : SourceCoreExecution.Artifact
  opened : artifact.CompiledAt fixture.facade
  bootstrap : SourceCoreExecution.Bootstrap artifact
  fresh : bootstrap.FreshAt
  authority : bootstrap.ExportAuthorityAt
  session : SourceCoreExecution.Session artifact
  ready : bootstrap.resume 100000 = .ready session
  call : StartedCall session key arguments runOptions

def observeStarted (fixture : CompiledFixture workspace options) (key : SourceCoreIndexedSession.Key)
    (arguments : List SourceCorePublicValues.Value) : IO (Started fixture key arguments) := do
  let opened ← fixture.facade.openWithReceipt
  let bootstrap ← opened.val.bootstrapWithExportReceipt
  match ready : bootstrap.val.resume 100000 with
  | .error error => throw (IO.userError (reprStr error))
  | .outOfFuel _ => throw (IO.userError "accepted fixture bootstrap exhausted")
  | .ready session =>
    match started : session.start key arguments runOptions.inputValidationFuel with
    | .error error => throw (IO.userError (reprStr error))
    | .ok checkpoint => return ⟨opened.val, opened.property, bootstrap.val, bootstrap.property.1,
        bootstrap.property.2, session, ready, checkpoint, started⟩

end Tests.SourceCoreAcceptedFixture
end

section
/-! Every cache row of a program is checked: its expression nodes are
nested sites that call only the instantiations a family admits, its
statement list has a supported shape with those roots, and it has no evidence
assumptions. With a complete inventory the checks give each issued header its
accepted body, coverage, nested sites and call authority, and so a row of
the family. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreAcceptedFixture
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Issued Inventory headers)
open CellAwareInvocationAcceptedNestedTrees (Nested)
open CellAwareInvocationAcceptedBodyShape (Shape)
open CellAwareInvocationAcceptedNamedHeaders (index)

variable {workspace : Workspace.RawWorkspace} {options : SourceCoreCompiler.Options}

/-- The checks of one cache row: its expression nodes are nested sites that
call only instantiations `called` admits, or declaration references the plan
records no reference edge for. -/
structure CallRow (fixture : CompiledFixture workspace options) (called : DeclarationInstantiation → Prop)
    (named : SourceCoreGeneralFunctions.Function) where
  nodes : ∀ id node, (CallableIndexedNamedGeneration.source named).lookupExpression? id = some node →
    CellAwareInvocationAcceptedNestedCheck.Checked fixture.recipe.compiled.indexed named
      (CallableIndexedNamedGeneration.source named) called id
  statements : List StatementId
  roots : (CallableIndexedNamedGeneration.source named).roots = statements.map NodeId.statement
  shape : Shape (CallableIndexedNamedGeneration.source named) named.specialized.function.inferredBodyType
    (Nested fixture.recipe.compiled.indexed named (CallableIndexedNamedGeneration.source named) called) true
    statements
  assumptions : named.specialized.assumptions = []

def observeCallRow (fixture : CompiledFixture workspace options) (called : DeclarationInstantiation → Prop)
    [DecidablePred called] (named : SourceCoreGeneralFunctions.Function) : IO (CallRow fixture called named) := do
  let source := CallableIndexedNamedGeneration.source named
  let some ⟨nodes⟩ := CellAwareInvocationAcceptedNestedCheck.nodes? fixture.recipe.compiled.indexed named source
      called
    | throw (IO.userError "accepted fixture row outside the nested sites")
  let statements := source.roots.filterMap fun root =>
    match root with
    | .statement id => some id
    | .expression _ => none
  let ⟨roots⟩ ← observed (source.roots = statements.map NodeId.statement) "accepted fixture statement roots"
  let some ⟨shape⟩ := CellAwareInvocationAcceptedBodyShape.shapeWith? source
      named.specialized.function.inferredBodyType _
      (CellAwareInvocationAcceptedNestedCheck.nested? fixture.recipe.compiled.indexed named source called
        (source.nodes.length + 1))
      (source.nodes.length + 1) true statements
    | throw (IO.userError "accepted fixture statement shape")
  match assumptions : named.specialized.assumptions with
  | [] => return ⟨nodes, statements, roots, shape, assumptions⟩
  | _ :: _ => throw (IO.userError "accepted fixture row assumptions")

inductive CallRows (fixture : CompiledFixture workspace options) (called : DeclarationInstantiation → Prop) :
    List SourceCoreGeneralFunctions.Function → Type where
  | nil : CallRows fixture called []
  | cons {named rest} (row : CallRow fixture called named) (tail : CallRows fixture called rest) :
      CallRows fixture called (named :: rest)

def observeCallRows (fixture : CompiledFixture workspace options) (called : DeclarationInstantiation → Prop)
    [DecidablePred called] :
    (functions : List SourceCoreGeneralFunctions.Function) → IO (CallRows fixture called functions)
  | [] => pure .nil
  | named :: rest => return .cons (← observeCallRow fixture called named) (← observeCallRows fixture called rest)

theorem CallRows.at_slot {fixture : CompiledFixture workspace options} {called : DeclarationInstantiation → Prop}
    {functions : List SourceCoreGeneralFunctions.Function}
    (calls : CallRows fixture called functions) {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : functions[index]? = some named) : Nonempty (CallRow fixture called named) := by
  induction calls generalizing index with
  | nil => cases selected
  | cons row tail ih =>
    cases index with
    | zero => simp only [List.getElem?_cons_zero] at selected; cases selected; exact ⟨row⟩
    | succ index => exact ih selected

private theorem statement_roots {left right : List StatementId}
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

/-- The accepted body, its coverage, its nested sites and its call
authority at the header of an issued packet, from the checks of the packet's
cache row. -/
theorem WholeInventory.call_inputs {fixture : CompiledFixture workspace options} (whole : WholeInventory fixture)
    {called : DeclarationInstantiation → Prop}
    (calls : CallRows fixture called fixture.recipe.compiled.indexed.base.functions)
    {input : Input fixture.recipe.compiled} (packet : Issued input) :
    ∃ body : AcceptedNamedBodyFlow.Body
        (index (CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued input.prepared packet.selected)
          packet.aligned).policy
        (index (CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued input.prepared packet.selected)
          packet.aligned).fuel
        (index (CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued input.prepared packet.selected)
          packet.aligned).compilerSource
        (index (CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued input.prepared packet.selected)
          packet.aligned).scope
        (index (CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued input.prepared packet.selected)
          packet.aligned).statements
        (index (CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued input.prepared packet.selected)
          packet.aligned).result
        (index (CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued input.prepared packet.selected)
          packet.aligned).reasonAt
        (index (CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued input.prepared packet.selected)
          packet.aligned).fellThrough
        (index (CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued input.prepared packet.selected)
          packet.aligned).escaped
        (index (CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued input.prepared packet.selected)
          packet.aligned).body,
      CellAwareInvocationAcceptedFlow.Covered
        (index (CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued input.prepared packet.selected)
          packet.aligned).source packet.header.function.resultType
        (CellAwareInvocationAcceptedMatches.Admitted
          (index (CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued input.prepared packet.selected)
            packet.aligned))
        (CellAwareInvocationAcceptedInputs.Generalized (attachment := fun _ _ _ => True)
          (index (CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued input.prepared packet.selected)
            packet.aligned)) body.tree ∧
      CellAwareInvocationAcceptedNestedExpressions.ClosedNested
        (CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued input.prepared packet.selected).compilation
        (CellAwareInvocationAcceptedNamedHeaders.record
          (CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued input.prepared packet.selected) packet.aligned)
        called ∧
      CellAwareInvocationAcceptedCallExpressions.Ports (headers := headers whole.rows)
        (CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued input.prepared packet.selected).compilation
        (CellAwareInvocationAcceptedNamedHeaders.record
          (CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued input.prepared packet.selected) packet.aligned) := by
  obtain ⟨call⟩ := calls.at_slot input.prepared.selected
  let prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued input.prepared packet.selected
  obtain ⟨body, ready⟩ := CellAwarePublicAcceptedNamedRoot.refined_body prepared packet.aligned
  have sourceEq : packet.header.function.source = CallableIndexedNamedGeneration.source input.prepared.named := by
    rw [packet.header.agreement.source, packet.aligned.named]
    rfl
  have bodyEq : packet.header.function.body = call.statements := by
    have roots : packet.header.function.source.roots = call.statements.map NodeId.statement := by
      rw [sourceEq]
      exact call.roots
    exact statement_roots (packet.header.agreement.roots.symm.trans roots)
  have indexStatements : (index prepared packet.aligned).statements = call.statements := by
    have same : packet.header.function.body = prepared.compilation.statements := by
      rw [packet.aligned.function]
      rfl
    exact same.symm.trans bodyEq
  have resultEq : packet.header.function.resultType = input.prepared.named.specialized.function.inferredBodyType := by
    rw [packet.header.agreement.result, packet.aligned.named]
    rfl
  have indexShape : Shape (index prepared packet.aligned).compilerSource packet.header.function.resultType
      (Nested fixture.recipe.compiled.indexed input.prepared.named
        (CallableIndexedNamedGeneration.source input.prepared.named) called) true
      (index prepared packet.aligned).statements := by
    rw [indexStatements, resultEq]
    exact call.shape
  have covered := CellAwareInvocationAcceptedBodyShape.covered (index prepared packet.aligned) rfl body.tree
    (semantic := (index prepared packet.aligned).source)
    (expected := packet.header.function.resultType)
    (admitted := CellAwareInvocationAcceptedMatches.Admitted (index prepared packet.aligned))
    (generalized := CellAwareInvocationAcceptedInputs.Generalized (attachment := fun _ _ _ => True)
      (index prepared packet.aligned))
    ready indexShape
  exact ⟨body, covered,
    CellAwareInvocationAcceptedNestedCheck.closedNested prepared.compilation
      (CellAwareInvocationAcceptedNamedHeaders.record prepared packet.aligned) call.nodes,
    CellAwareInvocationAcceptedCallAuthority.ports whole.rows whole.complete prepared.compilation
      (CellAwareInvocationAcceptedNamedHeaders.record prepared packet.aligned)⟩

/-- Every issued header of a complete inventory whose cache rows are all
checked is a row of the family. -/
theorem WholeInventory.family_row {fixture : CompiledFixture workspace options} (whole : WholeInventory fixture)
    {called : DeclarationInstantiation → Prop}
    (calls : CallRows fixture called fixture.recipe.compiled.indexed.base.functions)
    (support : SelectedCompilationNamedSupport.Support fixture.recipe.compiled)
    {entry : SourceCoreCallableIndexedPrograms.Entry fixture.recipe.compiled.indexed.layouts}
    (entryMember : entry ∈ fixture.recipe.compiled.indexed.entries)
    {header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    (member : header ∈ headers whole.rows) :
    Nonempty (CellAwareInvocationAcceptedCallFamily.Row (headers := headers whole.rows) called header) := by
  obtain ⟨input, packet, retained, same⟩ := whole.rows.mem_headers header member
  subst same
  let prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued input.prepared packet.selected
  have diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared :=
    ⟨packet.selected.diagnostics, packet.selected.found, rfl⟩
  obtain ⟨_source, _signatures, _typing, projection, native⟩ :=
    CellAwareInvocationAcceptedNamedHeaders.static_inputs prepared packet.aligned fixture.ready entryMember
      (support.certified packet.header)
  have issuer := CellAwareNamedDiagnosticIssuer.of_prepared prepared diagnostic packet.aligned
  rw [packet.aligned.reasonAt, packet.aligned.named] at issuer
  obtain ⟨body, covered, closed, ports⟩ := whole.call_inputs calls packet
  obtain ⟨_sidecar, _issued, bodySelected⟩ := whole.invocation packet retained
  exact ⟨{
    named := prepared.named
    diagnostics := prepared.diagnostics
    code := _
    generation := prepared.compilation
    record := CellAwareInvocationAcceptedNamedHeaders.record prepared packet.aligned
    sameNamed := packet.aligned.named
    sameLayouts := packet.aligned.layouts
    sameGlobals := packet.aligned.globals
    sameBindings := packet.aligned.bindings
    sameBody := packet.aligned.body
    sameSolved := packet.aligned.solved
    projection := projection
    issued := CallableIndexedOwnedIssuedAssignmentRecipes.of_prepared prepared diagnostic
    assignments := CallableIndexedOwnedPublicDiagnosticReceipts.assignments_prepared prepared diagnostic
    body := body
    covered := covered
    native := native
    issuer := issuer
    closed := closed
    ports := ports
    bodyScope := _
    bodySelected := bodySelected }⟩

end Tests.SourceCoreAcceptedFixture
end

section
/-! The checks of every cache row give each issued header its statement shape
and its empty dictionary, and the static receipts of the admitted callees of a
family whose instantiations are retained instantiations of cache rows: a
callee's body instance is its header's Source body, and its global view is its
header's function. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreAcceptedFixture
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Issued Inventory headers)
open CellAwareInvocationAcceptedNestedTrees (Nested)
open CellAwareInvocationAcceptedBodyShape (Shape)

variable {workspace : Workspace.RawWorkspace} {options : SourceCoreCompiler.Options}
  {fixture : CompiledFixture workspace options} {called : DeclarationInstantiation → Prop}

/-- A checked cache row's statement shape at the header of an issued packet. -/
theorem CallRows.header_shape (calls : CallRows fixture called fixture.recipe.compiled.indexed.base.functions)
    {input : Input fixture.recipe.compiled} (packet : Issued input) :
    Shape packet.header.function.source packet.header.function.resultType
      (Nested fixture.recipe.compiled.indexed input.prepared.named packet.header.function.source called) true
      packet.header.function.body := by
  obtain ⟨call⟩ := calls.at_slot input.prepared.selected
  have sourceEq : packet.header.function.source = CallableIndexedNamedGeneration.source input.prepared.named := by
    rw [packet.header.agreement.source, packet.aligned.named]
    rfl
  have bodyEq : packet.header.function.body = call.statements := by
    have roots : packet.header.function.source.roots = call.statements.map NodeId.statement := by
      rw [sourceEq]
      exact call.roots
    exact statement_roots (packet.header.agreement.roots.symm.trans roots)
  have resultEq : packet.header.function.resultType =
      input.prepared.named.specialized.function.inferredBodyType := by
    rw [packet.header.agreement.result, packet.aligned.named]
    rfl
  rw [bodyEq, resultEq, sourceEq]
  exact call.shape

/-- A checked cache row has no evidence assumptions, so the dictionary of its
issued header is empty. -/
theorem CallRows.header_evidence (calls : CallRows fixture called fixture.recipe.compiled.indexed.base.functions)
    {input : Input fixture.recipe.compiled} (packet : Issued input) : packet.header.function.evidence = [] := by
  obtain ⟨call⟩ := calls.at_slot input.prepared.selected
  have closed : input.row.assumptions = [] := by
    rw [← input.prepared.same]
    exact call.assumptions
  rw [packet.function]
  exact RecursiveNamedPreparedHeaders.Prepared.evidence_empty input.prepared closed

private theorem statementRoots_functional {roots : List NodeId} {left right : List StatementId}
    (first : Dynamic.StatementRoots roots left) (second : Dynamic.StatementRoots roots right) : left = right := by
  induction first generalizing right with
  | nil =>
    cases second
    rfl
  | cons _ ih =>
    cases second with
    | cons tail => rw [ih tail]

/-- The static receipts of the admitted callees, when every instantiation the
family admits is the retained instantiation of a cache row and every cache row
is checked. -/
theorem WholeInventory.callees (whole : WholeInventory fixture)
    (calls : CallRows fixture called fixture.recipe.compiled.indexed.base.functions)
    (wellFormed : ProgramWellFormed (Program.ofChecked fixture.recipe.compiled.sourceProgram))
    (admitted : ∀ {instantiation}, called instantiation →
      ∃ callee : Row fixture, instantiation = CallableNamedCanonicalOrder.retainedInstantiation callee.original) :
    CellAwareInvocationAcceptedCallLifting.Callees fixture.recipe.compiled.indexed
      (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      (SelectedCompilationPhysicalProgramSupport.stages fixture.recipe.compiled) called := by
  intro instantiation bodyInstance roots admits instantiates rootsEq
  obtain ⟨callee, same⟩ := admitted admits
  subst same
  obtain ⟨selected⟩ := whole.select callee
  have frameInstantiated := selected.packet.header.frame.instantiated
  rw [selected.packet.aligned.metadata, selected.original] at frameInstantiated
  have bodySame := BuiltinNamedCalls.instantiation_unique_of_wellFormed wellFormed instantiates frameInstantiated
  subst bodySame
  have rootsSame := statementRoots_functional rootsEq selected.packet.header.frame.roots
  subst rootsSame
  have view : Staging.Recursive.globalView selected.packet.header.sourceBody [] selected.packet.header.function.body =
      selected.packet.header.function := by
    have same := CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts.global_view selected.packet.sourceAt
    rw [← selected.packet.sourceAt.dictionary, calls.header_evidence selected.packet] at same
    exact same
  obtain ⟨sidecar, _issued, closure⟩ := whole.invocation selected.packet selected.retained
  refine ⟨RecursiveStageRegistry.scope sidecar [] selected.packet.header.function, selected.input.prepared.named,
    selected.packet.header.function.resultType, ?_, ?_, ?_⟩
  · rw [view]
    exact closure
  · rw [← selected.packet.header.frame.source]
    exact selected.packet.header.unique
  · rw [← selected.packet.header.frame.source]
    exact calls.header_shape selected.packet

end Tests.SourceCoreAcceptedFixture
end
