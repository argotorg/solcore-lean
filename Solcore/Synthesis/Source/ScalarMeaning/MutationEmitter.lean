import Solcore.Synthesis.Source.MutationEmitter
import Solcore.Synthesis.Source.ScalarMeaning.FunctionEmitter
import Solcore.Synthesis.Source.ScalarMeaning.MutationPreservation

/-! Meaning preservation for the actual private-mutation emitter
(`Mutation.emit`, profile `runtime-mutation`). Helpers become free functions as
for the named-helper emitter. A Core cell is a mutable `sc_c<n>` local; the
Core program may end with allocated cells in its store, so the result is stated
for the Word that Core returns together with that final store. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.ScalarMeaning

open Solcore.Synthesis.Core (functionDAGExpression)
open Solcore.Synthesis.Core.LocalMutation (CheckedDAG Local initializerKind? infer?)
open Solcore.Synthesis.Source.MutationRenderer (Binding)

/-- Core returns `word` with enough fuel and every completed run returns it
with the same final store; the store keeps the cells the program allocated. -/
def CoreReturnsWithStore (program : Solcore.Core.Program) (word : Solcore.Core.Word) : Prop :=
  ∃ store : Solcore.Core.Store,
    (∃ required, ∀ fuel, required ≤ fuel →
      program.runStateful fuel = .done (.word word) store) ∧
    ∀ fuel value store', program.runStateful fuel = .done value store' →
      value = .word word ∧ store' = store

theorem runStateful_of_evaluates_store {program : Solcore.Core.Program}
    {word : Solcore.Core.Word} {store : Solcore.Core.Store}
    (evaluates : Solcore.Core.Evaluates [] [] program.body (.word word) store) :
    CoreReturnsWithStore program word := by
  refine ⟨store, Solcore.Core.evaluation_runStateful_complete_with_sufficient_fuel evaluates, ?_⟩
  intro fuel value store' completed
  obtain ⟨same, sameStore⟩ := Solcore.Core.evaluation_deterministic
    (Solcore.Core.runStateful_evaluation_sound completed) evaluates
  exact ⟨same, sameStore⟩

/-! ### Names -/

theorem cellTemp_valid (index : Nat) : ValidIdentifier (cellTemp index) := by
  refine ⟨'s', ['c', '_', 'c'] ++ Nat.toDigits 10 index, by simp [cellTemp], by decide, ?_⟩
  intro char mem
  rcases List.mem_append.mp mem with prefix_ | digit
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at prefix_
    rcases prefix_ with rfl | rfl | rfl <;> decide
  · exact (digit_classes (toDigits_mem digit)).2.2

theorem cellTemp_not_reserved (index : Nat) : isReserved (cellTemp index) = false := by
  have heads : ∀ word ∈ reservedWords, word.toList.head? ≠ some 's' := by decide
  have absent : cellTemp index ∉ reservedWords := by
    intro mem
    exact heads _ mem (by simp [cellTemp])
  cases reserved : isReserved (cellTemp index)
  · rfl
  · exact absurd (List.elem_iff.mp reserved) absent

/-- Every identifier used by rendered mutation statements is a binding, a
helper or a temporary. -/
theorem mutation_identifier_ok {bindings : List Binding} {functions : List String}
    {first last : Nat} {name : String}
    (bindingsOk : ∀ index found, nameAt bindings index = some found →
      ValidIdentifier found ∧ isReserved found = false)
    (functionsOk : ∀ function ∈ functions, ValidIdentifier function ∧
      isReserved function = false)
    (classified : (∃ index, nameAt bindings index = some name) ∨ name ∈ functions ∨
      TempIn first last name) :
    ValidIdentifier name ∧ isReserved name = false := by
  rcases classified with ⟨index, named⟩ | mem | ⟨index, same, _, _⟩
  · exact bindingsOk index name named
  · exact functionsOk name mem
  · rcases same with rfl | rfl
    · exact ⟨temporary_valid index, temporary_not_reserved index⟩
    · exact ⟨cellTemp_valid index, cellTemp_not_reserved index⟩

theorem single_binding_ok {name : String} (valid : ValidIdentifier name)
    (notReserved : isReserved name = false) :
    ∀ index found, nameAt [Binding.word name] index = some found →
      ValidIdentifier found ∧ isReserved found = false := by
  intro index found named
  cases index with
  | zero =>
      rw [nameAt_cons_zero] at named
      cases named
      exact ⟨valid, notReserved⟩
  | succ index => simp [nameAt] at named

theorem single_binding_fresh {name : String} (notTemp : ∀ index, name ≠ temporary index)
    (notCell : ∀ index, name ≠ cellTemp index) : NamesFresh [Binding.word name] 0 := by
  intro index found named
  cases index with
  | zero =>
      rw [nameAt_cons_zero] at named
      cases named
      intro position isTemp
      rcases isTemp with same | same
      · exact absurd same (notTemp position)
      · exact absurd same (notCell position)
  | succ index => simp [nameAt] at named

theorem single_binding_distinct (name : String) : NamesDistinct [Binding.word name] := by
  intro first second found one two
  cases first with
  | zero =>
      cases second with
      | zero => rfl
      | succ second => simp [nameAt] at two
  | succ first => simp [nameAt] at one

theorem single_binding_cells (name : String) (core : CoreValue)
    (environment : Solcore.Core.Environment) :
    CellsDistinct [Binding.word name] (core :: environment) := by
  intro first second location cellOne _
  obtain ⟨⟨_, found⟩, _⟩ := cellOne
  cases first with
  | zero => simp at found
  | succ first => simp at found

theorem single_binding_agree {name : String} {word : Solcore.Core.Word} {scope : Scope}
    {outer : Frames} (lookup : Frames.lookup (scope :: outer) name = some (.word word.val))
    (environment : Solcore.Core.Environment) (store : Solcore.Core.Store) :
    BindingsAgree (scope :: outer) [Binding.word name] (.word word :: environment) store := by
  intro index binding found
  cases index with
  | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at found
      subst found
      exact ⟨.word word, rfl, word, rfl, lookup⟩
  | succ index => simp at found

theorem cellTemp_ne_input (index : Nat) : "sc_input" ≠ cellTemp index := by
  intro same
  have chars := congrArg String.toList same
  simp [cellTemp] at chars

theorem cellTemp_ne_argument (index : Nat) : "sc_arg" ≠ cellTemp index := by
  intro same
  have chars := congrArg String.toList same
  simp [cellTemp] at chars

/-! ### The emitter's helper loop -/

theorem helperNames_length : (count : Nat) → (helperNames count).length = count
  | 0 => rfl
  | count + 1 => by simp [helperNames, helperNames_length count]

/-- The helper loop of `Mutation.emit`, by structural recursion. -/
def mutationLoop : List CoreExpr → Nat → List String → List String →
    Except EmitError (List String × List String)
  | [], _, names, lines => .ok (names, lines)
  | body :: rest, index, names, lines =>
      (MutationRenderer.render names .word [.word "sc_arg"] 4 0 body).bind fun rendered =>
        (MutationRenderer.requireValue rendered).bind fun result =>
          mutationLoop rest (index + 1) (Function.helperName index :: names)
            (lines ++
              ["function " ++ Function.helperName index ++ "(sc_arg: word) returns (word) {"] ++
              rendered.lines ++ ["    return " ++ result ++ ";", "}", ""])

theorem forIn_mutationLoop
    {step : CoreExpr × Nat → List String × List String →
      Except EmitError (ForInStep (List String × List String))}
    (stepEq : ∀ body index names lines, step (body, index) (names, lines) =
      (MutationRenderer.render names .word [.word "sc_arg"] 4 0 body).bind fun rendered =>
        (MutationRenderer.requireValue rendered).bind fun result =>
          .ok (.yield (Function.helperName index :: names,
            lines ++
              ["function " ++ Function.helperName index ++ "(sc_arg: word) returns (word) {"] ++
              rendered.lines ++ ["    return " ++ result ++ ";", "}", ""]))) :
    ∀ (bodies : List CoreExpr) (start : Nat) (names lines : List String),
      forIn (bodies.zipIdx start) (names, lines) step = mutationLoop bodies start names lines
  | [], _, _, _ => rfl
  | body :: rest, start, names, lines => by
      rw [List.zipIdx_cons, List.forIn_cons, stepEq, mutationLoop]
      cases MutationRenderer.render names .word [.word "sc_arg"] 4 0 body with
      | error error => rfl
      | ok rendered =>
          simp only [Except.bind]
          cases MutationRenderer.requireValue rendered with
          | error error => rfl
          | ok result => exact forIn_mutationLoop stepEq rest (start + 1) _ _

theorem Mutation.emit_success {graph : CheckedDAG} {emitted : EmittedProgram}
    (emitted_eq : Mutation.emit graph = .ok emitted) :
    ∃ (names lines : List String) (entry : MRendered) (result : String),
      mutationLoop graph.helpers 0 [] ["import * from std;", "import * from std.dispatch;", ""] =
        .ok (names, lines) ∧
      MutationRenderer.render names .word [.word "sc_input"] 8 0 graph.entry = .ok entry ∧
      entry.value = some result ∧
      emitted.source = String.intercalate "\n" (lines ++
        ["contract " ++ Mutation.contractName ++ " {",
          "    function " ++ Mutation.methodName ++ "(input: uint256) public returns (uint256) {",
          "        let sc_input: word = Typedef.rep(input);"] ++ entry.lines ++
        ["        return uint256(" ++ result ++ ");", "    }", "}"]) ++ "\n" := by
  unfold Mutation.emit at emitted_eq
  dsimp only at emitted_eq
  rw [forIn_mutationLoop (fun _ _ _ _ => rfl)] at emitted_eq
  cases loop : mutationLoop graph.helpers 0 []
    ["import * from std;", "import * from std.dispatch;", ""] with
  | error error =>
      rw [loop] at emitted_eq
      cases emitted_eq
  | ok loopResult =>
      obtain ⟨names, lines⟩ := loopResult
      rw [loop] at emitted_eq
      cases entry : MutationRenderer.render names .word [.word "sc_input"] 8 0 graph.entry with
      | error error =>
          simp only [bind, Except.bind, entry] at emitted_eq
          cases emitted_eq
      | ok rendered =>
          simp only [bind, Except.bind, entry] at emitted_eq
          cases value : MutationRenderer.requireValue rendered with
          | error error =>
              simp only [value] at emitted_eq
              cases emitted_eq
          | ok result =>
              simp only [value, pure, Except.pure, Except.ok.injEq] at emitted_eq
              subst emitted_eq
              exact ⟨names, lines, rendered, result, rfl, entry, requireValue_ok value, rfl⟩

/-- A newly declared helper extends the agreement between helper names and
Core closures. -/
theorem MFunctionsAgree.extend {functions : List (String × (List Value → Option Value))}
    {aliases : List (String × String)} {names : List String} {closures : List CoreValue}
    (agree : MFunctionsAgree ⟨functions, aliases⟩ names closures) {name : String}
    (fresh : name ∉ names) {meaning : List Value → Option Value}
    {parameterType resultType : Solcore.Core.Ty} {body : Solcore.Core.Expr}
    (behaves : ∀ (argument : Solcore.Core.Word) (store : Solcore.Core.Store),
      ∃ (result : Solcore.Core.Word) (store' : Solcore.Core.Store),
        Solcore.Core.Evaluates (.word argument :: closures) store body (.word result) store' ∧
        store.length ≤ store'.length ∧
        (∀ location, location < store.length → store'.read? location = store.read? location) ∧
        meaning [.word argument.val] = some (.word result.val)) :
    MFunctionsAgree ⟨(name, meaning) :: functions, aliases⟩ (name :: names)
      (.closure parameterType resultType body closures :: closures) := by
  intro index found foundName
  cases index with
  | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at foundName
      subst foundName
      refine ⟨parameterType, resultType, body, closures, rfl, fun argument store => ?_⟩
      obtain ⟨result, store', evaluates, grows, keeps, called⟩ := behaves argument store
      exact ⟨result, store', evaluates, grows, keeps, by rw [Context.call_cons_same]; exact called⟩
  | succ index =>
      simp only [List.getElem?_cons_succ] at foundName
      have different : name ≠ found := fun same =>
        fresh (same ▸ List.mem_of_getElem? foundName)
      obtain ⟨parameterType', resultType', body', captured, closureFound, behaves'⟩ :=
        agree index found foundName
      refine ⟨parameterType', resultType', body', captured, by simpa using closureFound,
        fun argument store => ?_⟩
      obtain ⟨result, store', evaluates, grows, keeps, called⟩ := behaves' argument store
      exact ⟨result, store', evaluates, grows, keeps,
        by rw [Context.call_cons_other different]; exact called⟩

theorem acceptsAt_kind {locals : List Local} {prior : Nat} {target : MTarget}
    {expression : CoreExpr}
    (accepted : Solcore.Synthesis.Core.LocalMutation.acceptsAt locals prior target expression =
      true) :
    initializerKind? locals prior expression = some target.toLocal := by
  unfold Solcore.Synthesis.Core.LocalMutation.acceptsAt at accepted
  cases inferred : infer? locals prior expression with
  | none =>
      rw [inferred] at accepted
      cases accepted
  | some found =>
      rw [inferred] at accepted
      have same : found = target := by
        cases found <;> cases target <;> first | rfl | cases accepted
      subst same
      exact MutationKinds.infer_toLocal inferred

theorem mutation_helpers_accepted {helpers : List CoreExpr}
    (accepted : Solcore.Synthesis.Core.LocalMutation.helpersAccepted helpers = true) :
    ∀ (index : Nat) (body : CoreExpr), helpers[index]? = some body →
      Solcore.Synthesis.Core.LocalMutation.acceptsAt [.word] (0 + index) .word body = true := by
  intro index body found
  have all := List.all_eq_true.mp accepted (body, index)
    (List.mem_zipIdx_iff_getElem?.mpr found)
  simpa using all

/-- The helper loop prints free functions whose meanings agree with the Core
closures of the binding chain, and whose evaluation keeps the caller's
store. -/
theorem mutationLoop_spec : ∀ (bodies : List CoreExpr) (start : Nat)
    (lines names' lines' : List String)
    (functions : List (String × (List Value → Option Value))) (closures : List CoreValue),
    mutationLoop bodies start (helperNames start) lines = .ok (names', lines') →
    (∀ (index : Nat) (body : CoreExpr), bodies[index]? = some body →
      Solcore.Synthesis.Core.LocalMutation.acceptsAt [.word] (start + index) .word body = true) →
    MFunctionsAgree ⟨functions, []⟩ (helperNames start) closures →
    ∃ declarations : List FunctionDecl,
      lines' = lines ++ declarations.flatMap FunctionDecl.lines ∧
      names' = helperNames (start + bodies.length) ∧
      (∀ declaration ∈ declarations, declaration.NamesOk ∧
        ∀ name ∈ declaration.identifiers, ValidIdentifier name) ∧
      MFunctionsAgree ⟨declareFunctions [] functions declarations, []⟩ names'
        (bodies.foldl closureStep closures)
  | [], start, lines, names', lines', functions, closures, loop, _, agree => by
      simp only [mutationLoop, Except.ok.injEq, Prod.mk.injEq] at loop
      obtain ⟨rfl, rfl⟩ := loop
      exact ⟨[], by simp, by simp, by simp, by simpa [declareFunctions] using agree⟩
  | body :: rest, start, lines, names', lines', functions, closures, loop, accepted, agree => by
      simp only [mutationLoop] at loop
      obtain ⟨rendered, renderedEquation, loop⟩ := except_bind_eq_ok loop
      obtain ⟨result, resultEquation, loop⟩ := except_bind_eq_ok loop
      have resultFound := requireValue_ok resultEquation
      have bodyKind : initializerKind? ([Binding.word "sc_arg"].map Binding.kind)
          (helperNames start).length body = some Local.word := by
        rw [helperNames_length]
        exact acceptsAt_kind (accepted 0 body rfl)
      obtain ⟨statements, lines₁, _, valueName, names, simulates⟩ :=
        (mutation_render_spec (admits := fun _ => True) body).1 (helperNames start) .word
          [.word "sc_arg"] 4 0 rendered bodyKind renderedEquation
          (single_binding_fresh argument_not_temporary cellTemp_ne_argument)
          (single_binding_distinct _)
      let declaration := helperDecl start statements result
      have behaves : ∀ (argument : Solcore.Core.Word) (store : Solcore.Core.Store),
          ∃ (value : Solcore.Core.Word) (store' : Solcore.Core.Store),
            Solcore.Core.Evaluates (.word argument :: closures) store body.toCore
              (.word value) store' ∧
            store.length ≤ store'.length ∧
            (∀ location, location < store.length →
              store'.read? location = store.read? location) ∧
            declaration.denote ⟨functions, []⟩ [.word argument.val] =
              some (.word value.val) := by
        intro argument store
        obtain ⟨core, store', scope', outer', _, evaluates, represents, exec, _, frame, _⟩ :=
          simulates ⟨functions, []⟩ (.word argument :: closures) store []
            [[("sc_arg", .word argument.val)]] trivial
            (single_binding_agree (by simp [Frames.lookup, Scope.get?]) closures store)
            (single_binding_cells _ _ _) (by simp) (by simpa using agree)
        rw [resultFound, Option.bind_some] at represents
        obtain ⟨value, rfl, lookup⟩ := represents
        refine ⟨value, store', evaluates, frame.1, fun location inBounds =>
          frame.2 location inBounds fun index isCell => ?_, ?_⟩
        · obtain ⟨⟨_, found⟩, _⟩ := isCell
          cases index with
          | zero => simp at found
          | succ index => simp at found
        · simp [declaration, helperDecl, FunctionDecl.denote, FunctionDecl.bindParameters,
            LocalType.admits, exec, Expr.eval, lookup]
      have extended := agree.extend (helperName_not_mem start) behaves
        (parameterType := Solcore.Core.Wire.Ty.toCore .word)
        (resultType := Solcore.Core.Wire.Ty.toCore .word)
      have restAccepted : ∀ (index : Nat) (body : CoreExpr), rest[index]? = some body →
          Solcore.Synthesis.Core.LocalMutation.acceptsAt [.word] (start + 1 + index) .word body =
            true := by
        intro index body found
        have accepted' := accepted (index + 1) body (by simpa using found)
        rwa [show start + (index + 1) = start + 1 + index by omega] at accepted'
      obtain ⟨declarations, rest₁, rest₂, rest₃, rest₄⟩ :=
        mutationLoop_spec rest (start + 1) _ names' lines' _ _ loop restAccepted extended
      have block :
          ["function " ++ Function.helperName start ++ "(sc_arg: word) returns (word) {"] ++
          rendered.lines ++ ["    return " ++ result ++ ";", "}", ""] =
          declaration.lines := by
        simp only [declaration, helperDecl, FunctionDecl.lines, lines₁, List.cons_append,
          List.nil_append, List.cons.injEq]
        refine ⟨?_, ?_⟩
        · apply String.toList_inj.mp
          simp [FunctionDecl.parameterText, LocalType.spelling]
        · simp [Expr.print]
      have argumentOk : ∀ index found, nameAt [Binding.word "sc_arg"] index = some found →
          ValidIdentifier found ∧ isReserved found = false :=
        single_binding_ok (keyword_valid (by decide)) (by decide)
      refine ⟨declaration :: declarations, ?_, ?_, ?_, rest₄⟩
      · rw [rest₁, List.flatMap_cons, ← block]
        simp [List.append_assoc]
      · rw [rest₂]
        simp only [List.length_cons]
        congr 1
        omega
      · intro other mem
        rcases List.mem_cons.mp mem with same | mem
        · subst same
          have bodyOk := fun name mem =>
            mutation_identifier_ok argumentOk helperNames_ok (names name mem)
          have valueOk := mutation_identifier_ok (functions := helperNames start) argumentOk
            helperNames_ok (valueName result resultFound).uses
          refine ⟨⟨helperName_not_reserved start, ?_, fun name mem => (bodyOk name mem).2, ?_⟩,
            ?_⟩
          · intro parameter mem
            simp only [declaration, helperDecl, List.mem_singleton] at mem
            subst mem
            decide
          · intro name mem
            simp only [declaration, helperDecl, Expr.identifiers, List.mem_singleton] at mem
            subst mem
            exact valueOk.2
          · intro name mem
            simp only [declaration, helperDecl, FunctionDecl.identifiers, List.map_cons,
              List.map_nil, List.cons_append, List.nil_append, List.mem_cons, List.mem_append,
              Expr.identifiers, List.not_mem_nil, or_false] at mem
            rcases mem with rfl | rfl | mem | rfl
            · exact helperName_valid start
            · exact keyword_valid (by decide)
            · exact (bodyOk name mem).1
            · exact valueOk.1
        · exact rest₃ other mem

/-! ### The emitted file -/

/-- The source file printed by the private-mutation emitter. -/
def mutationFile (declarations : List FunctionDecl) (body : List Stmt) (value : String) :
    SourceFile := {
  opcodeAliases := []
  functions := declarations
  contract := "SynthesizedMutation"
  method := (inputFile body value).method }

/-- **Private-mutation emitter preservation.** If the actual emitter succeeds,
its source text is the printing of a file with one free function per helper and
parses back to it. For every runtime input, calling `run(uint256)` under the
independent source semantics returns exactly the Word that the original Core
binding chain, applied to that input, returns. -/
theorem Mutation.emit_preserves_meaning {graph : CheckedDAG}
    {emitted : EmittedProgram} (emitted_eq : Mutation.emit graph = .ok emitted) :
    ∃ file : SourceFile, emitted.source = file.print ∧ parseSource emitted.source = some file ∧
      ∀ input : Solcore.Core.Word, ∃ word : Solcore.Core.Word,
        file.call "run" [input.val] = some word.val ∧
        CoreReturnsWithStore (graph.instantiate input).toCore word := by
  obtain ⟨names, lines, entry, result, loop, entryEquation, resultFound, source⟩ :=
    Mutation.emit_success emitted_eq
  obtain ⟨declarations, linesEq, namesEq, declarationsOk, agree⟩ :=
    mutationLoop_spec graph.helpers 0 _ names lines [] [] loop
      (mutation_helpers_accepted graph.helperScopes)
      (fun _ _ found => by simp [helperNames] at found)
  have entryKind : initializerKind? ([Binding.word "sc_input"].map Binding.kind) names.length
      graph.entry = some Local.word := by
    rw [namesEq, helperNames_length, Nat.zero_add]
    exact acceptsAt_kind graph.entryScope
  obtain ⟨statements, entryLines, _, valueName, entryNames, simulates⟩ :=
    (mutation_render_spec (admits := fun _ => True) graph.entry).1 names .word
      [.word "sc_input"] 8 0 entry entryKind entryEquation
      (single_binding_fresh input_not_temporary cellTemp_ne_input) (single_binding_distinct _)
  let file := mutationFile declarations statements result
  have inputOk : ∀ index found, nameAt [Binding.word "sc_input"] index = some found →
      ValidIdentifier found ∧ isReserved found = false :=
    single_binding_ok (keyword_valid (by decide)) (by decide)
  have functionNamesOk : ∀ name ∈ names, ValidIdentifier name ∧ isReserved name = false := by
    rw [namesEq]
    exact helperNames_ok
  have printed : emitted.source = file.print := by
    have functionLine :
        "    function " ++ Mutation.methodName ++ "(input: uint256) public returns (uint256) {" =
          "    function " ++ file.method.name ++ "(" ++
            Method.parameterText file.method.parameters ++ ") public returns (uint256) {" := by
      apply String.toList_inj.mp
      simp [file, mutationFile, inputFile, Method.parameterText, Mutation.methodName]
    have returnLine : "        return uint256(" ++ result ++ ");" =
        "        return " ++ file.method.result.print ++ ";" := by
      apply String.toList_inj.mp
      simp [file, mutationFile, inputFile, Expr.print]
    have bodyLines : Stmt.listLines 8 file.method.body =
        "        let sc_input: word = Typedef.rep(input);" :: Stmt.listLines 8 statements :=
      inputFile_body_lines statements result
    rw [source, SourceFile.print, SourceFile.lines, bodyLines, entryLines, linesEq, functionLine,
      returnLine]
    simp [file, mutationFile, aliasImportLines, Mutation.contractName]
  have valueOk := mutation_identifier_ok inputOk functionNamesOk (valueName result resultFound).uses
  have bodyNames : ∀ name ∈ Stmt.listIdentifiers file.method.body,
      ValidIdentifier name ∧ isReserved name = false := by
    intro name mem
    simp only [file, mutationFile, inputFile, Stmt.listIdentifiers, Stmt.identifiers,
      Expr.identifiers, List.cons_append, List.nil_append, List.mem_cons] at mem
    rcases mem with rfl | rfl | mem
    · exact ⟨keyword_valid (by decide), by decide⟩
    · exact ⟨keyword_valid (by decide), by decide⟩
    · exact mutation_identifier_ok inputOk functionNamesOk (entryNames name mem)
  have parsed : parseSource emitted.source = some file := by
    rw [printed]
    apply parseSource_print
    · refine ⟨fun declaration mem => (declarationsOk declaration mem).1, rfl, rfl, ?_,
        fun name mem => (bodyNames name mem).2, ?_⟩
      · intro parameter mem
        simp only [file, mutationFile, inputFile, List.mem_singleton] at mem
        subst mem
        decide
      · intro name mem
        simp only [file, mutationFile, inputFile, Expr.identifiers, List.mem_singleton] at mem
        subst mem
        exact valueOk.2
    · refine ⟨fun _ absent => absurd absent List.not_mem_nil,
        fun declaration mem => (declarationsOk declaration mem).2,
        keyword_valid (show validIdentifier "SynthesizedMutation" = true by decide),
        keyword_valid (show validIdentifier "run" = true by decide), ?_,
        fun name mem => (bodyNames name mem).1, ?_⟩
      · intro parameter mem
        simp only [file, mutationFile, inputFile, List.mem_singleton] at mem
        subst mem
        exact keyword_valid (by decide)
      · intro name mem
        simp only [file, mutationFile, inputFile, Expr.identifiers, List.mem_singleton] at mem
        subst mem
        exact valueOk.1
  refine ⟨file, printed, parsed, ?_⟩
  intro input
  have context : file.context = ⟨declareFunctions [] [] declarations, []⟩ := rfl
  obtain ⟨core, store', scope', outer', _, evaluates, represents, exec, _⟩ :=
    simulates file.context (.word input :: graph.helpers.foldl closureStep []) []
      [("sc_input", .word input.val)] [[("input", .uint256 input.val)]] trivial
      (single_binding_agree (by simp [Frames.lookup, Scope.get?]) _ _)
      (single_binding_cells _ _ _) (by simp) (by rw [context]; simpa using agree)
  rw [resultFound, Option.bind_some] at represents
  obtain ⟨word, rfl, lookup⟩ := represents
  have applied : Solcore.Core.Evaluates [] []
      (graph.instantiate input).toCore.body (.word word) store' := by
    simp only [CheckedDAG.instantiate, CheckedDAG.program,
      Solcore.Synthesis.Core.functionDAGProgram, Solcore.Core.Wire.Program.toCore]
    simp only [Solcore.Core.Wire.Expr.toCore]
    exact .apply (dag_evaluates graph.entry graph.helpers [] []) .word evaluates
  refine ⟨word, ?_, runStateful_of_evaluates_store applied⟩
  have parameters : Method.bindParameters ["input"] [input.val] =
      some [("input", .uint256 input.val)] := by
    simp [Method.bindParameters, word_lt_modulus]
  have execBody : Stmt.execList file.context [[], [("input", .uint256 input.val)]]
      (.letDecl "sc_input" .word (.typedefRep (.name "input")) :: statements) =
        some (scope' :: outer') := by
    simp only [Stmt.execList, input_declaration]
    exact exec
  simp only [file, mutationFile, inputFile] at execBody
  simp [file, mutationFile, inputFile, SourceFile.call, Method.run, parameters, execBody,
    Expr.eval, lookup]

/-- **Private-mutation emitter preservation, on the emitted text.** -/
theorem Mutation.emit_source_meaning {graph : CheckedDAG}
    {emitted : EmittedProgram} (emitted_eq : Mutation.emit graph = .ok emitted)
    (input : Solcore.Core.Word) :
    ∃ word : Solcore.Core.Word,
      sourceCall emitted.source "run" [input.val] = some word.val ∧
      CoreReturnsWithStore (graph.instantiate input).toCore word := by
  obtain ⟨file, _, parsed, meaning⟩ := Mutation.emit_preserves_meaning emitted_eq
  obtain ⟨word, called, core⟩ := meaning input
  exact ⟨word, by simp [sourceCall, parsed, called], core⟩

end Solcore.Synthesis.Source.ScalarMeaning
