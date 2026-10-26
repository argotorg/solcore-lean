import Solcore.Synthesis.Source.AggregateCallGraphEmitter
import Solcore.Synthesis.Source.ScalarMeaning.AggregateCallGraphPreservation
import Solcore.Synthesis.Source.ScalarMeaning.AggregateEmitter

/-! Meaning preservation for the actual aggregate call-graph emitter
(`AggregateCallGraph.emit`, profile `runtime-aggregate-call-graphs`). Helpers
become free functions as for the named-helper emitter, and the file always
imports the fourteen raw `std.opcodes` aliases, as for the call-graph emitter.
The checked profile admits cells, which the renderer rejects; the result is
stated, as for the aggregate emitter, for the Word that Core returns with its
final store. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.ScalarMeaning

open Solcore.Synthesis.Core.Aggregates (CheckedDAG Local initializerKind? infer?)

/-! ### The emitter's helper loop -/

/-- The helper loop of `AggregateCallGraph.emit`, by structural recursion. -/
def aggregateCallGraphLoop : List CoreExpr → Nat → List String → List String →
    Except EmitError (List String × List String)
  | [], _, names, lines => .ok (names, lines)
  | body :: rest, index, names, lines =>
      (AggregateCallGraphRenderer.render names .word [.word "sc_arg"] 4 0 body).bind
        fun rendered =>
          aggregateCallGraphLoop rest (index + 1) (Function.helperName index :: names)
            (lines ++
              ["function " ++ Function.helperName index ++ "(sc_arg: word) returns (word) {"] ++
              rendered.lines ++ ["    return " ++ rendered.value ++ ";", "}", ""])

theorem forIn_aggregateCallGraphLoop
    {step : CoreExpr × Nat → List String × List String →
      Except EmitError (ForInStep (List String × List String))}
    (stepEq : ∀ body index names lines, step (body, index) (names, lines) =
      (AggregateCallGraphRenderer.render names .word [.word "sc_arg"] 4 0 body).bind
        fun rendered =>
          .ok (.yield (Function.helperName index :: names,
            lines ++
              ["function " ++ Function.helperName index ++ "(sc_arg: word) returns (word) {"] ++
              rendered.lines ++ ["    return " ++ rendered.value ++ ";", "}", ""]))) :
    ∀ (bodies : List CoreExpr) (start : Nat) (names lines : List String),
      forIn (bodies.zipIdx start) (names, lines) step =
        aggregateCallGraphLoop bodies start names lines
  | [], _, _, _ => rfl
  | body :: rest, start, names, lines => by
      rw [List.zipIdx_cons, List.forIn_cons, stepEq, aggregateCallGraphLoop]
      cases AggregateCallGraphRenderer.render names .word [.word "sc_arg"] 4 0 body with
      | error error => rfl
      | ok rendered => exact forIn_aggregateCallGraphLoop stepEq rest (start + 1) _ _

theorem AggregateCallGraph.emit_success {graph : CheckedDAG} {emitted : EmittedProgram}
    (emitted_eq : AggregateCallGraph.emit graph = .ok emitted) :
    ∃ (names lines : List String) (entry : ScalarRenderer.Rendered),
      aggregateCallGraphLoop graph.helpers 0 []
        ["import * from std;", "import * from std.dispatch;", Primitive.opcodeImport, ""] =
        .ok (names, lines) ∧
      AggregateCallGraphRenderer.render names .word [.word "sc_input"] 8 0 graph.entry =
        .ok entry ∧
      emitted.source = String.intercalate "\n" (lines ++
        ["contract " ++ AggregateCallGraph.contractName ++ " {",
          "    function " ++ AggregateCallGraph.methodName ++
            "(input: uint256) public returns (uint256) {",
          "        let sc_input: word = Typedef.rep(input);"] ++ entry.lines ++
        ["        return uint256(" ++ entry.value ++ ");", "    }", "}"]) ++ "\n" := by
  unfold AggregateCallGraph.emit at emitted_eq
  dsimp only at emitted_eq
  rw [forIn_aggregateCallGraphLoop (fun _ _ _ _ => rfl)] at emitted_eq
  cases loop : aggregateCallGraphLoop graph.helpers 0 []
    ["import * from std;", "import * from std.dispatch;", Primitive.opcodeImport, ""] with
  | error error =>
      rw [loop] at emitted_eq
      cases emitted_eq
  | ok loopResult =>
      obtain ⟨names, lines⟩ := loopResult
      rw [loop] at emitted_eq
      cases entry : AggregateCallGraphRenderer.render names .word [.word "sc_input"] 8 0
        graph.entry with
      | error error =>
          simp only [bind, Except.bind, entry] at emitted_eq
          cases emitted_eq
      | ok rendered =>
          simp only [bind, Except.bind, entry, pure, Except.pure, Except.ok.injEq] at emitted_eq
          subst emitted_eq
          exact ⟨names, lines, rendered, rfl, entry, rfl⟩

/-- The helper loop prints free functions whose meanings agree with the Core
closures of the binding chain, and whose evaluation keeps the caller's store.
Declaring a helper keeps the aliases and `tobool` reachable. -/
theorem aggregateCallGraphLoop_spec :
    ∀ (bodies : List CoreExpr) (start : Nat) (lines names' lines' : List String)
      (functions : List (String × (List Value → Option Value))) (closures : List CoreValue),
    aggregateCallGraphLoop bodies start (helperNames start) lines = .ok (names', lines') →
    (∀ (index : Nat) (body : CoreExpr), bodies[index]? = some body →
      Solcore.Synthesis.Core.Aggregates.acceptsAt [.word] (start + index) .word body = true) →
    PrimitiveContext ⟨functions, primitiveAliases⟩ →
    MFunctionsAgree ⟨functions, primitiveAliases⟩ (helperNames start) closures →
    ∃ declarations : List FunctionDecl,
      lines' = lines ++ declarations.flatMap FunctionDecl.lines ∧
      names' = helperNames (start + bodies.length) ∧
      (∀ declaration ∈ declarations, declaration.NamesOk ∧
        ∀ name ∈ declaration.identifiers, ValidIdentifier name) ∧
      PrimitiveContext
        ⟨declareFunctions primitiveAliases functions declarations, primitiveAliases⟩ ∧
      MFunctionsAgree
        ⟨declareFunctions primitiveAliases functions declarations, primitiveAliases⟩
        names' (bodies.foldl closureStep closures)
  | [], start, lines, names', lines', functions, closures, loop, _, primitive, agree => by
      simp only [aggregateCallGraphLoop, Except.ok.injEq, Prod.mk.injEq] at loop
      obtain ⟨rfl, rfl⟩ := loop
      exact ⟨[], by simp, by simp, by simp, by simpa [declareFunctions] using primitive,
        by simpa [declareFunctions] using agree⟩
  | body :: rest, start, lines, names', lines', functions, closures, loop, accepted, primitive,
      agree => by
      simp only [aggregateCallGraphLoop] at loop
      obtain ⟨rendered, renderedEquation, loop⟩ := except_bind_eq_ok loop
      have bodyKind : initializerKind?
          ([AggregateCallGraphRenderer.Binding.word "sc_arg"].map
            AggregateCallGraphRenderer.Binding.kind)
          (helperNames start).length body = some Local.word := by
        rw [helperNames_length]
        exact aggregate_acceptsAt_kind (accepted 0 body rfl)
      obtain ⟨_, statements, lines₁, _, valueName, names, simulates⟩ :=
        aggregateCallGraph_render_spec body (helperNames start) .word [.word "sc_arg"] 4 0
          rendered bodyKind renderedEquation
          (single_abinding_fresh argument_not_temporary cellTemp_ne_argument
            payloadTemp_ne_argument)
          (single_abinding_distinct _)
      let declaration := helperDecl start statements rendered.value
      have behaves : ∀ (argument : Solcore.Core.Word) (store : Solcore.Core.Store),
          ∃ (value : Solcore.Core.Word) (store' : Solcore.Core.Store),
            Solcore.Core.Evaluates (.word argument :: closures) store body.toCore
              (.word value) store' ∧
            store.length ≤ store'.length ∧
            (∀ location, location < store.length →
              store'.read? location = store.read? location) ∧
            declaration.denote ⟨functions, primitiveAliases⟩ [.word argument.val] =
              some (.word value.val) := by
        intro argument store
        obtain ⟨core, store', scope', outer', _, evaluates, represents, exec, _, frame, _⟩ :=
          simulates ⟨functions, primitiveAliases⟩ (.word argument :: closures) store []
            [[("sc_arg", .word argument.val)]] primitive
            (single_abinding_agree (by simp [Frames.lookup, Scope.get?]) closures store)
            (single_abinding_cells _ _ _) (by simp) (by simpa using agree)
        simp only [ARendered.ofScalar, Option.bind_some] at represents
        obtain ⟨_, lookup, value, rfl, rfl⟩ := represents
        refine ⟨value, store', evaluates, frame.1, fun location inBounds =>
          frame.2 location inBounds fun index isCell => ?_, ?_⟩
        · obtain ⟨⟨_, found⟩, _⟩ := isCell
          cases index with
          | zero => simp [GBinding.toAggregate] at found
          | succ index => simp at found
        · simp [declaration, helperDecl, FunctionDecl.denote, FunctionDecl.bindParameters,
            LocalType.admits, exec, Expr.eval, lookup]
      have extended := agree.extend (helperName_not_mem start) behaves
        (parameterType := Solcore.Core.Wire.Ty.toCore .word)
        (resultType := Solcore.Core.Wire.Ty.toCore .word)
      have extendedPrimitive := primitive.extend start
        (declaration.denote ⟨functions, primitiveAliases⟩)
      have restAccepted : ∀ (index : Nat) (body : CoreExpr), rest[index]? = some body →
          Solcore.Synthesis.Core.Aggregates.acceptsAt [.word] (start + 1 + index) .word body =
            true := by
        intro index body found
        have accepted' := accepted (index + 1) body (by simpa using found)
        rwa [show start + (index + 1) = start + 1 + index by omega] at accepted'
      obtain ⟨declarations, rest₁, rest₂, rest₃, rest₄, rest₅⟩ :=
        aggregateCallGraphLoop_spec rest (start + 1) _ names' lines' _ _ loop restAccepted
          extendedPrimitive extended
      have block :
          ["function " ++ Function.helperName start ++ "(sc_arg: word) returns (word) {"] ++
          rendered.lines ++ ["    return " ++ rendered.value ++ ";", "}", ""] =
          declaration.lines := by
        simp only [declaration, helperDecl, FunctionDecl.lines]
        rw [show rendered.lines = Stmt.listLines 4 statements from lines₁]
        simp only [List.cons_append, List.nil_append, List.cons.injEq]
        refine ⟨?_, ?_⟩
        · apply String.toList_inj.mp
          simp [FunctionDecl.parameterText, LocalType.spelling]
        · simp [Expr.print]
      have argumentOk : ∀ index found,
          anameAt [AggregateRenderer.Binding.word "sc_arg"] index = some found →
            ValidIdentifier found ∧ isReserved found = false :=
        single_abinding_ok (keyword_valid (by decide)) (by decide)
      refine ⟨declaration :: declarations, ?_, ?_, ?_, rest₄, rest₅⟩
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
            aggregate_identifier_ok argumentOk helperNames_ok (names name mem)
          have valueOk := aggregate_identifier_ok (functions := helperNames start) argumentOk
            helperNames_ok (valueName rendered.value rfl).uses
          refine ⟨⟨helperName_not_reserved start, ?_, fun name mem => (bodyOk name mem).2,
            ?_⟩, ?_⟩
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

/-- The source file printed by the aggregate call-graph emitter. -/
def aggregateCallGraphFile (declarations : List FunctionDecl) (body : List Stmt)
    (value : String) : SourceFile := {
  opcodeAliases := primitiveAliases
  functions := declarations
  contract := "SynthesizedAggregateCallGraphs"
  method := (inputFile body value).method }

/-- **Aggregate call-graph emitter preservation.** If the actual emitter
succeeds, its source text is the printing of a file with one free function per
helper and parses back to it. For every runtime input, calling `run(uint256)`
under the independent source semantics returns exactly the Word that the
original Core binding chain, applied to that input, returns, through Word
pairs and sums, their matches and projections, calls to earlier helpers and raw
opcode aliases. -/
theorem AggregateCallGraph.emit_preserves_meaning {graph : CheckedDAG}
    {emitted : EmittedProgram} (emitted_eq : AggregateCallGraph.emit graph = .ok emitted) :
    ∃ file : SourceFile, emitted.source = file.print ∧
      parseSource emitted.source = some file ∧
      ∀ input : Solcore.Core.Word, ∃ word : Solcore.Core.Word,
        file.call "run" [input.val] = some word.val ∧
        CoreReturnsWithStore (graph.instantiate input).toCore word := by
  obtain ⟨names, lines, entry, loop, entryEquation, source⟩ :=
    AggregateCallGraph.emit_success emitted_eq
  obtain ⟨declarations, linesEq, namesEq, declarationsOk, primitive, agree⟩ :=
    aggregateCallGraphLoop_spec graph.helpers 0 _ names lines [] [] loop
      (aggregate_helpers_accepted graph.helperScopes) primitiveContext_aliases
      (fun _ _ found => by simp [helperNames] at found)
  have entryKind : initializerKind?
      ([AggregateCallGraphRenderer.Binding.word "sc_input"].map
        AggregateCallGraphRenderer.Binding.kind) names.length
      graph.entry = some Local.word := by
    rw [namesEq, helperNames_length, Nat.zero_add]
    exact aggregate_acceptsAt_kind graph.entryScope
  obtain ⟨_, statements, entryLines, _, valueName, entryNames, simulates⟩ :=
    aggregateCallGraph_render_spec graph.entry names .word [.word "sc_input"] 8 0 entry
      entryKind entryEquation
      (single_abinding_fresh input_not_temporary cellTemp_ne_input payloadTemp_ne_input)
      (single_abinding_distinct _)
  let file := aggregateCallGraphFile declarations statements entry.value
  have inputOk : ∀ index found,
      anameAt [AggregateRenderer.Binding.word "sc_input"] index = some found →
        ValidIdentifier found ∧ isReserved found = false :=
    single_abinding_ok (keyword_valid (by decide)) (by decide)
  have functionNamesOk : ∀ name ∈ names, ValidIdentifier name ∧ isReserved name = false := by
    rw [namesEq]
    exact helperNames_ok
  have printed : emitted.source = file.print := by
    have functionLine :
        "    function " ++ AggregateCallGraph.methodName ++
            "(input: uint256) public returns (uint256) {" =
          "    function " ++ file.method.name ++ "(" ++
            Method.parameterText file.method.parameters ++ ") public returns (uint256) {" := by
      apply String.toList_inj.mp
      simp [file, aggregateCallGraphFile, inputFile, Method.parameterText,
        AggregateCallGraph.methodName]
    have returnLine : "        return uint256(" ++ entry.value ++ ");" =
        "        return " ++ file.method.result.print ++ ";" := by
      apply String.toList_inj.mp
      simp [file, aggregateCallGraphFile, inputFile, Expr.print]
    have bodyLines : Stmt.listLines 8 file.method.body =
        "        let sc_input: word = Typedef.rep(input);" :: Stmt.listLines 8 statements :=
      inputFile_body_lines statements entry.value
    rw [source, SourceFile.print, SourceFile.lines, bodyLines,
      show entry.lines = Stmt.listLines 8 statements from entryLines, linesEq, functionLine,
      returnLine]
    simp [file, aggregateCallGraphFile, primitiveImportLines, AggregateCallGraph.contractName,
      opcodeImport_eq]
  have valueOk := aggregate_identifier_ok inputOk functionNamesOk
    (valueName entry.value rfl).uses
  have bodyNames : ∀ name ∈ Stmt.listIdentifiers file.method.body,
      ValidIdentifier name ∧ isReserved name = false := by
    intro name mem
    simp only [file, aggregateCallGraphFile, inputFile, Stmt.listIdentifiers, Stmt.identifiers,
      Expr.identifiers, List.cons_append, List.nil_append, List.mem_cons] at mem
    rcases mem with rfl | rfl | mem
    · exact ⟨keyword_valid (by decide), by decide⟩
    · exact ⟨keyword_valid (by decide), by decide⟩
    · exact aggregate_identifier_ok inputOk functionNamesOk (entryNames name mem)
  have parsed : parseSource emitted.source = some file := by
    rw [printed]
    apply parseSource_print
    · refine ⟨fun declaration mem => (declarationsOk declaration mem).1, rfl, rfl, ?_,
        fun name mem => (bodyNames name mem).2, ?_⟩
      · intro parameter mem
        simp only [file, aggregateCallGraphFile, inputFile, List.mem_singleton] at mem
        subst mem
        decide
      · intro name mem
        simp only [file, aggregateCallGraphFile, inputFile, Expr.identifiers,
          List.mem_singleton] at mem
        subst mem
        exact valueOk.2
    · refine ⟨primitiveAliases_valid, fun declaration mem => (declarationsOk declaration mem).2,
        keyword_valid (show validIdentifier "SynthesizedAggregateCallGraphs" = true by decide),
        keyword_valid (show validIdentifier "run" = true by decide), ?_,
        fun name mem => (bodyNames name mem).1, ?_⟩
      · intro parameter mem
        simp only [file, aggregateCallGraphFile, inputFile, List.mem_singleton] at mem
        subst mem
        exact keyword_valid (by decide)
      · intro name mem
        simp only [file, aggregateCallGraphFile, inputFile, Expr.identifiers,
          List.mem_singleton] at mem
        subst mem
        exact valueOk.1
  refine ⟨file, printed, parsed, ?_⟩
  intro input
  have context : file.context =
      ⟨declareFunctions primitiveAliases [] declarations, primitiveAliases⟩ := rfl
  obtain ⟨core, store', scope', outer', _, evaluates, represents, exec, _⟩ :=
    simulates file.context (.word input :: graph.helpers.foldl closureStep []) []
      [("sc_input", .word input.val)] [[("input", .uint256 input.val)]]
      (by rw [context]; exact primitive)
      (single_abinding_agree (by simp [Frames.lookup, Scope.get?]) _ _)
      (single_abinding_cells _ _ _) (by simp) (by rw [context]; simpa using agree)
  simp only [ARendered.ofScalar, Option.bind_some] at represents
  obtain ⟨_, lookup, word, rfl, rfl⟩ := represents
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
  simp only [file, aggregateCallGraphFile, inputFile] at execBody
  simp [file, aggregateCallGraphFile, inputFile, SourceFile.call, Method.run, parameters,
    execBody, Expr.eval, lookup]

/-- **Aggregate call-graph emitter preservation, on the emitted text.** -/
theorem AggregateCallGraph.emit_source_meaning {graph : CheckedDAG}
    {emitted : EmittedProgram} (emitted_eq : AggregateCallGraph.emit graph = .ok emitted)
    (input : Solcore.Core.Word) :
    ∃ word : Solcore.Core.Word,
      sourceCall emitted.source "run" [input.val] = some word.val ∧
      CoreReturnsWithStore (graph.instantiate input).toCore word := by
  obtain ⟨file, _, parsed, meaning⟩ := AggregateCallGraph.emit_preserves_meaning emitted_eq
  obtain ⟨word, called, core⟩ := meaning input
  exact ⟨word, by simp [sourceCall, parsed, called], core⟩

end Solcore.Synthesis.Source.ScalarMeaning
