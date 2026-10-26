import Solcore.Core.Correspondence
import Solcore.Synthesis.Core.WordFunction
import Solcore.Synthesis.Source.Emitter
import Solcore.Synthesis.Source.InputEmitter
import Solcore.Synthesis.Source.ScalarMeaning.RendererPreservation
import Solcore.Synthesis.Source.ScalarMeaning.Text

/-! Meaning preservation for the actual closed G0 wrapper (`emit`, method
`run()`) and the runtime-input wrapper (`Input.emit`, method `run(uint256)`).
The emitted source text parses to a source file whose independently defined
method result is the Word returned by the original Core program under the
Core machine (`runStateful`) used as the differential-testing oracle. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.ScalarMeaning

open Solcore.Synthesis.Core (CheckedWordProgram CheckedWordFunction)

/-- The file printed by the closed G0 wrapper around rendered statements. -/
def closedFile (body : List Stmt) (value : String) : SourceFile := {
  opcodeAliases := []
  functions := []
  contract := "SynthesizedG0"
  method := { name := "run", parameters := [], body, result := .uint256 (.name value) } }

/-- The file printed by the runtime-input wrapper. The ABI input is converted
to a `word` once, and that word is the outermost rendered local. -/
def inputFile (body : List Stmt) (value : String) : SourceFile := {
  opcodeAliases := []
  functions := []
  contract := "SynthesizedInput"
  method := {
    name := "run"
    parameters := ["input"]
    body := .letDecl "sc_input" .word (.typedefRep (.name "input")) :: body
    result := .uint256 (.name value) } }

theorem input_not_temporary (index : Nat) : "sc_input" ≠ temporary index := by
  intro same
  have chars := congrArg String.toList same
  simp [temporary] at chars

private theorem string_eq_of_toList {first second : String}
    (same : first.toList = second.toList) : first = second :=
  String.toList_inj.mp same

theorem inputFile_body_lines (statements : List Stmt) (value : String) :
    Stmt.listLines 8 (inputFile statements value).method.body =
      "        let sc_input: word = Typedef.rep(input);" :: Stmt.listLines 8 statements := by
  simp only [inputFile, Stmt.listLines, Stmt.lines, List.singleton_append, List.cons.injEq,
    and_true]
  apply String.toList_inj.mp
  simp [indentLine, Expr.print, LocalType.spelling]

theorem input_declaration (context : Context) (input : Nat) :
    Stmt.exec context [[], [("input", .uint256 input)]]
      (.letDecl "sc_input" .word (.typedefRep (.name "input"))) =
      some [[("sc_input", .word input)], [("input", .uint256 input)]] := by
  simp [Stmt.exec, Expr.eval, Frames.lookup, Scope.get?, LocalType.admits, Frames.declare]

/-- The final Core result is unique and reached with enough fuel. -/
theorem runStateful_of_evaluates {expression : Solcore.Core.Expr} {value : Solcore.Core.Value}
    (evaluates : Solcore.Core.Evaluates [] [] expression value []) :
    (∃ required, ∀ fuel, required ≤ fuel →
      Solcore.Core.runStateful fuel (Solcore.Core.State.initial expression) = .done value []) ∧
    (∀ fuel other store,
      Solcore.Core.runStateful fuel (Solcore.Core.State.initial expression) = .done other store →
      other = value ∧ store = []) := by
  refine ⟨Solcore.Core.evaluation_runStateful_complete_with_sufficient_fuel evaluates, ?_⟩
  intro fuel other store completed
  obtain ⟨same, sameStore⟩ := Solcore.Core.evaluation_deterministic
    (Solcore.Core.runStateful_evaluation_sound completed) evaluates
  exact ⟨same, sameStore⟩

theorem emit_success {program : CheckedWordProgram} {emitted : EmittedProgram}
    (emitted_eq : emit program = .ok emitted) :
    ∃ body : ScalarRenderer.Rendered,
      ScalarRenderer.render .word [] 8 0 program.program.body = .ok body ∧
      emitted.source = String.intercalate "\n" (["import * from std;",
        "import * from std.dispatch;", "", "contract " ++ contractName ++ " {",
        "    function " ++ methodName ++ "() public returns (uint256) {"] ++ body.lines ++
        ["        return uint256(" ++ body.value ++ ");", "    }", "}"]) ++ "\n" := by
  unfold emit at emitted_eq
  cases rendered : ScalarRenderer.render .word [] 8 0 program.program.body with
  | error error =>
      rw [rendered] at emitted_eq
      cases emitted_eq
  | ok body =>
      rw [rendered] at emitted_eq
      cases emitted_eq
      exact ⟨body, rfl, rfl⟩

theorem Input.emit_success {function : CheckedWordFunction} {emitted : EmittedProgram}
    (emitted_eq : Input.emit function = .ok emitted) :
    ∃ body : ScalarRenderer.Rendered,
      ScalarRenderer.render .word ["sc_input"] 8 0 function.body = .ok body ∧
      emitted.source = String.intercalate "\n" (["import * from std;",
        "import * from std.dispatch;", "", "contract " ++ Input.contractName ++ " {",
        "    function " ++ Input.methodName ++ "(input: uint256) public returns (uint256) {",
        "        let sc_input: word = Typedef.rep(input);"] ++ body.lines ++
        ["        return uint256(" ++ body.value ++ ");", "    }", "}"]) ++ "\n" := by
  unfold Input.emit at emitted_eq
  cases rendered : ScalarRenderer.render .word ["sc_input"] 8 0 function.body with
  | error error =>
      rw [rendered] at emitted_eq
      cases emitted_eq
  | ok body =>
      rw [rendered] at emitted_eq
      cases emitted_eq
      exact ⟨body, rfl, rfl⟩

/-- Core returns `word` with enough fuel, and every completed run returns it
with an empty store. -/
def CoreReturns (program : Solcore.Core.Program) (word : Solcore.Core.Word) : Prop :=
  (∃ required, ∀ fuel, required ≤ fuel → program.runStateful fuel = .done (.word word) []) ∧
    (∀ fuel value store, program.runStateful fuel = .done value store →
      value = .word word ∧ store = [])

theorem temporary_valid (index : Nat) : ValidIdentifier (temporary index) := by
  refine ⟨'s', ['c', '_', 'v'] ++ Nat.toDigits 10 index, by simp [temporary], by decide, ?_⟩
  intro char mem
  rcases List.mem_append.mp mem with prefix_ | digit
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at prefix_
    rcases prefix_ with rfl | rfl | rfl <;> decide
  · exact (digit_classes (toDigits_mem digit)).2.2

theorem temporary_not_reserved (index : Nat) : isReserved (temporary index) = false := by
  have heads : ∀ word ∈ reservedWords, word.toList.head? ≠ some 's' := by decide
  have absent : temporary index ∉ reservedWords := by
    intro mem
    exact heads _ mem (by simp [temporary])
  cases reserved : isReserved (temporary index)
  · rfl
  · exact absurd (List.elem_iff.mp reserved) absent

/-- Every name used by rendered statements is a local or a temporary. -/
theorem rendered_name_ok {locals : List String} {name : String} {first last : Nat}
    (localsOk : ∀ local_ ∈ locals, ValidIdentifier local_ ∧ isReserved local_ = false)
    (classified : name ∈ locals ∨ AllocatedIn first last name) :
    ValidIdentifier name ∧ isReserved name = false := by
  rcases classified with mem | ⟨index, rfl, _, _⟩
  · exact localsOk name mem
  · exact ⟨temporary_valid index, temporary_not_reserved index⟩

/-- Every identifier used by rendered statements is a local, a helper name or
a temporary. -/
theorem rendered_identifier_ok {locals functions called : List String} {name : String}
    {first last : Nat}
    (localsOk : ∀ local_ ∈ locals, ValidIdentifier local_ ∧ isReserved local_ = false)
    (functionsOk : ∀ function ∈ functions, ValidIdentifier function ∧
      isReserved function = false)
    (calledOk : ∀ callee ∈ called, ValidIdentifier callee ∧ isReserved callee = false)
    (classified : name ∈ locals ∨ name ∈ functions ∨ AllocatedIn first last name ∨
      name ∈ called) :
    ValidIdentifier name ∧ isReserved name = false := by
  rcases classified with mem | mem | ⟨index, rfl, _, _⟩ | mem
  · exact localsOk name mem
  · exact functionsOk name mem
  · exact ⟨temporary_valid index, temporary_not_reserved index⟩
  · exact calledOk name mem

/-- **Closed G0 emitter preservation.** If the actual emitter succeeds, its
source text is the printing of a source file and parses back to it. Calling
`run()` under the independent source semantics returns exactly the Word that
the original Core program returns. -/
theorem emit_preserves_meaning {program : CheckedWordProgram} {emitted : EmittedProgram}
    (emitted_eq : emit program = .ok emitted) :
    ∃ (file : SourceFile) (word : Solcore.Core.Word),
      emitted.source = file.print ∧ parseSource emitted.source = some file ∧
      file.call "run" [] = some word.val ∧ CoreReturns program.program.toCore word := by
  obtain ⟨body, rendered, source⟩ := emit_success emitted_eq
  obtain ⟨statements, lines, _, valueName, names, simulates⟩ :=
    render_spec (fun _ => True) [] program.program.body [] 0 0 .word [] 8 0 body
      (acceptsAt_functionAcceptsAt _ 0 program.fragment) rendered
      (fun _ absent => absurd absent List.not_mem_nil)
  obtain ⟨core, value, scope', outer', _, evaluates, represents, exec, lookup, _⟩ :=
    simulates (closedFile statements body.value).context [] [] [] [[]] trivial
      (fun index name found => by simp at found) (by simp) (fun _ _ found => by simp at found)
  obtain ⟨word, rfl, rfl⟩ := represents
  have localsOk : ∀ local_ ∈ ([] : List String), ValidIdentifier local_ ∧
      isReserved local_ = false := fun _ absent => absurd absent List.not_mem_nil
  have bodyOk := fun name mem =>
    rendered_identifier_ok localsOk localsOk localsOk (names name mem)
  have printed : emitted.source = (closedFile statements body.value).print := by
    rw [source, SourceFile.print, SourceFile.lines, lines]
    apply string_eq_of_toList
    simp [closedFile, aliasImportLines, Method.parameterText, methodName, contractName,
      Expr.print]
  have valueOk := rendered_name_ok localsOk valueName
  have parsed : parseSource emitted.source = some (closedFile statements body.value) := by
    rw [printed]
    apply parseSource_print
    · refine ⟨fun _ absent => absurd absent List.not_mem_nil, rfl, rfl,
        fun _ absent => absurd absent List.not_mem_nil, fun name mem => (bodyOk name mem).2, ?_⟩
      intro name mem
      simp only [closedFile, Expr.identifiers, List.mem_singleton] at mem
      subst mem
      exact valueOk.2
    · refine ⟨fun _ absent => absurd absent List.not_mem_nil,
        fun _ absent => absurd absent List.not_mem_nil,
        keyword_valid (show validIdentifier "SynthesizedG0" = true by decide),
        keyword_valid (show validIdentifier "run" = true by decide),
        fun _ absent => absurd absent List.not_mem_nil, fun name mem => (bodyOk name mem).1, ?_⟩
      intro name mem
      simp only [closedFile, Expr.identifiers, List.mem_singleton] at mem
      subst mem
      exact valueOk.1
  refine ⟨closedFile statements body.value, word, printed, parsed, ?_,
    runStateful_of_evaluates evaluates⟩
  simp only [closedFile] at exec
  simp [closedFile, SourceFile.call, Method.run, Method.bindParameters, exec, Expr.eval, lookup]

/-- **Closed G0 emitter preservation, on the emitted text.** -/
theorem emit_source_meaning {program : CheckedWordProgram} {emitted : EmittedProgram}
    (emitted_eq : emit program = .ok emitted) :
    ∃ word : Solcore.Core.Word,
      sourceCall emitted.source "run" [] = some word.val ∧
      CoreReturns program.program.toCore word := by
  obtain ⟨file, word, _, parsed, called, core⟩ := emit_preserves_meaning emitted_eq
  exact ⟨word, by simp [sourceCall, parsed, called], core⟩

/-- **Runtime-input emitter preservation.** If the actual emitter succeeds,
its source text is the printing of one source file and parses back to it.
For every runtime input, calling `run(uint256)` under the independent source
semantics returns exactly the Word that the original Core function applied to
that input returns. -/
theorem Input.emit_preserves_meaning {function : CheckedWordFunction}
    {emitted : EmittedProgram} (emitted_eq : Input.emit function = .ok emitted) :
    ∃ file : SourceFile, emitted.source = file.print ∧ parseSource emitted.source = some file ∧
      ∀ input : Solcore.Core.Word, ∃ word : Solcore.Core.Word,
        file.call "run" [input.val] = some word.val ∧
        CoreReturns (function.instantiate input).toCore word := by
  obtain ⟨body, rendered, source⟩ := Input.emit_success emitted_eq
  have fresh : ∀ name ∈ ["sc_input"], OlderThan 0 name := by
    intro name mem index same
    simp only [List.mem_singleton] at mem
    subst mem
    exact absurd same (input_not_temporary index)
  obtain ⟨statements, lines, _, valueName, names, simulates⟩ :=
    render_spec (fun _ => True) [] function.body [] 1 0 .word ["sc_input"] 8 0 body
      (acceptsAt_functionAcceptsAt _ 0 function.fragment) rendered fresh
  have localsOk : ∀ local_ ∈ ["sc_input"], ValidIdentifier local_ ∧
      isReserved local_ = false := by
    intro local_ mem
    simp only [List.mem_singleton] at mem
    subst mem
    exact ⟨keyword_valid (by decide), by decide⟩
  have printed : emitted.source = (inputFile statements body.value).print := by
    have functionLine :
        "    function " ++ Input.methodName ++ "(input: uint256) public returns (uint256) {" =
          "    function " ++ (inputFile statements body.value).method.name ++ "(" ++
            Method.parameterText (inputFile statements body.value).method.parameters ++
            ") public returns (uint256) {" := by
      apply string_eq_of_toList
      simp [inputFile, Method.parameterText, Input.methodName]
    have returnLine : "        return uint256(" ++ body.value ++ ");" =
        "        return " ++ (inputFile statements body.value).method.result.print ++ ";" := by
      apply string_eq_of_toList
      simp [inputFile, Expr.print]
    rw [source, SourceFile.print, SourceFile.lines, lines, inputFile_body_lines, functionLine,
      returnLine]
    simp [inputFile, aliasImportLines, Input.contractName]
  have valueOk := rendered_name_ok localsOk valueName
  have bodyNames : ∀ name ∈ Stmt.listIdentifiers (inputFile statements body.value).method.body,
      ValidIdentifier name ∧ isReserved name = false := by
    intro name mem
    simp only [inputFile, Stmt.listIdentifiers, Stmt.identifiers, Expr.identifiers,
      List.cons_append, List.nil_append, List.mem_cons] at mem
    rcases mem with rfl | rfl | mem
    · exact ⟨keyword_valid (by decide), by decide⟩
    · exact ⟨keyword_valid (by decide), by decide⟩
    · exact rendered_identifier_ok localsOk (fun _ absent => absurd absent List.not_mem_nil)
        (fun _ absent => absurd absent List.not_mem_nil) (names name mem)
  have parsed : parseSource emitted.source = some (inputFile statements body.value) := by
    rw [printed]
    apply parseSource_print
    · refine ⟨fun _ absent => absurd absent List.not_mem_nil, rfl, rfl, ?_,
        fun name mem => (bodyNames name mem).2, ?_⟩
      · intro parameter mem
        simp only [inputFile, List.mem_singleton] at mem
        subst mem
        decide
      · intro name mem
        simp only [inputFile, Expr.identifiers, List.mem_singleton] at mem
        subst mem
        exact valueOk.2
    · refine ⟨fun _ absent => absurd absent List.not_mem_nil,
        fun _ absent => absurd absent List.not_mem_nil,
        keyword_valid (show validIdentifier "SynthesizedInput" = true by decide),
        keyword_valid (show validIdentifier "run" = true by decide), ?_,
        fun name mem => (bodyNames name mem).1, ?_⟩
      · intro parameter mem
        simp only [inputFile, List.mem_singleton] at mem
        subst mem
        exact keyword_valid (by decide)
      · intro name mem
        simp only [inputFile, Expr.identifiers, List.mem_singleton] at mem
        subst mem
        exact valueOk.1
  refine ⟨inputFile statements body.value, printed, parsed, ?_⟩
  intro input
  have agree : LocalsAgree [[("sc_input", .word input.val)], [("input", .uint256 input.val)]]
      ["sc_input"] [.word input] := by
    intro index name found
    cases index with
    | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at found
        subst found
        exact ⟨input, rfl, by simp [Frames.lookup, Scope.get?]⟩
    | succ index => simp at found
  obtain ⟨core, value, scope', outer', _, evaluates, represents, exec, lookup, _⟩ :=
    simulates (inputFile statements body.value).context [.word input] []
      [("sc_input", .word input.val)] [[("input", .uint256 input.val)]] trivial agree (by simp)
      (fun _ _ found => by simp at found)
  obtain ⟨word, rfl, rfl⟩ := represents
  have applied : Solcore.Core.Evaluates [] []
      (function.instantiate input).toCore.body (.word word) [] := by
    simp only [CheckedWordFunction.instantiate, CheckedWordFunction.program,
      Solcore.Synthesis.Core.wordFunctionProgram, Solcore.Core.Wire.Program.toCore,
      Solcore.Core.Wire.Expr.toCore]
    exact .apply .lambda .word evaluates
  refine ⟨word, ?_, runStateful_of_evaluates applied⟩
  have parameters : Method.bindParameters ["input"] [input.val] =
      some [("input", .uint256 input.val)] := by
    simp [Method.bindParameters, word_lt_modulus]
  have execBody : Stmt.execList (inputFile statements body.value).context
      [[], [("input", .uint256 input.val)]]
      (.letDecl "sc_input" .word (.typedefRep (.name "input")) :: statements) =
        some (scope' :: outer') := by
    simp only [Stmt.execList, input_declaration]
    exact exec
  simp only [inputFile] at execBody
  simp [SourceFile.call, Method.run, parameters, execBody, inputFile, Expr.eval, lookup]

/-- **Runtime-input emitter preservation, on the emitted text.** -/
theorem Input.emit_source_meaning {function : CheckedWordFunction}
    {emitted : EmittedProgram} (emitted_eq : Input.emit function = .ok emitted)
    (input : Solcore.Core.Word) :
    ∃ word : Solcore.Core.Word,
      sourceCall emitted.source "run" [input.val] = some word.val ∧
      CoreReturns (function.instantiate input).toCore word := by
  obtain ⟨file, _, parsed, meaning⟩ := Input.emit_preserves_meaning emitted_eq
  obtain ⟨word, called, core⟩ := meaning input
  exact ⟨word, by simp [sourceCall, parsed, called], core⟩

end Solcore.Synthesis.Source.ScalarMeaning
