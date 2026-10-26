import Solcore.Core.Correspondence
import Solcore.Synthesis.Core.WordFunction
import Solcore.Synthesis.Source.Emitter
import Solcore.Synthesis.Source.InputEmitter
import Solcore.Synthesis.Source.ScalarMeaning.RendererPreservation

/-! Meaning preservation for the actual closed G0 wrapper (`emit`, method
`run()`) and the runtime-input wrapper (`Input.emit`, method `run(uint256)`).
The emitted source text is the printing of a source file whose independently
defined method result is the Word returned by the original Core program under
the Core machine (`runStateful`) used as the differential-testing oracle. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.ScalarMeaning

open Solcore.Synthesis.Core (CheckedWordProgram CheckedWordFunction)

/-- The file printed by the closed G0 wrapper around rendered statements. -/
def closedFile (body : List Stmt) (value : String) : SourceFile := {
  contract := "SynthesizedG0"
  method := { name := "run", parameters := [], body, result := .uint256 (.name value) } }

/-- The file printed by the runtime-input wrapper. The ABI input is converted
to a `word` once, and that word is the outermost rendered local. -/
def inputFile (body : List Stmt) (value : String) : SourceFile := {
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

theorem input_declaration (input : Nat) :
    Stmt.exec [[], [("input", .uint256 input)]]
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

/-- **Closed G0 emitter preservation.** If the actual emitter succeeds, its
source text is the printing of a source file. Calling `run()` under the
independent source semantics returns exactly the Word that the original Core
program returns; Core reaches that Word with sufficient fuel, and every
completed Core run returns it. -/
theorem emit_preserves_meaning {program : CheckedWordProgram} {emitted : EmittedProgram}
    (emitted_eq : emit program = .ok emitted) :
    ∃ (file : SourceFile) (word : Solcore.Core.Word),
      emitted.source = file.print ∧
      file.call "run" [] = some word.val ∧
      (∃ required, ∀ fuel, required ≤ fuel →
        program.program.toCore.runStateful fuel = .done (.word word) []) ∧
      (∀ fuel value store, program.program.toCore.runStateful fuel = .done value store →
        value = .word word ∧ store = []) := by
  obtain ⟨body, rendered, source⟩ := emit_success emitted_eq
  obtain ⟨statements, lines, _, _, _, simulates⟩ :=
    render_spec program.program.body 0 .word [] 8 0 body program.fragment rendered
      (fun _ absent => absurd absent List.not_mem_nil)
  obtain ⟨core, value, scope', outer', _, evaluates, represents, exec, lookup, _⟩ :=
    simulates [] [] [] [[]] (fun index name found => by simp at found)
  obtain ⟨word, rfl, rfl⟩ := represents
  refine ⟨closedFile statements body.value, word, ?_, ?_,
    (runStateful_of_evaluates evaluates).1, (runStateful_of_evaluates evaluates).2⟩
  · rw [source, SourceFile.print, SourceFile.lines, lines]
    apply string_eq_of_toList
    simp [closedFile, Method.parameterText, methodName, contractName, Expr.print]
  · simp [closedFile, SourceFile.call, Method.run, Method.bindParameters, exec, Expr.eval,
      lookup]

/-- **Runtime-input emitter preservation.** If the actual emitter succeeds,
its source text is the printing of one source file. For every runtime input,
calling `run(uint256)` under the independent source semantics returns exactly
the Word that the original Core function applied to that input returns. -/
theorem Input.emit_preserves_meaning {function : CheckedWordFunction}
    {emitted : EmittedProgram} (emitted_eq : Input.emit function = .ok emitted) :
    ∃ file : SourceFile, emitted.source = file.print ∧
      ∀ input : Solcore.Core.Word, ∃ word : Solcore.Core.Word,
        file.call "run" [input.val] = some word.val ∧
        (∃ required, ∀ fuel, required ≤ fuel →
          (function.instantiate input).toCore.runStateful fuel = .done (.word word) []) ∧
        (∀ fuel value store,
          (function.instantiate input).toCore.runStateful fuel = .done value store →
          value = .word word ∧ store = []) := by
  obtain ⟨body, rendered, source⟩ := Input.emit_success emitted_eq
  have fresh : ∀ name ∈ ["sc_input"], OlderThan 0 name := by
    intro name mem index same
    simp only [List.mem_singleton] at mem
    subst mem
    exact absurd same (input_not_temporary index)
  obtain ⟨statements, lines, _, _, _, simulates⟩ :=
    render_spec function.body 1 .word ["sc_input"] 8 0 body function.fragment rendered fresh
  refine ⟨inputFile statements body.value, ?_, ?_⟩
  · have functionLine :
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
    rfl
  · intro input
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
      simulates [.word input] [] [("sc_input", .word input.val)] [[("input", .uint256 input.val)]]
        agree
    obtain ⟨word, rfl, rfl⟩ := represents
    have applied : Solcore.Core.Evaluates [] []
        (function.instantiate input).toCore.body (.word word) [] := by
      simp only [CheckedWordFunction.instantiate, CheckedWordFunction.program,
        Solcore.Synthesis.Core.wordFunctionProgram, Solcore.Core.Wire.Program.toCore,
        Solcore.Core.Wire.Expr.toCore]
      exact .apply .lambda .word evaluates
    refine ⟨word, ?_, (runStateful_of_evaluates applied).1, (runStateful_of_evaluates applied).2⟩
    have parameters : Method.bindParameters ["input"] [input.val] =
        some [("input", .uint256 input.val)] := by
      simp [Method.bindParameters, word_lt_modulus]
    have execBody : Stmt.execList [[], [("input", .uint256 input.val)]]
        (.letDecl "sc_input" .word (.typedefRep (.name "input")) :: statements) =
          some (scope' :: outer') := by
      simp only [Stmt.execList, input_declaration]
      exact exec
    simp [SourceFile.call, Method.run, parameters, execBody, inputFile, Expr.eval, lookup]

end Solcore.Synthesis.Source.ScalarMeaning
