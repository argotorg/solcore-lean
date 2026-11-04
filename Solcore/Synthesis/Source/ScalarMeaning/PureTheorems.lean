import Solcore.Core.Correspondence
import Solcore.Synthesis.Internal.Functions
import Solcore.Synthesis.Source.Emitter
import Solcore.Synthesis.Source.ScalarMeaning.Internal.Renderer
import Solcore.Synthesis.Source.ScalarMeaning.Grammar
import Solcore.Synthesis.Source.ScalarMeaning.Internal.CallGraphs
import Solcore.Synthesis.Internal.CallGraphs
import Solcore.Synthesis.Source.ScalarMeaning.Internal.Mutation
import Solcore.Synthesis.Internal.Aggregates
import Solcore.Synthesis.Source.ScalarMeaning.Internal.Aggregates

/-!
# Emitter meaning: pure profiles

What each pure emitter prints means what the original Core program computes. Main theorems:
`emit_source_meaning`, `Input.emit_source_meaning`, `Function.emit_source_meaning`,
`Primitive.emit_source_meaning`, `CallGraph.emit_source_meaning`, `Mutation.emit_source_meaning`,
`Aggregate.emit_source_meaning`, `AggregateCallGraph.emit_source_meaning`.
-/

section
-- leanmerge: from Solcore.Synthesis.Source.ScalarMeaning.Emitter
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
end

section
-- leanmerge: from Solcore.Synthesis.Source.ScalarMeaning.FunctionEmitter
/-! Meaning preservation for the actual named-helper emitter (`Function.emit`,
profile `runtime-functions`). Each Core helper lambda becomes a free function
`sc_fn<k>(sc_arg: word) returns (word)` before the contract. Under the source
semantics a helper sees only earlier helpers, matching the Core binding chain
whose closures capture only earlier helpers. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.ScalarMeaning

open Solcore.Synthesis.Core (CheckedWordFunctionDAG functionAcceptsAt functionDAGExpression
  functionHelpersAccepted)
open Solcore.Synthesis.Source.ScalarRenderer (Rendered)

/-! ### The emitter's helper loop -/

/-- The helper loop of the named-helper emitters, by structural recursion,
for the renderer each emitter uses. -/
def helperLoop (render : RenderFn) : List CoreExpr → Nat → List String → List String →
    Except EmitError (List String × List String)
  | [], _, names, lines => .ok (names, lines)
  | body :: rest, index, names, lines =>
      (render names .word ["sc_arg"] 4 0 body).bind fun rendered =>
        helperLoop render rest (index + 1) (Function.helperName index :: names)
          (lines ++
            ["function " ++ Function.helperName index ++ "(sc_arg: word) returns (word) {"] ++
            rendered.lines ++ ["    return " ++ rendered.value ++ ";", "}", ""])

theorem forIn_helperLoop {render : RenderFn}
    {step : CoreExpr × Nat → List String × List String →
      Except EmitError (ForInStep (List String × List String))}
    (stepEq : ∀ body index names lines, step (body, index) (names, lines) =
      (render names .word ["sc_arg"] 4 0 body).bind fun rendered =>
        .ok (.yield (Function.helperName index :: names,
          lines ++
            ["function " ++ Function.helperName index ++ "(sc_arg: word) returns (word) {"] ++
            rendered.lines ++ ["    return " ++ rendered.value ++ ";", "}", ""]))) :
    ∀ (bodies : List CoreExpr) (start : Nat) (names lines : List String),
      forIn (bodies.zipIdx start) (names, lines) step = helperLoop render bodies start names lines
  | [], _, _, _ => rfl
  | body :: rest, start, names, lines => by
      rw [List.zipIdx_cons, List.forIn_cons, stepEq, helperLoop]
      cases render names .word ["sc_arg"] 4 0 body with
      | error error => rfl
      | ok rendered => exact forIn_helperLoop stepEq rest (start + 1) _ _

theorem Function.emit_success {graph : CheckedWordFunctionDAG} {emitted : EmittedProgram}
    (emitted_eq : Function.emit graph = .ok emitted) :
    ∃ (names lines : List String) (entry : Rendered),
      helperLoop ScalarRenderer.renderWithFunctions graph.helpers 0 []
        ["import * from std;", "import * from std.dispatch;", ""] = .ok (names, lines) ∧
      ScalarRenderer.renderWithFunctions names .word ["sc_input"] 8 0 graph.entry = .ok entry ∧
      emitted.source = String.intercalate "\n" (lines ++
        ["contract " ++ Function.contractName ++ " {",
          "    function " ++ Function.methodName ++ "(input: uint256) public returns (uint256) {",
          "        let sc_input: word = Typedef.rep(input);"] ++ entry.lines ++
        ["        return uint256(" ++ entry.value ++ ");", "    }", "}"]) ++ "\n" := by
  unfold Function.emit at emitted_eq
  dsimp only at emitted_eq
  rw [forIn_helperLoop (render := ScalarRenderer.renderWithFunctions) (fun _ _ _ _ => rfl)]
    at emitted_eq
  cases loop : helperLoop ScalarRenderer.renderWithFunctions graph.helpers 0 []
    ["import * from std;", "import * from std.dispatch;", ""] with
  | error error =>
      rw [loop] at emitted_eq
      cases emitted_eq
  | ok result =>
      obtain ⟨names, lines⟩ := result
      rw [loop] at emitted_eq
      cases entry : ScalarRenderer.renderWithFunctions names .word ["sc_input"] 8 0 graph.entry with
      | error error =>
          simp only [bind, Except.bind, entry] at emitted_eq
          cases emitted_eq
      | ok rendered =>
          simp only [bind, Except.bind, entry, pure, Except.pure, Except.ok.injEq] at emitted_eq
          subst emitted_eq
          exact ⟨names, lines, rendered, rfl, entry, rfl⟩

/-! ### Helper names and the Core closure chain -/

/-- Earlier helper names, nearest first. -/
def helperNames : Nat → List String
  | 0 => []
  | count + 1 => Function.helperName count :: helperNames count

theorem helperName_injective {first second : Nat}
    (same : Function.helperName first = Function.helperName second) : first = second := by
  have chars := congrArg String.toList same
  simp only [Function.helperName, String.toList_append, Nat.toString_eq_repr, Nat.toList_repr,
    List.append_cancel_left_eq] at chars
  have values := congrArg (fun digits => Nat.ofDigitChars 10 digits 0) chars
  simpa using values

theorem mem_helperNames {name : String} {count : Nat} :
    name ∈ helperNames count ↔ ∃ index, index < count ∧ name = Function.helperName index := by
  induction count with
  | zero => simp [helperNames]
  | succ count ih =>
      simp only [helperNames, List.mem_cons, ih]
      constructor
      · rintro (same | ⟨index, below, same⟩)
        · exact ⟨count, Nat.lt_succ_self _, same⟩
        · exact ⟨index, by omega, same⟩
      · rintro ⟨index, below, same⟩
        by_cases last : index = count
        · subst last
          exact Or.inl same
        · exact Or.inr ⟨index, by omega, same⟩

theorem helperName_not_mem (count : Nat) : Function.helperName count ∉ helperNames count := by
  intro mem
  obtain ⟨index, below, same⟩ := mem_helperNames.mp mem
  have := helperName_injective same
  omega

theorem helperName_valid (index : Nat) : ValidIdentifier (Function.helperName index) := by
  refine ⟨'s', ['c', '_', 'f', 'n'] ++ Nat.toDigits 10 index, by simp [Function.helperName],
    by decide, ?_⟩
  intro char mem
  rcases List.mem_append.mp mem with prefix_ | digit
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at prefix_
    rcases prefix_ with rfl | rfl | rfl | rfl <;> decide
  · exact (digit_classes (toDigits_mem digit)).2.2

theorem helperName_not_reserved (index : Nat) :
    isReserved (Function.helperName index) = false := by
  have heads : ∀ word ∈ reservedWords, word.toList.head? ≠ some 's' := by decide
  have absent : Function.helperName index ∉ reservedWords := by
    intro mem
    exact heads _ mem (by simp [Function.helperName])
  cases reserved : isReserved (Function.helperName index)
  · rfl
  · exact absurd (List.elem_iff.mp reserved) absent

theorem helperNames_ok {count : Nat} :
    ∀ name ∈ helperNames count, ValidIdentifier name ∧ isReserved name = false := by
  intro name mem
  obtain ⟨index, _, rfl⟩ := mem_helperNames.mp mem
  exact ⟨helperName_valid index, helperName_not_reserved index⟩

theorem argument_not_temporary (index : Nat) : "sc_arg" ≠ temporary index := by
  intro same
  have chars := congrArg String.toList same
  simp [temporary] at chars

/-- Core's binding chain: each helper lambda closes over the earlier helpers,
nearest first. -/
def closureStep (closures : List CoreValue) (body : CoreExpr) : List CoreValue :=
  .closure (Solcore.Core.Wire.Ty.toCore .word) (Solcore.Core.Wire.Ty.toCore .word) body.toCore
    closures :: closures

theorem dag_evaluates (entry : CoreExpr) : ∀ (helpers : List CoreExpr)
    (environment : Solcore.Core.Environment) (store : Solcore.Core.Store),
    Solcore.Core.Evaluates environment store (functionDAGExpression helpers entry).toCore
      (.closure (Solcore.Core.Wire.Ty.toCore .word) (Solcore.Core.Wire.Ty.toCore .word)
        entry.toCore (helpers.foldl closureStep environment)) store
  | [], environment, store => by
      simp only [functionDAGExpression, List.foldr_nil, Solcore.Core.Wire.Expr.toCore,
        List.foldl_nil]
      exact .lambda
  | helper :: rest, environment, store => by
      simp only [functionDAGExpression, List.foldr_cons, Solcore.Core.Wire.Expr.toCore,
        List.foldl_cons] at *
      exact .letE .lambda (dag_evaluates entry rest _ store)

theorem Context.call_cons_same (name : String) (meaning : List Value → Option Value)
    (functions : List (String × (List Value → Option Value))) (aliases : List (String × String))
    (arguments : List Value) :
    Context.call ⟨(name, meaning) :: functions, aliases⟩ name arguments = meaning arguments := by
  simp [Context.call]

theorem Context.call_cons_other {name other : String} (different : name ≠ other)
    (meaning : List Value → Option Value)
    (functions : List (String × (List Value → Option Value))) (aliases : List (String × String))
    (arguments : List Value) :
    Context.call ⟨(name, meaning) :: functions, aliases⟩ other arguments =
      Context.call ⟨functions, aliases⟩ other arguments := by
  simp [Context.call, different]

/-- A newly declared helper extends the agreement between helper names and
Core closures. -/
theorem FunctionsAgree.extend {functions : List (String × (List Value → Option Value))}
    {aliases : List (String × String)} {names : List String} {closures : List CoreValue}
    (agree : FunctionsAgree ⟨functions, aliases⟩ names closures) {name : String}
    (fresh : name ∉ names) {meaning : List Value → Option Value}
    {parameterType resultType : Solcore.Core.Ty} {body : Solcore.Core.Expr}
    (behaves : ∀ (argument : Solcore.Core.Word) (store : Solcore.Core.Store),
      ∃ result : Solcore.Core.Word,
        Solcore.Core.Evaluates (.word argument :: closures) store body (.word result) store ∧
        meaning [.word argument.val] = some (.word result.val)) :
    FunctionsAgree ⟨(name, meaning) :: functions, aliases⟩ (name :: names)
      (.closure parameterType resultType body closures :: closures) := by
  intro index found foundName
  cases index with
  | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at foundName
      subst foundName
      refine ⟨parameterType, resultType, body, closures, rfl, fun argument store => ?_⟩
      obtain ⟨result, evaluates, called⟩ := behaves argument store
      exact ⟨result, evaluates, by rw [Context.call_cons_same]; exact called⟩
  | succ index =>
      simp only [List.getElem?_cons_succ] at foundName
      have different : name ≠ found := fun same =>
        fresh (same ▸ List.mem_of_getElem? foundName)
      obtain ⟨parameterType', resultType', body', captured, closureFound, behaves'⟩ :=
        agree index found foundName
      refine ⟨parameterType', resultType', body', captured, by simpa using closureFound,
        fun argument store => ?_⟩
      obtain ⟨result, evaluates, called⟩ := behaves' argument store
      exact ⟨result, evaluates, by rw [Context.call_cons_other different]; exact called⟩

/-! ### Helpers as free functions -/

/-- The free function printed for one rendered helper. -/
def helperDecl (index : Nat) (statements : List Stmt) (value : String) : FunctionDecl where
  name := Function.helperName index
  parameters := [("sc_arg", .word)]
  resultType := .word
  body := statements
  result := .name value

private theorem string_eq_of_toList' {first second : String}
    (same : first.toList = second.toList) : first = second :=
  String.toList_inj.mp same

/-- The helper loop prints free functions whose meanings agree with the Core
closures of the binding chain. It holds for any renderer that meets its
rendering specification in the admitted call contexts, provided that adding a
helper keeps a context admitted. -/
theorem helperLoop_spec {render : RenderFn} {admits : Context → Prop} {called : List String}
    {aliases : List (String × String)}
    (renderSpec : ∀ expression, RenderIH render admits called expression)
    (calledOk : ∀ callee ∈ called, ValidIdentifier callee ∧ isReserved callee = false)
    (extendAdmits : ∀ (functions : List (String × (List Value → Option Value))) (index : Nat)
      (meaning : List Value → Option Value), admits ⟨functions, aliases⟩ →
      admits ⟨(Function.helperName index, meaning) :: functions, aliases⟩) :
    ∀ (bodies : List CoreExpr) (start : Nat) (lines names' lines' : List String)
      (functions : List (String × (List Value → Option Value))) (closures : List CoreValue),
    helperLoop render bodies start (helperNames start) lines = .ok (names', lines') →
    (∀ (index : Nat) (body : CoreExpr), bodies[index]? = some body →
      functionAcceptsAt 1 (start + index) .word body = true) →
    admits ⟨functions, aliases⟩ →
    FunctionsAgree ⟨functions, aliases⟩ (helperNames start) closures →
    ∃ declarations : List FunctionDecl,
      lines' = lines ++ declarations.flatMap FunctionDecl.lines ∧
      names' = helperNames (start + bodies.length) ∧
      (∀ declaration ∈ declarations, declaration.NamesOk ∧
        ∀ name ∈ declaration.identifiers, ValidIdentifier name) ∧
      admits ⟨declareFunctions aliases functions declarations, aliases⟩ ∧
      FunctionsAgree ⟨declareFunctions aliases functions declarations, aliases⟩ names'
        (bodies.foldl closureStep closures)
  | [], start, lines, names', lines', functions, closures, loop, _, admitted, agree => by
      simp only [helperLoop, Except.ok.injEq, Prod.mk.injEq] at loop
      obtain ⟨rfl, rfl⟩ := loop
      exact ⟨[], by simp, by simp, by simp, by simpa [declareFunctions] using admitted,
        by simpa [declareFunctions] using agree⟩
  | body :: rest, start, lines, names', lines', functions, closures, loop, accepted, admitted,
      agree => by
      simp only [helperLoop] at loop
      obtain ⟨rendered, renderedEquation, loop⟩ := except_bind_eq_ok loop
      have fresh : ∀ name ∈ ["sc_arg"], OlderThan 0 name := by
        intro name mem index same
        simp only [List.mem_singleton] at mem
        subst mem
        exact absurd same (argument_not_temporary index)
      obtain ⟨statements, lines₁, _, valueName, names, simulates⟩ :=
        renderSpec body (helperNames start) 1 start .word ["sc_arg"] 4 0 rendered
          (by simpa using accepted 0 body rfl) renderedEquation fresh
      let declaration := helperDecl start statements rendered.value
      have behaves : ∀ (argument : Solcore.Core.Word) (store : Solcore.Core.Store),
          ∃ result : Solcore.Core.Word,
            Solcore.Core.Evaluates (.word argument :: closures) store body.toCore
              (.word result) store ∧
            declaration.denote ⟨functions, aliases⟩ [.word argument.val] =
              some (.word result.val) := by
        intro argument store
        have localsAgree : LocalsAgree [[], [("sc_arg", .word argument.val)]] ["sc_arg"]
            (.word argument :: closures) := by
          intro index name found
          cases index with
          | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at found
              subst found
              exact ⟨argument, rfl, by simp [Frames.lookup, Scope.get?]⟩
          | succ index => simp at found
        obtain ⟨core, value, scope', outer', _, evaluates, represents, exec, lookup, _⟩ :=
          simulates ⟨functions, aliases⟩ (.word argument :: closures) store [] _ admitted
            localsAgree (by simp) (by simpa using agree)
        obtain ⟨result, rfl, rfl⟩ := represents
        refine ⟨result, evaluates, ?_⟩
        simp [declaration, helperDecl, FunctionDecl.denote, FunctionDecl.bindParameters,
          LocalType.admits, exec, Expr.eval, lookup]
      have extended := agree.extend (helperName_not_mem start) behaves
        (parameterType := Solcore.Core.Wire.Ty.toCore .word)
        (resultType := Solcore.Core.Wire.Ty.toCore .word)
      have restAccepted : ∀ (index : Nat) (body : CoreExpr), rest[index]? = some body →
          functionAcceptsAt 1 (start + 1 + index) .word body = true := by
        intro index body found
        have accepted' := accepted (index + 1) body (by simpa using found)
        rwa [show start + (index + 1) = start + 1 + index by omega] at accepted'
      obtain ⟨declarations, rest₁, rest₂, rest₃, rest₄, rest₅⟩ :=
        helperLoop_spec renderSpec calledOk extendAdmits rest (start + 1) _ names' lines' _ _
          loop restAccepted (extendAdmits functions start _ admitted) extended
      have block :
          ["function " ++ Function.helperName start ++ "(sc_arg: word) returns (word) {"] ++
          rendered.lines ++ ["    return " ++ rendered.value ++ ";", "}", ""] =
          declaration.lines := by
        simp only [declaration, helperDecl, FunctionDecl.lines, lines₁, List.cons_append,
          List.nil_append, List.cons.injEq]
        refine ⟨?_, ?_⟩
        · apply string_eq_of_toList'
          simp [FunctionDecl.parameterText, LocalType.spelling]
        · simp [Expr.print]
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
          have localsOk : ∀ local_ ∈ ["sc_arg"], ValidIdentifier local_ ∧
              isReserved local_ = false := by
            intro local_ mem
            simp only [List.mem_singleton] at mem
            subst mem
            exact ⟨keyword_valid (by decide), by decide⟩
          have bodyOk := fun name mem =>
            rendered_identifier_ok localsOk helperNames_ok calledOk (names name mem)
          have valueOk := rendered_name_ok localsOk valueName
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

theorem helpers_accepted {helpers : List CoreExpr}
    (accepted : functionHelpersAccepted helpers = true) :
    ∀ (index : Nat) (body : CoreExpr), helpers[index]? = some body →
      functionAcceptsAt 1 (0 + index) .word body = true := by
  intro index body found
  have all := List.all_eq_true.mp accepted (body, index)
    (List.mem_zipIdx_iff_getElem?.mpr found)
  simpa using all

/-! ### The emitted file -/

/-- The source file printed by the named-helper emitter. -/
def functionsFile (declarations : List FunctionDecl) (body : List Stmt) (value : String) :
    SourceFile where
  opcodeAliases := []
  functions := declarations
  contract := "SynthesizedFunctions"
  method := {
    name := "run"
    parameters := ["input"]
    body := .letDecl "sc_input" .word (.typedefRep (.name "input")) :: body
    result := .uint256 (.name value) }

/-- **Named-helper emitter preservation.** If the actual emitter succeeds, its
source text is the printing of a file with one free function per helper and
parses back to it. For every runtime input, calling `run(uint256)` under the
independent source semantics returns exactly the Word that the original Core
binding chain, applied to that input, returns. -/
theorem Function.emit_preserves_meaning {graph : CheckedWordFunctionDAG}
    {emitted : EmittedProgram} (emitted_eq : Function.emit graph = .ok emitted) :
    ∃ file : SourceFile, emitted.source = file.print ∧ parseSource emitted.source = some file ∧
      ∀ input : Solcore.Core.Word, ∃ word : Solcore.Core.Word,
        file.call "run" [input.val] = some word.val ∧
        CoreReturns (graph.instantiate input).toCore word := by
  obtain ⟨names, lines, entry, loop, entryEquation, source⟩ := Function.emit_success emitted_eq
  obtain ⟨declarations, linesEq, namesEq, declarationsOk, _, agree⟩ :=
    helperLoop_spec (render_spec (fun _ => True) [])
      (fun _ absent => absurd absent List.not_mem_nil) (fun _ _ _ _ => trivial) graph.helpers 0 _
      names lines [] [] loop (helpers_accepted graph.helperScopes) trivial
      (fun _ _ found => by simp [helperNames] at found)
  have fresh : ∀ name ∈ ["sc_input"], OlderThan 0 name := by
    intro name mem index same
    simp only [List.mem_singleton] at mem
    subst mem
    exact absurd same (input_not_temporary index)
  obtain ⟨statements, entryLines, _, valueName, entryNames, simulates⟩ :=
    render_spec (fun _ => True) [] graph.entry names 1 graph.helpers.length .word ["sc_input"] 8 0
      entry
      graph.entryScope entryEquation fresh
  let file := functionsFile declarations statements entry.value
  have localsOk : ∀ local_ ∈ ["sc_input"], ValidIdentifier local_ ∧
      isReserved local_ = false := by
    intro local_ mem
    simp only [List.mem_singleton] at mem
    subst mem
    exact ⟨keyword_valid (by decide), by decide⟩
  have functionNamesOk : ∀ name ∈ names, ValidIdentifier name ∧ isReserved name = false := by
    rw [namesEq]
    exact helperNames_ok
  have printed : emitted.source = file.print := by
    have functionLine :
        "    function " ++ Function.methodName ++ "(input: uint256) public returns (uint256) {" =
          "    function " ++ file.method.name ++ "(" ++
            Method.parameterText file.method.parameters ++ ") public returns (uint256) {" := by
      apply string_eq_of_toList'
      simp [file, functionsFile, Method.parameterText, Function.methodName]
    have returnLine : "        return uint256(" ++ entry.value ++ ");" =
        "        return " ++ file.method.result.print ++ ";" := by
      apply string_eq_of_toList'
      simp [file, functionsFile, Expr.print]
    have bodyLines : Stmt.listLines 8 file.method.body =
        "        let sc_input: word = Typedef.rep(input);" :: Stmt.listLines 8 statements := by
      simpa [file, functionsFile, inputFile] using inputFile_body_lines statements entry.value
    rw [source, SourceFile.print, SourceFile.lines, bodyLines, entryLines, linesEq, functionLine,
      returnLine]
    simp [file, functionsFile, aliasImportLines, Function.contractName]
  have valueOk := rendered_name_ok localsOk valueName
  have bodyNames : ∀ name ∈ Stmt.listIdentifiers file.method.body,
      ValidIdentifier name ∧ isReserved name = false := by
    intro name mem
    simp only [file, functionsFile, Stmt.listIdentifiers, Stmt.identifiers, Expr.identifiers,
      List.cons_append, List.nil_append, List.mem_cons] at mem
    rcases mem with rfl | rfl | mem
    · exact ⟨keyword_valid (by decide), by decide⟩
    · exact ⟨keyword_valid (by decide), by decide⟩
    · exact rendered_identifier_ok localsOk functionNamesOk
        (fun _ absent => absurd absent List.not_mem_nil) (entryNames name mem)
  have parsed : parseSource emitted.source = some file := by
    rw [printed]
    apply parseSource_print
    · refine ⟨fun declaration mem => (declarationsOk declaration mem).1, rfl, rfl, ?_,
        fun name mem => (bodyNames name mem).2, ?_⟩
      · intro parameter mem
        simp only [file, functionsFile, List.mem_singleton] at mem
        subst mem
        decide
      · intro name mem
        simp only [file, functionsFile, Expr.identifiers, List.mem_singleton] at mem
        subst mem
        exact valueOk.2
    · refine ⟨fun _ absent => absurd absent List.not_mem_nil,
        fun declaration mem => (declarationsOk declaration mem).2,
        keyword_valid (show validIdentifier "SynthesizedFunctions" = true by decide),
        keyword_valid (show validIdentifier "run" = true by decide), ?_,
        fun name mem => (bodyNames name mem).1, ?_⟩
      · intro parameter mem
        simp only [file, functionsFile, List.mem_singleton] at mem
        subst mem
        exact keyword_valid (by decide)
      · intro name mem
        simp only [file, functionsFile, Expr.identifiers, List.mem_singleton] at mem
        subst mem
        exact valueOk.1
  refine ⟨file, printed, parsed, ?_⟩
  intro input
  have closures := graph.helpers.foldl closureStep []
  have localsAgree : LocalsAgree [[("sc_input", .word input.val)], [("input", .uint256 input.val)]]
      ["sc_input"] (.word input :: graph.helpers.foldl closureStep []) := by
    intro index name found
    cases index with
    | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at found
        subst found
        exact ⟨input, rfl, by simp [Frames.lookup, Scope.get?]⟩
    | succ index => simp at found
  have context : file.context = ⟨declareFunctions [] [] declarations, []⟩ := rfl
  obtain ⟨core, value, scope', outer', _, evaluates, represents, exec, lookup, _⟩ :=
    simulates file.context (.word input :: graph.helpers.foldl closureStep []) []
      [("sc_input", .word input.val)] [[("input", .uint256 input.val)]] trivial localsAgree
      (by simp) (by rw [context]; simpa using agree)
  obtain ⟨word, rfl, rfl⟩ := represents
  have applied : Solcore.Core.Evaluates [] []
      (graph.instantiate input).toCore.body (.word word) [] := by
    simp only [CheckedWordFunctionDAG.instantiate, CheckedWordFunctionDAG.program,
      Solcore.Synthesis.Core.functionDAGProgram, Solcore.Core.Wire.Program.toCore]
    simp only [Solcore.Core.Wire.Expr.toCore]
    exact .apply (dag_evaluates graph.entry graph.helpers [] []) .word evaluates
  refine ⟨word, ?_, runStateful_of_evaluates applied⟩
  have parameters : Method.bindParameters ["input"] [input.val] =
      some [("input", .uint256 input.val)] := by
    simp [Method.bindParameters, word_lt_modulus]
  have execBody : Stmt.execList file.context [[], [("input", .uint256 input.val)]]
      (.letDecl "sc_input" .word (.typedefRep (.name "input")) :: statements) =
        some (scope' :: outer') := by
    simp only [Stmt.execList, input_declaration]
    exact exec
  simp only [file, functionsFile] at execBody
  simp [file, functionsFile, SourceFile.call, Method.run, parameters, execBody, Expr.eval, lookup]

/-- **Named-helper emitter preservation, on the emitted text.** -/
theorem Function.emit_source_meaning {graph : CheckedWordFunctionDAG}
    {emitted : EmittedProgram} (emitted_eq : Function.emit graph = .ok emitted)
    (input : Solcore.Core.Word) :
    ∃ word : Solcore.Core.Word,
      sourceCall emitted.source "run" [input.val] = some word.val ∧
      CoreReturns (graph.instantiate input).toCore word := by
  obtain ⟨file, _, parsed, meaning⟩ := Function.emit_preserves_meaning emitted_eq
  obtain ⟨word, called, core⟩ := meaning input
  exact ⟨word, by simp [sourceCall, parsed, called], core⟩

end Solcore.Synthesis.Source.ScalarMeaning
end

section
-- leanmerge: from Solcore.Synthesis.Source.ScalarMeaning.PrimitiveEmitter
/-! Meaning preservation for the actual primitive wrapper (`Primitive.emit`,
contract `SynthesizedPrimitives`, method `run(uint256)`). It imports fourteen
raw `std.opcodes` aliases; the source semantics gives each the EVM instruction
of its opcode, and `tobool` the standard library meaning. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.ScalarMeaning

open Solcore.Synthesis.Core (CheckedWordFunction)

/-- The file printed by the primitive wrapper: the runtime-input method after
the raw opcode import line. -/
def primitiveFile (body : List Stmt) (value : String) : SourceFile := {
  opcodeAliases := primitiveAliases
  functions := []
  contract := "SynthesizedPrimitives"
  method := (inputFile body value).method }

theorem opcodeImport_eq : Primitive.opcodeImport = aliasImportLine primitiveAliases := by
  decide +kernel

theorem primitiveImportLines :
    aliasImportLines primitiveAliases = [aliasImportLine primitiveAliases] :=
  rfl

/-- Without free functions, the file's aliases are the whole call context. -/
theorem primitiveContext_aliases : PrimitiveContext ⟨[], primitiveAliases⟩ := by
  refine ⟨?_, fun _ => rfl⟩
  intro alias mem arguments
  simp only [primitiveAliases, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> rfl

theorem primitiveCallees_ok :
    ∀ callee ∈ primitiveCallees, ValidIdentifier callee ∧ isReserved callee = false := by
  have checked : ∀ callee ∈ primitiveCallees,
      validIdentifier callee = true ∧ isReserved callee = false := by
    decide
  exact fun callee mem => ⟨keyword_valid (checked callee mem).1, (checked callee mem).2⟩

theorem primitiveAliases_valid :
    ∀ alias ∈ primitiveAliases, ValidIdentifier alias.1 ∧ ValidIdentifier alias.2 := by
  have checked : ∀ alias ∈ primitiveAliases,
      validIdentifier alias.1 = true ∧ validIdentifier alias.2 = true := by
    decide
  exact fun alias mem => ⟨keyword_valid (checked alias mem).1, keyword_valid (checked alias mem).2⟩

theorem Primitive.emit_success {function : CheckedWordFunction} {emitted : EmittedProgram}
    (emitted_eq : Primitive.emit function = .ok emitted) :
    ∃ body : ScalarRenderer.Rendered,
      PrimitiveRenderer.render .word ["sc_input"] 8 0 function.body = .ok body ∧
      emitted.source = String.intercalate "\n" (["import * from std;",
        "import * from std.dispatch;", Primitive.opcodeImport, "",
        "contract " ++ Primitive.contractName ++ " {",
        "    function " ++ Primitive.methodName ++ "(input: uint256) public returns (uint256) {",
        "        let sc_input: word = Typedef.rep(input);"] ++ body.lines ++
        ["        return uint256(" ++ body.value ++ ");", "    }", "}"]) ++ "\n" := by
  unfold Primitive.emit at emitted_eq
  cases rendered : PrimitiveRenderer.render .word ["sc_input"] 8 0 function.body with
  | error error =>
      rw [rendered] at emitted_eq
      cases emitted_eq
  | ok body =>
      rw [rendered] at emitted_eq
      cases emitted_eq
      exact ⟨body, rfl, rfl⟩

/-- **Raw primitive emitter preservation.** If the actual primitive emitter
succeeds, its source text is the printing of one source file and parses back
to it. For every runtime input, calling `run(uint256)` under the independent
source semantics returns exactly the Word that the original Core function
applied to that input returns, including the division, remainder, shift,
signed, byte, sign-extension, exponent, leading-zero and modular operations
reached through raw opcode aliases. -/
theorem Primitive.emit_preserves_meaning {function : CheckedWordFunction}
    {emitted : EmittedProgram} (emitted_eq : Primitive.emit function = .ok emitted) :
    ∃ file : SourceFile, emitted.source = file.print ∧ parseSource emitted.source = some file ∧
      ∀ input : Solcore.Core.Word, ∃ word : Solcore.Core.Word,
        file.call "run" [input.val] = some word.val ∧
        CoreReturns (function.instantiate input).toCore word := by
  obtain ⟨body, rendered, source⟩ := Primitive.emit_success emitted_eq
  have fresh : ∀ name ∈ ["sc_input"], OlderThan 0 name := by
    intro name mem index same
    simp only [List.mem_singleton] at mem
    subst mem
    exact absurd same (input_not_temporary index)
  obtain ⟨statements, lines, _, valueName, names, simulates⟩ :=
    primitive_render_spec function.body [] 1 0 .word ["sc_input"] 8 0 body
      (acceptsAt_functionAcceptsAt _ 0 function.fragment) rendered fresh
  let file := primitiveFile statements body.value
  have localsOk : ∀ local_ ∈ ["sc_input"], ValidIdentifier local_ ∧
      isReserved local_ = false := by
    intro local_ mem
    simp only [List.mem_singleton] at mem
    subst mem
    exact ⟨keyword_valid (by decide), by decide⟩
  have printed : emitted.source = file.print := by
    have functionLine :
        "    function " ++ Primitive.methodName ++ "(input: uint256) public returns (uint256) {" =
          "    function " ++ file.method.name ++ "(" ++
            Method.parameterText file.method.parameters ++ ") public returns (uint256) {" := by
      apply String.toList_inj.mp
      simp [file, primitiveFile, inputFile, Method.parameterText, Primitive.methodName]
    have returnLine : "        return uint256(" ++ body.value ++ ");" =
        "        return " ++ file.method.result.print ++ ";" := by
      apply String.toList_inj.mp
      simp [file, primitiveFile, inputFile, Expr.print]
    have bodyLines : Stmt.listLines 8 file.method.body =
        "        let sc_input: word = Typedef.rep(input);" :: Stmt.listLines 8 statements :=
      inputFile_body_lines statements body.value
    rw [source, SourceFile.print, SourceFile.lines, bodyLines, lines, functionLine, returnLine]
    simp [file, primitiveFile, primitiveImportLines, Primitive.contractName, opcodeImport_eq]
  have valueOk := rendered_name_ok localsOk valueName
  have bodyNames : ∀ name ∈ Stmt.listIdentifiers file.method.body,
      ValidIdentifier name ∧ isReserved name = false := by
    intro name mem
    simp only [file, primitiveFile, inputFile, Stmt.listIdentifiers, Stmt.identifiers,
      Expr.identifiers, List.cons_append, List.nil_append, List.mem_cons] at mem
    rcases mem with rfl | rfl | mem
    · exact ⟨keyword_valid (by decide), by decide⟩
    · exact ⟨keyword_valid (by decide), by decide⟩
    · exact rendered_identifier_ok localsOk (fun _ absent => absurd absent List.not_mem_nil)
        primitiveCallees_ok (names name mem)
  have parsed : parseSource emitted.source = some file := by
    rw [printed]
    apply parseSource_print
    · refine ⟨fun _ absent => absurd absent List.not_mem_nil, rfl, rfl, ?_,
        fun name mem => (bodyNames name mem).2, ?_⟩
      · intro parameter mem
        simp only [file, primitiveFile, inputFile, List.mem_singleton] at mem
        subst mem
        decide
      · intro name mem
        simp only [file, primitiveFile, inputFile, Expr.identifiers, List.mem_singleton] at mem
        subst mem
        exact valueOk.2
    · refine ⟨primitiveAliases_valid, fun _ absent => absurd absent List.not_mem_nil,
        keyword_valid (show validIdentifier "SynthesizedPrimitives" = true by decide),
        keyword_valid (show validIdentifier "run" = true by decide), ?_,
        fun name mem => (bodyNames name mem).1, ?_⟩
      · intro parameter mem
        simp only [file, primitiveFile, inputFile, List.mem_singleton] at mem
        subst mem
        exact keyword_valid (by decide)
      · intro name mem
        simp only [file, primitiveFile, inputFile, Expr.identifiers, List.mem_singleton] at mem
        subst mem
        exact valueOk.1
  refine ⟨file, printed, parsed, ?_⟩
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
  have context : file.context = ⟨[], primitiveAliases⟩ := rfl
  obtain ⟨core, value, scope', outer', _, evaluates, represents, exec, lookup, _⟩ :=
    simulates file.context [.word input] [] [("sc_input", .word input.val)]
      [[("input", .uint256 input.val)]] (context ▸ primitiveContext_aliases) agree (by simp)
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
  have execBody : Stmt.execList file.context [[], [("input", .uint256 input.val)]]
      (.letDecl "sc_input" .word (.typedefRep (.name "input")) :: statements) =
        some (scope' :: outer') := by
    simp only [Stmt.execList, input_declaration]
    exact exec
  simp only [file, primitiveFile, inputFile] at execBody
  simp [file, SourceFile.call, Method.run, parameters, execBody, primitiveFile, inputFile,
    Expr.eval, lookup]

/-- **Raw primitive emitter preservation, on the emitted text.** -/
theorem Primitive.emit_source_meaning {function : CheckedWordFunction}
    {emitted : EmittedProgram} (emitted_eq : Primitive.emit function = .ok emitted)
    (input : Solcore.Core.Word) :
    ∃ word : Solcore.Core.Word,
      sourceCall emitted.source "run" [input.val] = some word.val ∧
      CoreReturns (function.instantiate input).toCore word := by
  obtain ⟨file, _, parsed, meaning⟩ := Primitive.emit_preserves_meaning emitted_eq
  obtain ⟨word, called, core⟩ := meaning input
  exact ⟨word, by simp [sourceCall, parsed, called], core⟩

end Solcore.Synthesis.Source.ScalarMeaning
end

section
-- leanmerge: from Solcore.Synthesis.Source.ScalarMeaning.CallGraphEmitter
/-! Meaning preservation for the actual call-graph emitter (`CallGraph.emit`,
profile `runtime-call-graphs`). As for the named-helper emitter, each Core
helper becomes a free function that sees only earlier helpers. Every function
body may also call the fourteen raw opcode aliases, which the file imports. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.ScalarMeaning

open Solcore.Synthesis.Core (CheckedWordFunctionDAG)
open Solcore.Synthesis.Source.ScalarRenderer (Rendered)

theorem helperName_not_callee (index : Nat) :
    ∀ callee ∈ primitiveCallees, Function.helperName index ≠ callee := by
  have heads : ∀ callee ∈ primitiveCallees, callee.toList.take 4 ≠ ['s', 'c', '_', 'f'] := by
    decide
  intro callee mem same
  apply heads callee mem
  rw [← same]
  simp [Function.helperName]

/-- Declaring a helper keeps the primitive aliases and `tobool` reachable. -/
theorem PrimitiveContext.extend {functions : List (String × (List Value → Option Value))}
    (admitted : PrimitiveContext ⟨functions, primitiveAliases⟩) (index : Nat)
    (meaning : List Value → Option Value) :
    PrimitiveContext ⟨(Function.helperName index, meaning) :: functions, primitiveAliases⟩ := by
  refine ⟨fun alias mem arguments => ?_, fun arguments => ?_⟩
  · rw [Context.call_cons_other (helperName_not_callee index alias.2
      (List.mem_cons_of_mem _ (List.mem_map_of_mem mem)))]
    exact admitted.1 alias mem arguments
  · rw [Context.call_cons_other (helperName_not_callee index "tobool"
      (by simp [primitiveCallees]))]
    exact admitted.2 arguments

theorem CallGraph.emit_success {graph : CheckedWordFunctionDAG} {emitted : EmittedProgram}
    (emitted_eq : CallGraph.emit graph = .ok emitted) :
    ∃ (names lines : List String) (entry : Rendered),
      helperLoop CallGraphRenderer.renderWithFunctions graph.helpers 0 []
        ["import * from std;", "import * from std.dispatch;", Primitive.opcodeImport, ""] =
        .ok (names, lines) ∧
      CallGraphRenderer.renderWithFunctions names .word ["sc_input"] 8 0 graph.entry =
        .ok entry ∧
      emitted.source = String.intercalate "\n" (lines ++
        ["contract " ++ CallGraph.contractName ++ " {",
          "    function " ++ CallGraph.methodName ++
            "(input: uint256) public returns (uint256) {",
          "        let sc_input: word = Typedef.rep(input);"] ++ entry.lines ++
        ["        return uint256(" ++ entry.value ++ ");", "    }", "}"]) ++ "\n" := by
  unfold CallGraph.emit at emitted_eq
  dsimp only at emitted_eq
  rw [forIn_helperLoop (render := CallGraphRenderer.renderWithFunctions) (fun _ _ _ _ => rfl)]
    at emitted_eq
  cases loop : helperLoop CallGraphRenderer.renderWithFunctions graph.helpers 0 []
    ["import * from std;", "import * from std.dispatch;", Primitive.opcodeImport, ""] with
  | error error =>
      rw [loop] at emitted_eq
      cases emitted_eq
  | ok result =>
      obtain ⟨names, lines⟩ := result
      rw [loop] at emitted_eq
      cases entry : CallGraphRenderer.renderWithFunctions names .word ["sc_input"] 8 0
        graph.entry with
      | error error =>
          simp only [bind, Except.bind, entry] at emitted_eq
          cases emitted_eq
      | ok rendered =>
          simp only [bind, Except.bind, entry, pure, Except.pure, Except.ok.injEq] at emitted_eq
          subst emitted_eq
          exact ⟨names, lines, rendered, rfl, entry, rfl⟩

/-- The source file printed by the call-graph emitter. -/
def callGraphFile (declarations : List FunctionDecl) (body : List Stmt) (value : String) :
    SourceFile := {
  opcodeAliases := primitiveAliases
  functions := declarations
  contract := "SynthesizedCallGraphs"
  method := (inputFile body value).method }

/-- **Call-graph emitter preservation.** If the actual emitter succeeds, its
source text is the printing of a file with the raw opcode imports and one free
function per helper, and parses back to it. For every runtime input, calling
`run(uint256)` under the independent source semantics returns exactly the Word
that the original Core binding chain, applied to that input, returns. -/
theorem CallGraph.emit_preserves_meaning {graph : CheckedWordFunctionDAG}
    {emitted : EmittedProgram} (emitted_eq : CallGraph.emit graph = .ok emitted) :
    ∃ file : SourceFile, emitted.source = file.print ∧ parseSource emitted.source = some file ∧
      ∀ input : Solcore.Core.Word, ∃ word : Solcore.Core.Word,
        file.call "run" [input.val] = some word.val ∧
        CoreReturns (graph.instantiate input).toCore word := by
  obtain ⟨names, lines, entry, loop, entryEquation, source⟩ := CallGraph.emit_success emitted_eq
  obtain ⟨declarations, linesEq, namesEq, declarationsOk, admitted, agree⟩ :=
    helperLoop_spec callGraph_render_spec primitiveCallees_ok
      (fun _ index meaning admitted => admitted.extend index meaning) graph.helpers 0 _ names
      lines [] [] loop (helpers_accepted graph.helperScopes) primitiveContext_aliases
      (fun _ _ found => by simp [helperNames] at found)
  have fresh : ∀ name ∈ ["sc_input"], OlderThan 0 name := by
    intro name mem index same
    simp only [List.mem_singleton] at mem
    subst mem
    exact absurd same (input_not_temporary index)
  obtain ⟨statements, entryLines, _, valueName, entryNames, simulates⟩ :=
    callGraph_render_spec graph.entry names 1 graph.helpers.length .word ["sc_input"] 8 0 entry
      graph.entryScope entryEquation fresh
  let file := callGraphFile declarations statements entry.value
  have localsOk : ∀ local_ ∈ ["sc_input"], ValidIdentifier local_ ∧
      isReserved local_ = false := by
    intro local_ mem
    simp only [List.mem_singleton] at mem
    subst mem
    exact ⟨keyword_valid (by decide), by decide⟩
  have functionNamesOk : ∀ name ∈ names, ValidIdentifier name ∧ isReserved name = false := by
    rw [namesEq]
    exact helperNames_ok
  have printed : emitted.source = file.print := by
    have functionLine :
        "    function " ++ CallGraph.methodName ++ "(input: uint256) public returns (uint256) {" =
          "    function " ++ file.method.name ++ "(" ++
            Method.parameterText file.method.parameters ++ ") public returns (uint256) {" := by
      apply String.toList_inj.mp
      simp [file, callGraphFile, inputFile, Method.parameterText, CallGraph.methodName]
    have returnLine : "        return uint256(" ++ entry.value ++ ");" =
        "        return " ++ file.method.result.print ++ ";" := by
      apply String.toList_inj.mp
      simp [file, callGraphFile, inputFile, Expr.print]
    have bodyLines : Stmt.listLines 8 file.method.body =
        "        let sc_input: word = Typedef.rep(input);" :: Stmt.listLines 8 statements :=
      inputFile_body_lines statements entry.value
    rw [source, SourceFile.print, SourceFile.lines, bodyLines, entryLines, linesEq, functionLine,
      returnLine]
    simp [file, callGraphFile, primitiveImportLines, CallGraph.contractName, opcodeImport_eq]
  have valueOk := rendered_name_ok localsOk valueName
  have bodyNames : ∀ name ∈ Stmt.listIdentifiers file.method.body,
      ValidIdentifier name ∧ isReserved name = false := by
    intro name mem
    simp only [file, callGraphFile, inputFile, Stmt.listIdentifiers, Stmt.identifiers,
      Expr.identifiers, List.cons_append, List.nil_append, List.mem_cons] at mem
    rcases mem with rfl | rfl | mem
    · exact ⟨keyword_valid (by decide), by decide⟩
    · exact ⟨keyword_valid (by decide), by decide⟩
    · exact rendered_identifier_ok localsOk functionNamesOk primitiveCallees_ok
        (entryNames name mem)
  have parsed : parseSource emitted.source = some file := by
    rw [printed]
    apply parseSource_print
    · refine ⟨fun declaration mem => (declarationsOk declaration mem).1, rfl, rfl, ?_,
        fun name mem => (bodyNames name mem).2, ?_⟩
      · intro parameter mem
        simp only [file, callGraphFile, inputFile, List.mem_singleton] at mem
        subst mem
        decide
      · intro name mem
        simp only [file, callGraphFile, inputFile, Expr.identifiers, List.mem_singleton] at mem
        subst mem
        exact valueOk.2
    · refine ⟨primitiveAliases_valid, fun declaration mem => (declarationsOk declaration mem).2,
        keyword_valid (show validIdentifier "SynthesizedCallGraphs" = true by decide),
        keyword_valid (show validIdentifier "run" = true by decide), ?_,
        fun name mem => (bodyNames name mem).1, ?_⟩
      · intro parameter mem
        simp only [file, callGraphFile, inputFile, List.mem_singleton] at mem
        subst mem
        exact keyword_valid (by decide)
      · intro name mem
        simp only [file, callGraphFile, inputFile, Expr.identifiers, List.mem_singleton] at mem
        subst mem
        exact valueOk.1
  refine ⟨file, printed, parsed, ?_⟩
  intro input
  have localsAgree : LocalsAgree [[("sc_input", .word input.val)], [("input", .uint256 input.val)]]
      ["sc_input"] (.word input :: graph.helpers.foldl closureStep []) := by
    intro index name found
    cases index with
    | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at found
        subst found
        exact ⟨input, rfl, by simp [Frames.lookup, Scope.get?]⟩
    | succ index => simp at found
  have context : file.context =
      ⟨declareFunctions primitiveAliases [] declarations, primitiveAliases⟩ := rfl
  obtain ⟨core, value, scope', outer', _, evaluates, represents, exec, lookup, _⟩ :=
    simulates file.context (.word input :: graph.helpers.foldl closureStep []) []
      [("sc_input", .word input.val)] [[("input", .uint256 input.val)]] admitted localsAgree
      (by simp) (by rw [context]; simpa using agree)
  obtain ⟨word, rfl, rfl⟩ := represents
  have applied : Solcore.Core.Evaluates [] []
      (graph.instantiate input).toCore.body (.word word) [] := by
    simp only [CheckedWordFunctionDAG.instantiate, CheckedWordFunctionDAG.program,
      Solcore.Synthesis.Core.functionDAGProgram, Solcore.Core.Wire.Program.toCore]
    simp only [Solcore.Core.Wire.Expr.toCore]
    exact .apply (dag_evaluates graph.entry graph.helpers [] []) .word evaluates
  refine ⟨word, ?_, runStateful_of_evaluates applied⟩
  have parameters : Method.bindParameters ["input"] [input.val] =
      some [("input", .uint256 input.val)] := by
    simp [Method.bindParameters, word_lt_modulus]
  have execBody : Stmt.execList file.context [[], [("input", .uint256 input.val)]]
      (.letDecl "sc_input" .word (.typedefRep (.name "input")) :: statements) =
        some (scope' :: outer') := by
    simp only [Stmt.execList, input_declaration]
    exact exec
  simp only [file, callGraphFile, inputFile] at execBody
  simp [file, callGraphFile, inputFile, SourceFile.call, Method.run, parameters, execBody,
    Expr.eval, lookup]

/-- **Call-graph emitter preservation, on the emitted text.** -/
theorem CallGraph.emit_source_meaning {graph : CheckedWordFunctionDAG}
    {emitted : EmittedProgram} (emitted_eq : CallGraph.emit graph = .ok emitted)
    (input : Solcore.Core.Word) :
    ∃ word : Solcore.Core.Word,
      sourceCall emitted.source "run" [input.val] = some word.val ∧
      CoreReturns (graph.instantiate input).toCore word := by
  obtain ⟨file, _, parsed, meaning⟩ := CallGraph.emit_preserves_meaning emitted_eq
  obtain ⟨word, called, core⟩ := meaning input
  exact ⟨word, by simp [sourceCall, parsed, called], core⟩

end Solcore.Synthesis.Source.ScalarMeaning
end

section
-- leanmerge: from Solcore.Synthesis.Source.ScalarMeaning.MutationEmitter
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
end

section
-- leanmerge: from Solcore.Synthesis.Source.ScalarMeaning.AggregateEmitter
/-! Meaning preservation for the actual aggregate emitter (`Aggregate.emit`,
profile `runtime-aggregates`). Helpers become free functions as for the
named-helper emitter. The file imports the fourteen raw `std.opcodes` aliases
only when some rendered body uses one; otherwise no body calls an alias. As for
private mutation, the Core program may end with allocated cells in its store,
so the result is stated for the Word that Core returns with that final store. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.ScalarMeaning

open Solcore.Synthesis.Core.Aggregates (CheckedDAG Local initializerKind? infer?)
open Solcore.Synthesis.Source.AggregateRenderer (Binding)

/-! ### Names -/

theorem payloadTemp_valid (index : Nat) : ValidIdentifier (payloadTemp index) := by
  refine ⟨'s', ['c', '_', 'p'] ++ Nat.toDigits 10 index, by simp [payloadTemp], by decide, ?_⟩
  intro char mem
  rcases List.mem_append.mp mem with prefix_ | digit
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at prefix_
    rcases prefix_ with rfl | rfl | rfl <;> decide
  · exact (digit_classes (toDigits_mem digit)).2.2

theorem payloadTemp_not_reserved (index : Nat) : isReserved (payloadTemp index) = false := by
  have heads : ∀ word ∈ reservedWords, word.toList.head? ≠ some 's' := by decide
  have absent : payloadTemp index ∉ reservedWords := by
    intro mem
    exact heads _ mem (by simp [payloadTemp])
  cases reserved : isReserved (payloadTemp index)
  · rfl
  · exact absurd (List.elem_iff.mp reserved) absent

/-- Every identifier used by rendered aggregate statements is a binding, a
helper, a temporary, a raw opcode alias or `tobool`. -/
theorem aggregate_identifier_ok {bindings : List Binding} {functions : List String}
    {first last : Nat} {name : String}
    (bindingsOk : ∀ index found, anameAt bindings index = some found →
      ValidIdentifier found ∧ isReserved found = false)
    (functionsOk : ∀ function ∈ functions, ValidIdentifier function ∧
      isReserved function = false)
    (classified : AUses bindings functions first last name) :
    ValidIdentifier name ∧ isReserved name = false := by
  rcases classified with ⟨index, named⟩ | mem | ⟨index, same, _, _⟩ | called
  · exact bindingsOk index name named
  · exact functionsOk name mem
  · rcases same with rfl | rfl | rfl
    · exact ⟨temporary_valid index, temporary_not_reserved index⟩
    · exact ⟨cellTemp_valid index, cellTemp_not_reserved index⟩
    · exact ⟨payloadTemp_valid index, payloadTemp_not_reserved index⟩
  · exact primitiveCallees_ok name called

theorem single_abinding_ok {name : String} (valid : ValidIdentifier name)
    (notReserved : isReserved name = false) :
    ∀ index found, anameAt [Binding.word name] index = some found →
      ValidIdentifier found ∧ isReserved found = false := by
  intro index found named
  cases index with
  | zero =>
      rw [anameAt_cons_zero] at named
      cases named
      exact ⟨valid, notReserved⟩
  | succ index => simp [anameAt] at named

theorem single_abinding_fresh {name : String} (notTemp : ∀ index, name ≠ temporary index)
    (notCell : ∀ index, name ≠ cellTemp index) (notPayload : ∀ index, name ≠ payloadTemp index) :
    ANamesFresh [Binding.word name] 0 := by
  intro index found named
  cases index with
  | zero =>
      rw [anameAt_cons_zero] at named
      cases named
      intro position isTemp
      rcases isTemp with same | same | same
      · exact absurd same (notTemp position)
      · exact absurd same (notCell position)
      · exact absurd same (notPayload position)
  | succ index => simp [anameAt] at named

theorem single_abinding_distinct (name : String) : ANamesDistinct [Binding.word name] := by
  intro first second found one two
  cases first with
  | zero =>
      cases second with
      | zero => rfl
      | succ second => simp [anameAt] at two
  | succ first => simp [anameAt] at one

theorem single_abinding_cells (name : String) (core : CoreValue)
    (environment : Solcore.Core.Environment) :
    ACellsDistinct [Binding.word name] (core :: environment) := by
  intro first second location cellOne _
  obtain ⟨⟨_, found⟩, _⟩ := cellOne
  cases first with
  | zero => simp at found
  | succ first => simp at found

theorem single_abinding_agree {name : String} {word : Solcore.Core.Word} {scope : Scope}
    {outer : Frames} (lookup : Frames.lookup (scope :: outer) name = some (.word word.val))
    (environment : Solcore.Core.Environment) (store : Solcore.Core.Store) :
    ABindingsAgree (scope :: outer) [Binding.word name] (.word word :: environment) store := by
  intro index binding found
  cases index with
  | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at found
      subst found
      exact ⟨.word word, rfl, .word word.val, lookup, word, rfl, rfl⟩
  | succ index => simp at found

theorem payloadTemp_ne_input (index : Nat) : "sc_input" ≠ payloadTemp index := by
  intro same
  have chars := congrArg String.toList same
  simp [payloadTemp] at chars

theorem payloadTemp_ne_argument (index : Nat) : "sc_arg" ≠ payloadTemp index := by
  intro same
  have chars := congrArg String.toList same
  simp [payloadTemp] at chars

/-! ### Raw opcode aliases -/

theorem aggregateImport_eq :
    "import { " ++ ", ".intercalate AggregateRenderer.opcodeAliases ++ " } from std.opcodes;" =
      aliasImportLine primitiveAliases := by
  decide +kernel

/-- The aliases the aggregate file imports: all fourteen if a rendered body
uses one, otherwise none. -/
def aggregateAliases (bodies : List CoreExpr) : List (String × String) :=
  if bodies.any AggregateRenderer.usesOpcodeAliases then primitiveAliases else []

theorem opcodeImports_eq (bodies : List CoreExpr) :
    AggregateRenderer.opcodeImports bodies = aliasImportLines (aggregateAliases bodies) := by
  unfold AggregateRenderer.opcodeImports aggregateAliases
  split
  · rw [aggregateImport_eq]
    rfl
  · rfl

theorem aggregateAliases_valid (bodies : List CoreExpr) :
    ∀ alias ∈ aggregateAliases bodies, ValidIdentifier alias.1 ∧ ValidIdentifier alias.2 := by
  unfold aggregateAliases
  split
  · exact primitiveAliases_valid
  · intro _ absent
    cases absent

/-- Declaring a helper keeps the aliases and `tobool` reachable. -/
theorem PrimitiveContext.extendWith {functions : List (String × (List Value → Option Value))}
    {aliases : List (String × String)} {uses : Bool}
    (aliasesOk : uses = true → aliases = primitiveAliases)
    (admitted : uses = true → PrimitiveContext ⟨functions, aliases⟩) (index : Nat)
    (meaning : List Value → Option Value) :
    uses = true →
      PrimitiveContext ⟨(Function.helperName index, meaning) :: functions, aliases⟩ := by
  intro used
  have same := aliasesOk used
  subst same
  exact (admitted used).extend index meaning

/-! ### The emitter's helper loop -/

/-- The helper loop of `Aggregate.emit`, by structural recursion. -/
def aggregateLoop : List CoreExpr → Nat → List String → List String →
    Except EmitError (List String × List String)
  | [], _, names, lines => .ok (names, lines)
  | body :: rest, index, names, lines =>
      (AggregateRenderer.render names .word [.word "sc_arg"] 4 0 body).bind fun rendered =>
        (AggregateRenderer.requireValue rendered).bind fun result =>
          aggregateLoop rest (index + 1) (Function.helperName index :: names)
            (lines ++
              ["function " ++ Function.helperName index ++ "(sc_arg: word) returns (word) {"] ++
              rendered.lines ++ ["    return " ++ result ++ ";", "}", ""])

theorem forIn_aggregateLoop
    {step : CoreExpr × Nat → List String × List String →
      Except EmitError (ForInStep (List String × List String))}
    (stepEq : ∀ body index names lines, step (body, index) (names, lines) =
      (AggregateRenderer.render names .word [.word "sc_arg"] 4 0 body).bind fun rendered =>
        (AggregateRenderer.requireValue rendered).bind fun result =>
          .ok (.yield (Function.helperName index :: names,
            lines ++
              ["function " ++ Function.helperName index ++ "(sc_arg: word) returns (word) {"] ++
              rendered.lines ++ ["    return " ++ result ++ ";", "}", ""]))) :
    ∀ (bodies : List CoreExpr) (start : Nat) (names lines : List String),
      forIn (bodies.zipIdx start) (names, lines) step = aggregateLoop bodies start names lines
  | [], _, _, _ => rfl
  | body :: rest, start, names, lines => by
      rw [List.zipIdx_cons, List.forIn_cons, stepEq, aggregateLoop]
      cases AggregateRenderer.render names .word [.word "sc_arg"] 4 0 body with
      | error error => rfl
      | ok rendered =>
          simp only [Except.bind]
          cases AggregateRenderer.requireValue rendered with
          | error error => rfl
          | ok result => exact forIn_aggregateLoop stepEq rest (start + 1) _ _

theorem Aggregate.emit_success {graph : CheckedDAG} {emitted : EmittedProgram}
    (emitted_eq : Aggregate.emit graph = .ok emitted) :
    ∃ (names lines : List String) (entry : ARendered) (result : String),
      aggregateLoop graph.helpers 0 []
        (["import * from std;", "import * from std.dispatch;"] ++
          aliasImportLines (aggregateAliases (graph.helpers ++ [graph.entry])) ++ [""]) =
        .ok (names, lines) ∧
      AggregateRenderer.render names .word [.word "sc_input"] 8 0 graph.entry = .ok entry ∧
      entry.value = some result ∧
      emitted.source = String.intercalate "\n" (lines ++
        ["contract " ++ Aggregate.contractName ++ " {",
          "    function " ++ Aggregate.methodName ++ "(input: uint256) public returns (uint256) {",
          "        let sc_input: word = Typedef.rep(input);"] ++ entry.lines ++
        ["        return uint256(" ++ result ++ ");", "    }", "}"]) ++ "\n" := by
  unfold Aggregate.emit at emitted_eq
  dsimp only at emitted_eq
  rw [forIn_aggregateLoop (fun _ _ _ _ => rfl), opcodeImports_eq] at emitted_eq
  cases loop : aggregateLoop graph.helpers 0 []
    (["import * from std;", "import * from std.dispatch;"] ++
      aliasImportLines (aggregateAliases (graph.helpers ++ [graph.entry])) ++ [""]) with
  | error error =>
      rw [loop] at emitted_eq
      cases emitted_eq
  | ok loopResult =>
      obtain ⟨names, lines⟩ := loopResult
      rw [loop] at emitted_eq
      cases entry : AggregateRenderer.render names .word [.word "sc_input"] 8 0 graph.entry with
      | error error =>
          simp only [bind, Except.bind, entry] at emitted_eq
          cases emitted_eq
      | ok rendered =>
          simp only [bind, Except.bind, entry] at emitted_eq
          cases value : AggregateRenderer.requireValue rendered with
          | error error =>
              simp only [value] at emitted_eq
              cases emitted_eq
          | ok result =>
              simp only [value, pure, Except.pure, Except.ok.injEq] at emitted_eq
              subst emitted_eq
              exact ⟨names, lines, rendered, result, rfl, entry, arequireValue_ok value, rfl⟩

theorem aggregate_acceptsAt_kind {locals : List Local} {prior : Nat} {target : ATarget}
    {expression : CoreExpr}
    (accepted : Solcore.Synthesis.Core.Aggregates.acceptsAt locals prior target expression =
      true) :
    initializerKind? locals prior expression = some target.toLocal := by
  unfold Solcore.Synthesis.Core.Aggregates.acceptsAt at accepted
  cases inferred : infer? locals prior expression with
  | none =>
      rw [inferred] at accepted
      cases accepted
  | some found =>
      rw [inferred] at accepted
      have same : found = target := by
        cases found <;> cases target <;> first | rfl | cases accepted
      subst same
      exact AggregateKinds.infer_toLocal inferred

theorem aggregate_helpers_accepted {helpers : List CoreExpr}
    (accepted : Solcore.Synthesis.Core.Aggregates.helpersAccepted helpers = true) :
    ∀ (index : Nat) (body : CoreExpr), helpers[index]? = some body →
      Solcore.Synthesis.Core.Aggregates.acceptsAt [.word] (0 + index) .word body = true := by
  intro index body found
  have all := List.all_eq_true.mp accepted (body, index)
    (List.mem_zipIdx_iff_getElem?.mpr found)
  simpa using all

/-- The helper loop prints free functions whose meanings agree with the Core
closures of the binding chain, and whose evaluation keeps the caller's store.
When some body uses a raw alias, the file imports all of them and every helper
body runs in a context in which they reach their opcodes. -/
theorem aggregateLoop_spec {aliases : List (String × String)} {uses : Bool}
    (aliasesOk : uses = true → aliases = primitiveAliases) :
    ∀ (bodies : List CoreExpr) (start : Nat) (lines names' lines' : List String)
      (functions : List (String × (List Value → Option Value))) (closures : List CoreValue),
    aggregateLoop bodies start (helperNames start) lines = .ok (names', lines') →
    (∀ (index : Nat) (body : CoreExpr), bodies[index]? = some body →
      Solcore.Synthesis.Core.Aggregates.acceptsAt [.word] (start + index) .word body = true ∧
        (AggregateRenderer.usesOpcodeAliases body = true → uses = true)) →
    (uses = true → PrimitiveContext ⟨functions, aliases⟩) →
    MFunctionsAgree ⟨functions, aliases⟩ (helperNames start) closures →
    ∃ declarations : List FunctionDecl,
      lines' = lines ++ declarations.flatMap FunctionDecl.lines ∧
      names' = helperNames (start + bodies.length) ∧
      (∀ declaration ∈ declarations, declaration.NamesOk ∧
        ∀ name ∈ declaration.identifiers, ValidIdentifier name) ∧
      (uses = true →
        PrimitiveContext ⟨declareFunctions aliases functions declarations, aliases⟩) ∧
      MFunctionsAgree ⟨declareFunctions aliases functions declarations, aliases⟩ names'
        (bodies.foldl closureStep closures)
  | [], start, lines, names', lines', functions, closures, loop, _, primitive, agree => by
      simp only [aggregateLoop, Except.ok.injEq, Prod.mk.injEq] at loop
      obtain ⟨rfl, rfl⟩ := loop
      exact ⟨[], by simp, by simp, by simp, by simpa [declareFunctions] using primitive,
        by simpa [declareFunctions] using agree⟩
  | body :: rest, start, lines, names', lines', functions, closures, loop, accepted, primitive,
      agree => by
      simp only [aggregateLoop] at loop
      obtain ⟨rendered, renderedEquation, loop⟩ := except_bind_eq_ok loop
      obtain ⟨result, resultEquation, loop⟩ := except_bind_eq_ok loop
      have resultFound := arequireValue_ok resultEquation
      obtain ⟨bodyAccepted, bodyUses⟩ := accepted 0 body rfl
      have bodyKind : initializerKind? ([Binding.word "sc_arg"].map Binding.kind)
          (helperNames start).length body = some Local.word := by
        rw [helperNames_length]
        exact aggregate_acceptsAt_kind bodyAccepted
      obtain ⟨statements, lines₁, _, valueName, names, simulates⟩ :=
        (aggregate_render_spec body).1 (fun context => uses = true → PrimitiveContext context)
          (fun context admitted used => admitted (bodyUses used)) (helperNames start) .word
          [.word "sc_arg"] 4 0 rendered bodyKind renderedEquation
          (single_abinding_fresh argument_not_temporary cellTemp_ne_argument
            payloadTemp_ne_argument)
          (single_abinding_distinct _)
      let declaration := helperDecl start statements result
      have behaves : ∀ (argument : Solcore.Core.Word) (store : Solcore.Core.Store),
          ∃ (value : Solcore.Core.Word) (store' : Solcore.Core.Store),
            Solcore.Core.Evaluates (.word argument :: closures) store body.toCore
              (.word value) store' ∧
            store.length ≤ store'.length ∧
            (∀ location, location < store.length →
              store'.read? location = store.read? location) ∧
            declaration.denote ⟨functions, aliases⟩ [.word argument.val] =
              some (.word value.val) := by
        intro argument store
        obtain ⟨core, store', scope', outer', _, evaluates, represents, exec, _, frame, _⟩ :=
          simulates ⟨functions, aliases⟩ (.word argument :: closures) store []
            [[("sc_arg", .word argument.val)]] primitive
            (single_abinding_agree (by simp [Frames.lookup, Scope.get?]) closures store)
            (single_abinding_cells _ _ _) (by simp) (by simpa using agree)
        rw [resultFound, Option.bind_some] at represents
        obtain ⟨_, lookup, value, rfl, rfl⟩ := represents
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
      have extendedPrimitive := PrimitiveContext.extendWith aliasesOk primitive start
        (declaration.denote ⟨functions, aliases⟩)
      have restAccepted : ∀ (index : Nat) (body : CoreExpr), rest[index]? = some body →
          Solcore.Synthesis.Core.Aggregates.acceptsAt [.word] (start + 1 + index) .word body =
            true ∧ (AggregateRenderer.usesOpcodeAliases body = true → uses = true) := by
        intro index body found
        have accepted' := accepted (index + 1) body (by simpa using found)
        rwa [show start + (index + 1) = start + 1 + index by omega] at accepted'
      obtain ⟨declarations, rest₁, rest₂, rest₃, rest₄, rest₅⟩ :=
        aggregateLoop_spec aliasesOk rest (start + 1) _ names' lines' _ _ loop restAccepted
          extendedPrimitive extended
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
      have argumentOk : ∀ index found, anameAt [Binding.word "sc_arg"] index = some found →
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

/-- The source file printed by the aggregate emitter. -/
def aggregateFile (aliases : List (String × String)) (declarations : List FunctionDecl)
    (body : List Stmt) (value : String) : SourceFile := {
  opcodeAliases := aliases
  functions := declarations
  contract := "SynthesizedAggregates"
  method := (inputFile body value).method }

/-- **Aggregate emitter preservation.** If the actual emitter succeeds, its
source text is the printing of a file with one free function per helper and
parses back to it. For every runtime input, calling `run(uint256)` under the
independent source semantics returns exactly the Word that the original Core
binding chain, applied to that input, returns, through Word pairs and sums,
their matches and projections, private Word cells, helper calls and raw opcode
aliases. -/
theorem Aggregate.emit_preserves_meaning {graph : CheckedDAG}
    {emitted : EmittedProgram} (emitted_eq : Aggregate.emit graph = .ok emitted) :
    ∃ file : SourceFile, emitted.source = file.print ∧ parseSource emitted.source = some file ∧
      ∀ input : Solcore.Core.Word, ∃ word : Solcore.Core.Word,
        file.call "run" [input.val] = some word.val ∧
        CoreReturnsWithStore (graph.instantiate input).toCore word := by
  obtain ⟨names, lines, entry, result, loop, entryEquation, resultFound, source⟩ :=
    Aggregate.emit_success emitted_eq
  let bodies := graph.helpers ++ [graph.entry]
  let uses := bodies.any AggregateRenderer.usesOpcodeAliases
  have aliasesOk : uses = true → aggregateAliases bodies = primitiveAliases := by
    intro used
    simp only [aggregateAliases]
    rw [if_pos used]
  have bodyUses : ∀ body ∈ bodies, AggregateRenderer.usesOpcodeAliases body = true →
      uses = true := fun body mem used => List.any_eq_true.mpr ⟨body, mem, used⟩
  have startPrimitive : uses = true → PrimitiveContext ⟨[], aggregateAliases bodies⟩ := by
    intro used
    rw [aliasesOk used]
    exact primitiveContext_aliases
  obtain ⟨declarations, linesEq, namesEq, declarationsOk, primitive, agree⟩ :=
    aggregateLoop_spec aliasesOk graph.helpers 0 _ names lines [] [] loop
      (fun index body found => ⟨aggregate_helpers_accepted graph.helperScopes index body found,
        bodyUses body (List.mem_append_left _ (List.mem_of_getElem? found))⟩)
      startPrimitive (fun _ _ found => by simp [helperNames] at found)
  have entryKind : initializerKind? ([Binding.word "sc_input"].map Binding.kind) names.length
      graph.entry = some Local.word := by
    rw [namesEq, helperNames_length, Nat.zero_add]
    exact aggregate_acceptsAt_kind graph.entryScope
  obtain ⟨statements, entryLines, _, valueName, entryNames, simulates⟩ :=
    (aggregate_render_spec graph.entry).1 (fun context => uses = true → PrimitiveContext context)
      (fun context admitted used =>
        admitted (bodyUses graph.entry (List.mem_append_right _ (by simp)) used))
      names .word [.word "sc_input"] 8 0 entry entryKind entryEquation
      (single_abinding_fresh input_not_temporary cellTemp_ne_input payloadTemp_ne_input)
      (single_abinding_distinct _)
  let file := aggregateFile (aggregateAliases bodies) declarations statements result
  have inputOk : ∀ index found, anameAt [Binding.word "sc_input"] index = some found →
      ValidIdentifier found ∧ isReserved found = false :=
    single_abinding_ok (keyword_valid (by decide)) (by decide)
  have functionNamesOk : ∀ name ∈ names, ValidIdentifier name ∧ isReserved name = false := by
    rw [namesEq]
    exact helperNames_ok
  have printed : emitted.source = file.print := by
    have functionLine :
        "    function " ++ Aggregate.methodName ++ "(input: uint256) public returns (uint256) {" =
          "    function " ++ file.method.name ++ "(" ++
            Method.parameterText file.method.parameters ++ ") public returns (uint256) {" := by
      apply String.toList_inj.mp
      simp [file, aggregateFile, inputFile, Method.parameterText, Aggregate.methodName]
    have returnLine : "        return uint256(" ++ result ++ ");" =
        "        return " ++ file.method.result.print ++ ";" := by
      apply String.toList_inj.mp
      simp [file, aggregateFile, inputFile, Expr.print]
    have bodyLines : Stmt.listLines 8 file.method.body =
        "        let sc_input: word = Typedef.rep(input);" :: Stmt.listLines 8 statements :=
      inputFile_body_lines statements result
    rw [source, SourceFile.print, SourceFile.lines, bodyLines, entryLines, linesEq, functionLine,
      returnLine]
    simp [file, aggregateFile, Aggregate.contractName, bodies]
  have valueOk := aggregate_identifier_ok inputOk functionNamesOk
    (valueName result resultFound).uses
  have bodyNames : ∀ name ∈ Stmt.listIdentifiers file.method.body,
      ValidIdentifier name ∧ isReserved name = false := by
    intro name mem
    simp only [file, aggregateFile, inputFile, Stmt.listIdentifiers, Stmt.identifiers,
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
        simp only [file, aggregateFile, inputFile, List.mem_singleton] at mem
        subst mem
        decide
      · intro name mem
        simp only [file, aggregateFile, inputFile, Expr.identifiers, List.mem_singleton] at mem
        subst mem
        exact valueOk.2
    · refine ⟨aggregateAliases_valid bodies,
        fun declaration mem => (declarationsOk declaration mem).2,
        keyword_valid (show validIdentifier "SynthesizedAggregates" = true by decide),
        keyword_valid (show validIdentifier "run" = true by decide), ?_,
        fun name mem => (bodyNames name mem).1, ?_⟩
      · intro parameter mem
        simp only [file, aggregateFile, inputFile, List.mem_singleton] at mem
        subst mem
        exact keyword_valid (by decide)
      · intro name mem
        simp only [file, aggregateFile, inputFile, Expr.identifiers, List.mem_singleton] at mem
        subst mem
        exact valueOk.1
  refine ⟨file, printed, parsed, ?_⟩
  intro input
  have context : file.context =
      ⟨declareFunctions (aggregateAliases bodies) [] declarations, aggregateAliases bodies⟩ :=
    rfl
  obtain ⟨core, store', scope', outer', _, evaluates, represents, exec, _⟩ :=
    simulates file.context (.word input :: graph.helpers.foldl closureStep []) []
      [("sc_input", .word input.val)] [[("input", .uint256 input.val)]]
      (by rw [context]; exact primitive)
      (single_abinding_agree (by simp [Frames.lookup, Scope.get?]) _ _)
      (single_abinding_cells _ _ _) (by simp) (by rw [context]; simpa using agree)
  rw [resultFound, Option.bind_some] at represents
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
  simp only [file, aggregateFile, inputFile] at execBody
  simp [file, aggregateFile, inputFile, SourceFile.call, Method.run, parameters, execBody,
    Expr.eval, lookup]

/-- **Aggregate emitter preservation, on the emitted text.** -/
theorem Aggregate.emit_source_meaning {graph : CheckedDAG}
    {emitted : EmittedProgram} (emitted_eq : Aggregate.emit graph = .ok emitted)
    (input : Solcore.Core.Word) :
    ∃ word : Solcore.Core.Word,
      sourceCall emitted.source "run" [input.val] = some word.val ∧
      CoreReturnsWithStore (graph.instantiate input).toCore word := by
  obtain ⟨file, _, parsed, meaning⟩ := Aggregate.emit_preserves_meaning emitted_eq
  obtain ⟨word, called, core⟩ := meaning input
  exact ⟨word, by simp [sourceCall, parsed, called], core⟩

end Solcore.Synthesis.Source.ScalarMeaning
end

section
-- leanmerge: from Solcore.Synthesis.Source.ScalarMeaning.AggregateCallGraphEmitter
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
end
