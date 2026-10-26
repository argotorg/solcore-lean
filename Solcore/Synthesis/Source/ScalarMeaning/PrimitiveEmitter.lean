import Solcore.Synthesis.Source.PrimitiveEmitter
import Solcore.Synthesis.Source.ScalarMeaning.Emitter
import Solcore.Synthesis.Source.ScalarMeaning.PrimitivePreservation

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
