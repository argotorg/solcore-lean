import Solcore.Synthesis.Source.CallGraphEmitter
import Solcore.Synthesis.Source.ScalarMeaning.CallGraphPreservation
import Solcore.Synthesis.Source.ScalarMeaning.FunctionEmitter
import Solcore.Synthesis.Source.ScalarMeaning.PrimitiveEmitter

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
