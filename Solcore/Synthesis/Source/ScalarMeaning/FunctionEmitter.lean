import Solcore.Synthesis.Source.FunctionEmitter
import Solcore.Synthesis.Source.ScalarMeaning.Emitter

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
