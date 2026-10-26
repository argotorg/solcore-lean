import Solcore.Synthesis.Source.AggregateEmitter
import Solcore.Synthesis.Source.ScalarMeaning.AggregateControl
import Solcore.Synthesis.Source.ScalarMeaning.CallGraphEmitter
import Solcore.Synthesis.Source.ScalarMeaning.MutationEmitter

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
