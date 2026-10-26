import Solcore.Synthesis.Source.LoopEmitter
import Solcore.Synthesis.Source.ScalarMeaning.AggregateEmitter
import Solcore.Synthesis.Source.ScalarMeaning.CallGraphLoopEmitter

/-! Meaning preservation for the actual aggregate loop emitter (`Loop.emit`,
profile `runtime-loops`). The helpers are free functions as for the aggregate
emitter, the entry becomes the free function `sc_step` as for the call-graph
loop emitter, and the method is the same bounded `while` wrapper. Unlike a
scalar step, an aggregate step may allocate private cells. Core keeps them in
its store, which therefore grows from one iteration to the next, while the
accumulator cell keeps its location and every earlier cell keeps its value.
The result is stated with the final store. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.ScalarMeaning

open Solcore.Synthesis.Core.BoundedLoop (CheckedPlan)
open Solcore.Synthesis.Core.Aggregates (Local initializerKind?)
open Solcore.Synthesis.Source.AggregateRenderer (Binding)

/-! ### The emitted text -/

theorem Loop.emit_success {plan : CheckedPlan} {emitted : EmittedProgram}
    (emitted_eq : Loop.emit plan = .ok emitted) :
    ∃ (names lines : List String) (entry : ARendered) (result : String),
      aggregateLoop plan.step.helpers 0 []
        (["import * from std;", "import * from std.dispatch;"] ++
          aliasImportLines (aggregateAliases (plan.step.helpers ++ [plan.step.entry])) ++
          [""]) = .ok (names, lines) ∧
      AggregateRenderer.render names .word [.word "sc_arg"] 4 0 plan.step.entry = .ok entry ∧
      entry.value = some result ∧
      emitted.source = String.intercalate "\n" (lines ++
        ["function sc_step(sc_arg: word) returns (word) {"] ++ entry.lines ++
        ["    return " ++ result ++ ";", "}", "",
          "contract " ++ Loop.contractName ++ " {",
          "    function " ++ Loop.methodName ++ "(input: uint256) public returns (uint256) {",
          "        let sc_input: word = Typedef.rep(input);",
          "        let sc_limit: word = (sc_input & " ++ toString plan.mask ++ ");",
          "        let sc_acc: word = sc_input;",
          "        let sc_counter: word = 0;",
          "        while (sc_limit > sc_counter) {",
          "            sc_acc = sc_step(sc_acc);",
          "            sc_counter = (sc_counter + 1);",
          "        }",
          "        return uint256(sc_acc);", "    }", "}"]) ++ "\n" := by
  unfold Loop.emit at emitted_eq
  dsimp only at emitted_eq
  rw [forIn_aggregateLoop (fun _ _ _ _ => rfl), opcodeImports_eq] at emitted_eq
  cases loop : aggregateLoop plan.step.helpers 0 []
    (["import * from std;", "import * from std.dispatch;"] ++
      aliasImportLines (aggregateAliases (plan.step.helpers ++ [plan.step.entry])) ++ [""]) with
  | error error =>
      rw [loop] at emitted_eq
      cases emitted_eq
  | ok loopResult =>
      obtain ⟨names, lines⟩ := loopResult
      rw [loop] at emitted_eq
      cases entry : AggregateRenderer.render names .word [.word "sc_arg"] 4 0
        plan.step.entry with
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

/-- The loop file printed by the aggregate loop emitter. -/
def aggregateLoopFile (aliases : List (String × String)) (declarations : List FunctionDecl)
    (statements : List Stmt) (value : String) (mask : Nat) : LoopFile where
  opcodeAliases := aliases
  functions := declarations ++ [stepDecl statements value]
  contract := "SynthesizedLoops"
  method := {
    name := "run"
    parameters := ["input"]
    body := boundedBody mask
    result := .uint256 (.name "sc_acc") }

/-! ### The Core bounded loop with a growing store -/

/-- Every admitted mask is at most seven. -/
theorem loopPlan_mask_le (plan : CheckedPlan) : plan.mask ≤ 7 := by
  rcases plan.allowed with same | same | same | same <;> rw [same] <;> decide

/-- From the bound on, a guard skips the step and keeps the store, in which the
accumulator cell is the first location. -/
theorem guards_skip_store {closure : CoreValue} {input bound accumulator : Solcore.Core.Word} :
    ∀ (remaining ordinal : Nat) (store : Solcore.Core.Store), bound.val ≤ ordinal →
      ordinal + remaining < 2 ^ 256 → store.read? 0 = some (.word accumulator) →
      Solcore.Core.Evaluates (guardEnvironment closure input bound ordinal) store
        (loopGuards remaining ordinal).toCore (.word accumulator) store
  | 0, ordinal, _, _, _, held => by
      simp only [loopGuards, Solcore.Core.Wire.Expr.toCore]
      exact .loadCell (.var (guardEnvironment_cell closure input bound ordinal)) held
  | remaining + 1, ordinal, store, past, small, held => by
      simp only [loopGuards, Solcore.Core.Wire.Expr.toCore, Solcore.Core.Wire.BinaryOp.toCore]
      have notGreater : ¬ bound > Solcore.Core.Word.ofNatModulo ordinal := by
        show ¬ (Solcore.Core.Word.ofNatModulo ordinal).val < bound.val
        rw [ofNatModulo_val_small (by omega)]
        omega
      refine .letE (.ifFalse (Solcore.Core.Evaluates.wordGt_not_gt notGreater
        (.var (guardEnvironment_bound closure input bound ordinal)) .word) .unit) ?_
      rw [guardEnvironment_succ]
      exact guards_skip_store remaining (ordinal + 1) store (by omega) (by omega) held

theorem store_read_zero_length {store : Solcore.Core.Store} {value : CoreValue}
    (held : store.read? 0 = some value) : 0 < store.length := by
  cases store with
  | nil => simp [Solcore.Core.Store.read?] at held
  | cons first rest => simp

/-- From an ordinal `count` steps before the bound, the Core guards and the
source loop both apply the step `count` times. A step may append cells to the
store but keeps every existing location, so the accumulator stays in the first
location. -/
theorem storeLoop_agrees {context : Context} {closures : List CoreValue} {entry : CoreExpr}
    (behaves : ∀ (argument : Solcore.Core.Word) (store : Solcore.Core.Store),
      ∃ (result : Solcore.Core.Word) (store' : Solcore.Core.Store),
        Solcore.Core.Evaluates (.word argument :: closures) store entry.toCore (.word result)
          store' ∧
        store.length ≤ store'.length ∧
        (∀ location, location < store.length → store'.read? location = store.read? location) ∧
        context.call "sc_step" [.word argument.val] = some (.word result.val))
    (input bound : Solcore.Core.Word) {mask : Nat} (bounded : bound.val ≤ mask)
    (small : mask < 2 ^ 255) :
    ∀ (count ordinal remaining : Nat) (accumulator : Solcore.Core.Word)
      (store : Solcore.Core.Store),
      ordinal + count = bound.val → ordinal + remaining = mask →
      store.read? 0 = some (.word accumulator) →
      ∃ (final : Solcore.Core.Word) (store' : Solcore.Core.Store),
        Solcore.Core.Evaluates
          (guardEnvironment (.closure (Solcore.Core.Wire.Ty.toCore .word)
            (Solcore.Core.Wire.Ty.toCore .word) entry.toCore closures) input bound ordinal)
          store (loopGuards remaining ordinal).toCore (.word final) store' ∧
        ∀ fuel, count < fuel →
          runWhile context boundedCondition boundedStep fuel
            (loopFrames input.val bound.val ordinal accumulator.val) =
            some (loopFrames input.val bound.val bound.val final.val)
  | 0, ordinal, remaining, accumulator, store, reached, total, held => by
      refine ⟨accumulator, store,
        guards_skip_store remaining ordinal store (by omega) (by omega) held, ?_⟩
      intro fuel enough
      obtain ⟨fuel, rfl⟩ : ∃ rest, fuel = rest + 1 := ⟨fuel - 1, by omega⟩
      have same : ordinal = bound.val := by omega
      rw [same]
      simp [runWhile, boundedCondition_eval]
  | count + 1, ordinal, remaining, accumulator, store, reached, total, held => by
      obtain ⟨rest, rfl⟩ : ∃ rest, remaining = rest + 1 := ⟨remaining - 1, by omega⟩
      obtain ⟨next, stepped, stepCore, longer, kept, stepSource⟩ := behaves accumulator store
      have nonempty := store_read_zero_length held
      have positive : 0 < stepped.length := by omega
      have written : stepped.write? 0 (.word next) = some (stepped.set 0 (.word next)) := by
        simp [Solcore.Core.Store.write?, positive]
      have heldNext : Solcore.Core.Store.read? (stepped.set 0 (.word next)) 0 =
          some (.word next) := by
        simp [Solcore.Core.Store.read?, positive]
      obtain ⟨final, finalStore, guardsRest, loopRest⟩ :=
        storeLoop_agrees behaves input bound bounded small count (ordinal + 1) rest next
          (stepped.set 0 (.word next)) (by omega) (by omega) heldNext
      refine ⟨final, finalStore, ?_, ?_⟩
      · simp only [loopGuards, Solcore.Core.Wire.Expr.toCore, Solcore.Core.Wire.BinaryOp.toCore]
        have greater : bound > Solcore.Core.Word.ofNatModulo ordinal := by
          show (Solcore.Core.Word.ofNatModulo ordinal).val < bound.val
          rw [ofNatModulo_val_small (by omega)]
          omega
        refine .letE (.ifTrue (Solcore.Core.Evaluates.wordGt_gt greater
          (.var (guardEnvironment_bound _ input bound ordinal)) .word)
          (.storeCell (.var (guardEnvironment_cell _ input bound ordinal)) held
            (.apply (.var (guardEnvironment_closure _ input bound ordinal))
              (.loadCell (.var (guardEnvironment_cell _ input bound ordinal)) held) stepCore)
            written)) ?_
        rw [guardEnvironment_succ]
        exact guardsRest
      · intro fuel enough
        obtain ⟨fuel, rfl⟩ : ∃ rest, fuel = rest + 1 := ⟨fuel - 1, by omega⟩
        have below : ordinal < bound.val := by omega
        have counted : ordinal + 1 < Evm.modulus := by
          simp only [Evm.modulus]
          omega
        simp only [runWhile, boundedCondition_eval, below, decide_true,
          boundedStep_exec stepSource counted]
        exact loopRest fuel (by omega)

/-- The applied Core reference returns the accumulator after the step was
applied `input & mask` times, as the source loop does, with some final store. -/
theorem storeLoop_meaning {context : Context} {plan : CheckedPlan}
    (behaves : ∀ (argument : Solcore.Core.Word) (store : Solcore.Core.Store),
      ∃ (result : Solcore.Core.Word) (store' : Solcore.Core.Store),
        Solcore.Core.Evaluates (.word argument :: plan.step.helpers.foldl closureStep [])
          store plan.step.entry.toCore (.word result) store' ∧
        store.length ≤ store'.length ∧
        (∀ location, location < store.length → store'.read? location = store.read? location) ∧
        context.call "sc_step" [.word argument.val] = some (.word result.val))
    (input : Solcore.Core.Word) :
    ∃ (final : Solcore.Core.Word) (store : Solcore.Core.Store),
      Solcore.Core.Evaluates [] [] (plan.instantiate input).toCore.body (.word final) store ∧
      ∀ fuel, plan.mask < fuel →
        runWhile context boundedCondition boundedStep fuel
          (loopFrames input.val (Evm.and input.val plan.mask) 0 input.val) =
          some (loopFrames input.val (Evm.and input.val plan.mask)
            (Evm.and input.val plan.mask) final.val) := by
  have masked := loopPlan_mask_le plan
  let maskWord := Solcore.Core.Word.ofNatModulo plan.mask
  let bound := input.bitAnd maskWord
  have maskVal : maskWord.val = plan.mask := ofNatModulo_val_small (by omega)
  have boundVal : bound.val = Evm.and input.val plan.mask := by
    rw [← maskVal]
    exact (evm_and input maskWord).symm
  have bounded : bound.val ≤ plan.mask := by
    rw [boundVal]
    exact Nat.and_le_right
  obtain ⟨final, store, guards, loop⟩ := storeLoop_agrees behaves input bound bounded
    (by omega) bound.val 0 plan.mask input [.word input] (by omega) (by omega) rfl
  refine ⟨final, store, ?_, ?_⟩
  · have body : (plan.instantiate input).toCore.body = Solcore.Core.Wire.Expr.toCore
        (.apply (.letE (Solcore.Synthesis.Core.functionDAGExpression plan.step.helpers
          plan.step.entry) (.lambda .word .word
            (.letE (.binary .wordAnd (.var 0) (.word maskWord))
              (.letE (.newCell .word (.var 1)) (loopGuards plan.mask 0))))) (.word input)) := by
      show (Solcore.Synthesis.Core.BoundedLoop.appliedProgram plan.step plan.mask
        input).body.toCore = _
      rw [appliedProgram_body plan.allowed]
      rfl
    rw [body]
    simp only [Solcore.Core.Wire.Expr.toCore, Solcore.Core.Wire.BinaryOp.toCore]
    exact .apply (.letE (dag_evaluates plan.step.entry plan.step.helpers [] []) .lambda) .word
      (.letE (Solcore.Core.Evaluates.wordAnd (.var rfl) .word) (.letE (.newCell (.var rfl)) guards))
  · intro fuel enough
    rw [← boundVal]
    exact loop fuel (by omega)

/-! ### Preservation -/

/-- **Aggregate loop emitter preservation.** If the actual emitter succeeds, its
source text is the printing of a loop file with one free function per helper
and the step function `sc_step`, importing the raw opcode aliases exactly when
a rendered body uses one, and parses back to it. For every runtime input,
calling `run(uint256)` under the fuel-indexed source semantics, with fuel above
the mask, returns exactly the Word that the original Core bounded loop, applied
to that input, returns with its final store. -/
theorem Loop.emit_preserves_meaning {plan : CheckedPlan} {emitted : EmittedProgram}
    (emitted_eq : Loop.emit plan = .ok emitted) :
    ∃ file : LoopFile, emitted.source = file.print ∧
      parseLoopSource emitted.source = some file ∧
      ∀ input : Solcore.Core.Word, ∃ word : Solcore.Core.Word,
        (∀ fuel, plan.mask < fuel → file.call fuel "run" [input.val] = some word.val) ∧
        CoreReturnsWithStore (plan.instantiate input).toCore word := by
  obtain ⟨names, lines, entry, result, loop, entryEquation, resultFound, source⟩ :=
    Loop.emit_success emitted_eq
  let bodies := plan.step.helpers ++ [plan.step.entry]
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
    aggregateLoop_spec aliasesOk plan.step.helpers 0 _ names lines [] [] loop
      (fun index body found =>
        ⟨aggregate_helpers_accepted plan.step.helperScopes index body found,
          bodyUses body (List.mem_append_left _ (List.mem_of_getElem? found))⟩)
      startPrimitive (fun _ _ found => by simp [helperNames] at found)
  have entryKind : initializerKind? ([Binding.word "sc_arg"].map Binding.kind) names.length
      plan.step.entry = some Local.word := by
    rw [namesEq, helperNames_length, Nat.zero_add]
    exact aggregate_acceptsAt_kind plan.step.entryScope
  obtain ⟨statements, entryLines, _, valueName, entryNames, simulates⟩ :=
    (aggregate_render_spec plan.step.entry).1
      (fun context => uses = true → PrimitiveContext context)
      (fun context admitted used =>
        admitted (bodyUses plan.step.entry (List.mem_append_right _ (by simp)) used))
      names .word [.word "sc_arg"] 4 0 entry entryKind entryEquation
      (single_abinding_fresh argument_not_temporary cellTemp_ne_argument
        payloadTemp_ne_argument)
      (single_abinding_distinct _)
  let file := aggregateLoopFile (aggregateAliases bodies) declarations statements result
    plan.mask
  have argumentOk : ∀ index found, anameAt [Binding.word "sc_arg"] index = some found →
      ValidIdentifier found ∧ isReserved found = false :=
    single_abinding_ok (keyword_valid (by decide)) (by decide)
  have functionNamesOk : ∀ name ∈ names, ValidIdentifier name ∧ isReserved name = false := by
    rw [namesEq]
    exact helperNames_ok
  have valueOk := aggregate_identifier_ok argumentOk functionNamesOk
    (valueName result resultFound).uses
  have stepOk : (stepDecl statements result).NamesOk ∧
      ∀ name ∈ (stepDecl statements result).identifiers, ValidIdentifier name := by
    have bodyOk := fun name mem =>
      aggregate_identifier_ok argumentOk functionNamesOk (entryNames name mem)
    refine ⟨⟨show isReserved "sc_step" = false by decide, ?_,
      fun name mem => (bodyOk name mem).2, ?_⟩, ?_⟩
    · intro parameter mem
      simp only [stepDecl, List.mem_singleton] at mem
      subst mem
      decide
    · intro name mem
      simp only [stepDecl, Expr.identifiers, List.mem_singleton] at mem
      subst mem
      exact valueOk.2
    · intro name mem
      simp only [stepDecl, FunctionDecl.identifiers, List.map_cons, List.map_nil,
        List.cons_append, List.nil_append, List.mem_cons, List.mem_append, Expr.identifiers,
        List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl | mem | rfl
      · exact keyword_valid (by decide)
      · exact keyword_valid (by decide)
      · exact (bodyOk name mem).1
      · exact valueOk.1
  have functionsOk : ∀ function ∈ file.functions, function.NamesOk ∧
      ∀ name ∈ function.identifiers, ValidIdentifier name := by
    intro function mem
    rcases List.mem_append.mp mem with mem | mem
    · exact declarationsOk function mem
    · simp only [List.mem_singleton] at mem
      subst mem
      exact stepOk
  have printed : emitted.source = file.print := by
    have stepLines : (stepDecl statements result).lines =
        ["function sc_step(sc_arg: word) returns (word) {"] ++ entry.lines ++
          ["    return " ++ result ++ ";", "}", ""] := by
      simp only [stepDecl, FunctionDecl.lines, entryLines, List.cons_append, List.nil_append,
        List.cons.injEq]
      refine ⟨?_, ?_⟩
      · apply String.toList_inj.mp
        simp [FunctionDecl.parameterText, LocalType.spelling]
      · simp [Expr.print]
    have functionLine : "    function " ++ Loop.methodName ++
        "(input: uint256) public returns (uint256) {" =
          "    function " ++ file.method.name ++ "(" ++
            Method.parameterText file.method.parameters ++ ") public returns (uint256) {" := by
      apply String.toList_inj.mp
      simp [file, aggregateLoopFile, Method.parameterText, Loop.methodName]
    have returnLine : "        return uint256(sc_acc);" =
        "        return " ++ file.method.result.print ++ ";" := by
      apply String.toList_inj.mp
      simp [file, aggregateLoopFile, Expr.print]
    rw [source, LoopFile.print, LoopFile.lines, linesEq, functionLine, returnLine]
    simp [file, aggregateLoopFile, Loop.contractName, boundedBody_lines, stepLines, bodies]
  have parsed : parseLoopSource emitted.source = some file := by
    rw [printed]
    apply parseLoopSource_print
    · refine ⟨fun function mem => (functionsOk function mem).1, rfl, rfl, ?_,
        fun name mem => (boundedBody_names_ok plan.mask name mem).2, ?_⟩
      · intro parameter mem
        simp only [file, aggregateLoopFile, List.mem_singleton] at mem
        subst mem
        decide
      · intro name mem
        simp only [file, aggregateLoopFile, Expr.identifiers, List.mem_singleton] at mem
        subst mem
        decide
    · refine ⟨aggregateAliases_valid bodies, fun function mem => (functionsOk function mem).2,
        keyword_valid (show validIdentifier "SynthesizedLoops" = true by decide),
        keyword_valid (show validIdentifier "run" = true by decide), ?_,
        fun name mem => (boundedBody_names_ok plan.mask name mem).1, ?_⟩
      · intro parameter mem
        simp only [file, aggregateLoopFile, List.mem_singleton] at mem
        subst mem
        exact keyword_valid (by decide)
      · intro name mem
        simp only [file, aggregateLoopFile, Expr.identifiers, List.mem_singleton] at mem
        subst mem
        exact keyword_valid (by decide)
  refine ⟨file, printed, parsed, ?_⟩
  intro input
  have stepCall : ∀ arguments, file.context.call "sc_step" arguments =
      (stepDecl statements result).denote
        ⟨declareFunctions (aggregateAliases bodies) [] declarations, aggregateAliases bodies⟩
        arguments := by
    intro arguments
    show Context.call ⟨declareFunctions (aggregateAliases bodies) []
      (declarations ++ [stepDecl statements result]), aggregateAliases bodies⟩ "sc_step"
        arguments = _
    rw [declareFunctions_append_single]
    exact Context.call_cons_same _ _ _ _ _
  have behaves : ∀ (argument : Solcore.Core.Word) (store : Solcore.Core.Store),
      ∃ (value : Solcore.Core.Word) (store' : Solcore.Core.Store),
        Solcore.Core.Evaluates (.word argument :: plan.step.helpers.foldl closureStep [])
          store plan.step.entry.toCore (.word value) store' ∧
        store.length ≤ store'.length ∧
        (∀ location, location < store.length → store'.read? location = store.read? location) ∧
        file.context.call "sc_step" [.word argument.val] = some (.word value.val) := by
    intro argument store
    obtain ⟨core, store', scope', outer', _, evaluates, represents, exec, _, frame, _⟩ :=
      simulates ⟨declareFunctions (aggregateAliases bodies) [] declarations,
          aggregateAliases bodies⟩
        (.word argument :: plan.step.helpers.foldl closureStep []) store []
        [[("sc_arg", .word argument.val)]] primitive
        (single_abinding_agree (by simp [Frames.lookup, Scope.get?]) _ store)
        (single_abinding_cells _ _ _) (by simp) (by simpa using agree)
    rw [resultFound, Option.bind_some] at represents
    obtain ⟨_, lookup, value, rfl, rfl⟩ := represents
    refine ⟨value, store', evaluates, frame.1, fun location inBounds =>
      frame.2 location inBounds fun index isCell => ?_, ?_⟩
    · obtain ⟨⟨_, found⟩, _⟩ := isCell
      cases index with
      | zero => simp at found
      | succ index => simp at found
    · rw [stepCall]
      simp [stepDecl, FunctionDecl.denote, FunctionDecl.bindParameters, LocalType.admits, exec,
        Expr.eval, lookup]
  obtain ⟨final, store, evaluates, loopRun⟩ := storeLoop_meaning behaves input
  refine ⟨final, ?_, runStateful_of_evaluates_store evaluates⟩
  intro fuel enough
  have masked : plan.mask < Evm.modulus := by
    have := loopPlan_mask_le plan
    simp only [Evm.modulus]
    omega
  have parameters : Method.bindParameters ["input"] [input.val] =
      some [("input", .uint256 input.val)] := by
    simp [Method.bindParameters, word_lt_modulus]
  have execBody : LoopStmt.execList file.context fuel [[], [("input", .uint256 input.val)]]
      (boundedBody plan.mask) = some (loopFrames input.val (Evm.and input.val plan.mask)
        (Evm.and input.val plan.mask) final.val) := by
    rw [boundedBody_exec _ _ masked, loopRun fuel enough]
  simp only [file, aggregateLoopFile] at execBody
  simp [file, aggregateLoopFile, LoopFile.call, LoopMethod.run, parameters, execBody, Expr.eval,
    loopFrames, Frames.lookup, Scope.get?]

/-- **Aggregate loop emitter preservation, on the emitted text.** The emitted
`run` terminates on every input: with fuel above the mask, the loop meaning of
the text returns the Word that Core returns, with its final store. All
completed calls agree (`loopSourceCall_unique`). -/
theorem Loop.emit_source_meaning {plan : CheckedPlan} {emitted : EmittedProgram}
    (emitted_eq : Loop.emit plan = .ok emitted) (input : Solcore.Core.Word) :
    ∃ word : Solcore.Core.Word,
      (∀ fuel, plan.mask < fuel →
        loopSourceCall fuel emitted.source "run" [input.val] = some word.val) ∧
      CoreReturnsWithStore (plan.instantiate input).toCore word := by
  obtain ⟨file, _, parsed, meaning⟩ := Loop.emit_preserves_meaning emitted_eq
  obtain ⟨word, called, core⟩ := meaning input
  exact ⟨word, fun fuel enough => by simp [loopSourceCall, parsed, called fuel enough], core⟩

end Solcore.Synthesis.Source.ScalarMeaning
