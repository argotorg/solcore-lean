import Solcore.Core.BitwiseLogic
import Solcore.Core.DirectWordComparisons
import Solcore.Synthesis.Source.CallGraphLoopEmitter
import Solcore.Synthesis.Source.ScalarMeaning.CallGraphEmitter
import Solcore.Synthesis.Source.ScalarMeaning.LoopText
import Solcore.Synthesis.Source.ScalarMeaning.MutationEmitter

/-! Meaning preservation for the actual call-graph loop emitter
(`CallGraphLoop.emit`, profile `runtime-call-graph-loops`). The helpers are
free functions as for the call-graph emitter, and the entry becomes the free
function `sc_step`. The method runs a source `while` loop that applies
`sc_step` to an accumulator `input & mask` times, under the fuel-indexed loop
semantics. The Core reference instead checks literal ordinals against the
bound and keeps the accumulator in a cell, so the Core result is stated with
its final store. The step is a scalar call graph and never touches the store. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.ScalarMeaning

open Solcore.Synthesis.Core.CallGraphLoop (CheckedPlan)
open Solcore.Synthesis.Source.ScalarRenderer (Rendered)

/-! ### The emitted text -/

theorem CallGraphLoop.emit_success {plan : CheckedPlan} {emitted : EmittedProgram}
    (emitted_eq : CallGraphLoop.emit plan = .ok emitted) :
    ∃ (names lines : List String) (entry : Rendered),
      helperLoop CallGraphRenderer.renderWithFunctions plan.graph.helpers 0 []
        ["import * from std;", "import * from std.dispatch;", Primitive.opcodeImport, ""] =
        .ok (names, lines) ∧
      CallGraphRenderer.renderWithFunctions names .word ["sc_arg"] 4 0 plan.graph.entry =
        .ok entry ∧
      emitted.source = String.intercalate "\n" (lines ++
        ["function sc_step(sc_arg: word) returns (word) {"] ++ entry.lines ++
        ["    return " ++ entry.value ++ ";", "}", "",
          "contract " ++ CallGraphLoop.contractName ++ " {",
          "    function " ++ CallGraphLoop.methodName ++
            "(input: uint256) public returns (uint256) {",
          "        let sc_input: word = Typedef.rep(input);",
          "        let sc_limit: word = (sc_input & " ++ toString plan.mask ++ ");",
          "        let sc_acc: word = sc_input;",
          "        let sc_counter: word = 0;",
          "        while (sc_limit > sc_counter) {",
          "            sc_acc = sc_step(sc_acc);",
          "            sc_counter = (sc_counter + 1);",
          "        }",
          "        return uint256(sc_acc);", "    }", "}"]) ++ "\n" := by
  unfold CallGraphLoop.emit at emitted_eq
  dsimp only at emitted_eq
  rw [forIn_helperLoop (render := CallGraphRenderer.renderWithFunctions) (fun _ _ _ _ => rfl)]
    at emitted_eq
  cases loop : helperLoop CallGraphRenderer.renderWithFunctions plan.graph.helpers 0 []
    ["import * from std;", "import * from std.dispatch;", Primitive.opcodeImport, ""] with
  | error error =>
      rw [loop] at emitted_eq
      cases emitted_eq
  | ok result =>
      obtain ⟨names, lines⟩ := result
      rw [loop] at emitted_eq
      cases entry : CallGraphRenderer.renderWithFunctions names .word ["sc_arg"] 4 0
        plan.graph.entry with
      | error error =>
          simp only [bind, Except.bind, entry] at emitted_eq
          cases emitted_eq
      | ok rendered =>
          simp only [bind, Except.bind, entry, pure, Except.pure, Except.ok.injEq] at emitted_eq
          subst emitted_eq
          exact ⟨names, lines, rendered, rfl, entry, rfl⟩

/-- The free function printed for the loop step, the rendered graph entry. -/
def stepDecl (statements : List Stmt) (value : String) : FunctionDecl where
  name := "sc_step"
  parameters := [("sc_arg", .word)]
  resultType := .word
  body := statements
  result := .name value

/-- The loop condition `sc_limit > sc_counter`. -/
def boundedCondition : Expr := .binary .gt (.name "sc_limit") (.name "sc_counter")

/-- The loop body: apply the step to the accumulator, then count. -/
def boundedStep : List Stmt :=
  [.assign "sc_acc" (.call1 "sc_step" (.name "sc_acc")),
    .assign "sc_counter" (.binary .add (.name "sc_counter") (.number 1))]

/-- The method body printed by the bounded-loop wrappers: the bound is the
input masked by `mask`, and the loop counts from zero up to it. -/
def boundedBody (mask : Nat) : List LoopStmt :=
  [.plain (.letDecl "sc_input" .word (.typedefRep (.name "input"))),
    .plain (.letDecl "sc_limit" .word (.binary .bitAnd (.name "sc_input") (.number mask))),
    .plain (.letDecl "sc_acc" .word (.name "sc_input")),
    .plain (.letDecl "sc_counter" .word (.number 0)),
    .whileLoop .gt (.name "sc_limit") (.name "sc_counter") boundedStep]

/-- The loop file printed by the call-graph loop emitter. -/
def callGraphLoopFile (declarations : List FunctionDecl) (statements : List Stmt)
    (value : String) (mask : Nat) : LoopFile where
  opcodeAliases := primitiveAliases
  functions := declarations ++ [stepDecl statements value]
  contract := "SynthesizedCallGraphLoops"
  method := {
    name := "run"
    parameters := ["input"]
    body := boundedBody mask
    result := .uint256 (.name "sc_acc") }

theorem boundedBody_lines (mask : Nat) :
    LoopStmt.listLines 8 (boundedBody mask) =
      ["        let sc_input: word = Typedef.rep(input);",
        "        let sc_limit: word = (sc_input & " ++ toString mask ++ ");",
        "        let sc_acc: word = sc_input;",
        "        let sc_counter: word = 0;",
        "        while (sc_limit > sc_counter) {",
        "            sc_acc = sc_step(sc_acc);",
        "            sc_counter = (sc_counter + 1);",
        "        }"] := by
  simp only [boundedBody, boundedStep, LoopStmt.listLines, LoopStmt.lines, Stmt.lines,
    Stmt.listLines, List.cons_append, List.nil_append, List.append_nil, List.cons.injEq,
    and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply String.toList_inj.mp <;>
    simp [indentLine, Expr.print, LocalType.spelling, BinaryOp.spelling] <;> rfl

theorem boundedBody_identifiers (mask : Nat) :
    LoopStmt.listIdentifiers (boundedBody mask) =
      ["sc_input", "input", "sc_limit", "sc_input", "sc_acc", "sc_input", "sc_counter",
        "sc_limit", "sc_counter", "sc_acc", "sc_step", "sc_acc", "sc_counter", "sc_counter"] := by
  simp [boundedBody, boundedStep, LoopStmt.listIdentifiers, LoopStmt.identifiers,
    Stmt.identifiers, Stmt.listIdentifiers, Expr.identifiers]

theorem boundedBody_names_ok (mask : Nat) :
    ∀ name ∈ LoopStmt.listIdentifiers (boundedBody mask),
      ValidIdentifier name ∧ isReserved name = false := by
  have checked : ∀ name ∈ ["sc_input", "input", "sc_limit", "sc_input", "sc_acc", "sc_input",
      "sc_counter", "sc_limit", "sc_counter", "sc_acc", "sc_step", "sc_acc", "sc_counter",
      "sc_counter"], validIdentifier name = true ∧ isReserved name = false := by
    decide
  rw [boundedBody_identifiers]
  exact fun name mem => ⟨keyword_valid (checked name mem).1, (checked name mem).2⟩

/-! ### The Core bounded loop -/

/-- The finite ordinal guards of `BoundedLoop`, restated. At ordinal `i`, the
accumulator cell, the bound, the input and the step closure are at indices `i`
to `i + 3`, after `i` Unit binders. -/
def loopGuards : Nat → Nat → CoreExpr
  | 0, ordinal => .loadCell (.var ordinal)
  | remaining + 1, ordinal =>
      .letE (.ifE (.binary .wordGt (.var (ordinal + 1))
          (.word (Solcore.Core.Word.ofNatModulo ordinal)))
        (.storeCell (.var ordinal) (.apply (.var (ordinal + 3)) (.loadCell (.var ordinal))))
        .unit)
        (loopGuards remaining (ordinal + 1))

/-- The applied bounded-loop program, for every admitted mask. -/
theorem appliedProgram_body {step : Solcore.Synthesis.Core.Aggregates.CheckedDAG} {mask : Nat}
    (allowed : Solcore.Synthesis.Core.BoundedLoop.AllowedMask mask)
    (input : Solcore.Core.Word) :
    (Solcore.Synthesis.Core.BoundedLoop.appliedProgram step mask input).body =
      .apply (.letE step.program.body (.lambda .word .word
        (.letE (.binary .wordAnd (.var 0) (.word (Solcore.Core.Word.ofNatModulo mask)))
          (.letE (.newCell .word (.var 1)) (loopGuards mask 0))))) (.word input) := by
  rcases allowed with rfl | rfl | rfl | rfl <;> rfl

/-- Core's environment at one ordinal of the guards. -/
def guardEnvironment (closure : CoreValue) (input bound : Solcore.Core.Word) (ordinal : Nat) :
    Solcore.Core.Environment :=
  List.replicate ordinal .unit ++
    [.cellRef (Solcore.Core.Wire.Ty.toCore .word) 0, .word bound, .word input, closure]

theorem guardEnvironment_cell (closure : CoreValue) (input bound : Solcore.Core.Word)
    (ordinal : Nat) : (guardEnvironment closure input bound ordinal)[ordinal]? =
      some (.cellRef (Solcore.Core.Wire.Ty.toCore .word) 0) := by
  simp [guardEnvironment]

theorem guardEnvironment_bound (closure : CoreValue) (input bound : Solcore.Core.Word)
    (ordinal : Nat) : (guardEnvironment closure input bound ordinal)[ordinal + 1]? =
      some (.word bound) := by
  simp [guardEnvironment]

theorem guardEnvironment_closure (closure : CoreValue) (input bound : Solcore.Core.Word)
    (ordinal : Nat) : (guardEnvironment closure input bound ordinal)[ordinal + 3]? =
      some closure := by
  simp [guardEnvironment]

theorem guardEnvironment_succ (closure : CoreValue) (input bound : Solcore.Core.Word)
    (ordinal : Nat) : .unit :: guardEnvironment closure input bound ordinal =
      guardEnvironment closure input bound (ordinal + 1) := by
  simp [guardEnvironment, List.replicate_succ]

theorem ofNatModulo_val_small {ordinal : Nat} (small : ordinal < 2 ^ 256) :
    (Solcore.Core.Word.ofNatModulo ordinal).val = ordinal := by
  simp [Solcore.Core.Word.ofNatModulo, Solcore.Core.wordModulus, Nat.mod_eq_of_lt small]

/-- From the bound on, a guard skips the step and keeps the accumulator. -/
theorem guards_skip {closure : CoreValue} {input bound accumulator : Solcore.Core.Word} :
    ∀ (remaining ordinal : Nat), bound.val ≤ ordinal → ordinal + remaining < 2 ^ 256 →
      Solcore.Core.Evaluates (guardEnvironment closure input bound ordinal) [.word accumulator]
        (loopGuards remaining ordinal).toCore (.word accumulator) [.word accumulator]
  | 0, ordinal, _, _ => by
      simp only [loopGuards, Solcore.Core.Wire.Expr.toCore]
      exact .loadCell (.var (guardEnvironment_cell closure input bound ordinal)) rfl
  | remaining + 1, ordinal, past, small => by
      simp only [loopGuards, Solcore.Core.Wire.Expr.toCore, Solcore.Core.Wire.BinaryOp.toCore]
      have notGreater : ¬ bound > Solcore.Core.Word.ofNatModulo ordinal := by
        show ¬ (Solcore.Core.Word.ofNatModulo ordinal).val < bound.val
        rw [ofNatModulo_val_small (by omega)]
        omega
      refine .letE (.ifFalse (Solcore.Core.Evaluates.wordGt_not_gt notGreater
        (.var (guardEnvironment_bound closure input bound ordinal)) .word) .unit) ?_
      rw [guardEnvironment_succ]
      exact guards_skip remaining (ordinal + 1) (by omega) (by omega)

/-! ### The source while loop -/

/-- The method's frames while its loop runs. -/
def loopFrames (input limit counter accumulator : Nat) : Frames :=
  [[("sc_counter", .word counter), ("sc_acc", .word accumulator), ("sc_limit", .word limit),
    ("sc_input", .word input)], [("input", .uint256 input)]]

theorem boundedCondition_eval (context : Context) (input limit counter accumulator : Nat) :
    boundedCondition.eval context (loopFrames input limit counter accumulator) =
      some (.bool (decide (counter < limit))) := by
  by_cases below : counter < limit <;>
    simp [boundedCondition, Expr.eval, loopFrames, Frames.lookup, Scope.get?, BinaryOp.apply,
      toBool, Evm.gt, below]

theorem one_lt_modulus : 1 < Evm.modulus := by decide

theorem boundedStep_exec {context : Context} {input limit counter accumulator next : Nat}
    (stepped : context.call "sc_step" [.word accumulator] = some (.word next))
    (small : counter + 1 < Evm.modulus) :
    Stmt.execList context ([] :: loopFrames input limit counter accumulator) boundedStep =
      some ([] :: loopFrames input limit (counter + 1) next) := by
  simp [boundedStep, Stmt.execList, Stmt.exec, Expr.eval, loopFrames, Frames.lookup,
    Scope.get?, stepped, Value.sameType, Frames.assign, Scope.set?, BinaryOp.apply, Evm.add,
    Nat.mod_eq_of_lt small, one_lt_modulus]

/-- Before the loop, the method declares the input word, the bound, the
accumulator and the counter. -/
theorem boundedBody_exec (context : Context) (fuel : Nat) {mask : Nat}
    (small : mask < Evm.modulus) (input : Nat) :
    LoopStmt.execList context fuel [[], [("input", .uint256 input)]] (boundedBody mask) =
      runWhile context boundedCondition boundedStep fuel
        (loopFrames input (Evm.and input mask) 0 input) := by
  have zero : 0 < Evm.modulus := by decide
  have declared : LoopStmt.execList context fuel [[], [("input", .uint256 input)]]
      (boundedBody mask) = LoopStmt.execList context fuel
        (loopFrames input (Evm.and input mask) 0 input)
        [.whileLoop .gt (.name "sc_limit") (.name "sc_counter") boundedStep] := by
    simp [boundedBody, LoopStmt.execList, LoopStmt.exec, Stmt.exec, Expr.eval, Frames.lookup,
      Scope.get?, LocalType.admits, Frames.declare, BinaryOp.apply, small, zero, loopFrames]
  rw [declared]
  simp only [LoopStmt.execList, LoopStmt.exec, boundedCondition]
  cases runWhile context (.binary .gt (.name "sc_limit") (.name "sc_counter")) boundedStep fuel
    (loopFrames input (Evm.and input mask) 0 input) <;> rfl

/-! ### The loop agrees with the guards -/

/-- From an ordinal `count` steps before the bound, the Core guards and the
source loop both apply the step `count` times. -/
theorem boundedLoop_agrees {context : Context} {closures : List CoreValue} {entry : CoreExpr}
    (behaves : ∀ (argument : Solcore.Core.Word) (store : Solcore.Core.Store),
      ∃ result : Solcore.Core.Word,
        Solcore.Core.Evaluates (.word argument :: closures) store entry.toCore (.word result)
          store ∧
        context.call "sc_step" [.word argument.val] = some (.word result.val))
    (input bound : Solcore.Core.Word) {mask : Nat} (bounded : bound.val ≤ mask)
    (small : mask < 2 ^ 255) :
    ∀ (count ordinal remaining : Nat) (accumulator : Solcore.Core.Word),
      ordinal + count = bound.val → ordinal + remaining = mask →
      ∃ final : Solcore.Core.Word,
        Solcore.Core.Evaluates
          (guardEnvironment (.closure (Solcore.Core.Wire.Ty.toCore .word)
            (Solcore.Core.Wire.Ty.toCore .word) entry.toCore closures) input bound ordinal)
          [.word accumulator] (loopGuards remaining ordinal).toCore (.word final)
          [.word final] ∧
        ∀ fuel, count < fuel →
          runWhile context boundedCondition boundedStep fuel
            (loopFrames input.val bound.val ordinal accumulator.val) =
            some (loopFrames input.val bound.val bound.val final.val)
  | 0, ordinal, remaining, accumulator, reached, total => by
      refine ⟨accumulator, guards_skip remaining ordinal (by omega) (by omega), ?_⟩
      intro fuel enough
      obtain ⟨fuel, rfl⟩ : ∃ rest, fuel = rest + 1 := ⟨fuel - 1, by omega⟩
      have same : ordinal = bound.val := by omega
      rw [same]
      simp [runWhile, boundedCondition_eval]
  | count + 1, ordinal, remaining, accumulator, reached, total => by
      obtain ⟨rest, rfl⟩ : ∃ rest, remaining = rest + 1 := ⟨remaining - 1, by omega⟩
      obtain ⟨next, stepCore, stepSource⟩ := behaves accumulator [.word accumulator]
      obtain ⟨final, guardsRest, loopRest⟩ :=
        boundedLoop_agrees behaves input bound bounded small count (ordinal + 1) rest next
          (by omega) (by omega)
      refine ⟨final, ?_, ?_⟩
      · simp only [loopGuards, Solcore.Core.Wire.Expr.toCore, Solcore.Core.Wire.BinaryOp.toCore]
        have greater : bound > Solcore.Core.Word.ofNatModulo ordinal := by
          show (Solcore.Core.Word.ofNatModulo ordinal).val < bound.val
          rw [ofNatModulo_val_small (by omega)]
          omega
        refine .letE (.ifTrue (Solcore.Core.Evaluates.wordGt_gt greater
          (.var (guardEnvironment_bound _ input bound ordinal)) .word)
          (.storeCell (.var (guardEnvironment_cell _ input bound ordinal)) rfl
            (.apply (.var (guardEnvironment_closure _ input bound ordinal))
              (.loadCell (.var (guardEnvironment_cell _ input bound ordinal)) rfl) stepCore)
            rfl)) ?_
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

/-- Every admitted mask is at most seven. -/
theorem plan_mask_le (plan : CheckedPlan) : plan.mask ≤ 7 := by
  show plan.loop.mask ≤ 7
  rcases plan.loop.allowed with same | same | same | same <;> rw [same] <;> decide

/-- The applied Core reference returns the accumulator after the step was
applied `input & mask` times, as the source loop does. -/
theorem boundedLoop_meaning {context : Context} {plan : CheckedPlan}
    (behaves : ∀ (argument : Solcore.Core.Word) (store : Solcore.Core.Store),
      ∃ result : Solcore.Core.Word,
        Solcore.Core.Evaluates (.word argument :: plan.graph.helpers.foldl closureStep [])
          store plan.graph.entry.toCore (.word result) store ∧
        context.call "sc_step" [.word argument.val] = some (.word result.val))
    (input : Solcore.Core.Word) :
    ∃ final : Solcore.Core.Word,
      Solcore.Core.Evaluates [] [] (plan.instantiate input).toCore.body (.word final)
        [.word final] ∧
      ∀ fuel, plan.mask < fuel →
        runWhile context boundedCondition boundedStep fuel
          (loopFrames input.val (Evm.and input.val plan.mask) 0 input.val) =
          some (loopFrames input.val (Evm.and input.val plan.mask)
            (Evm.and input.val plan.mask) final.val) := by
  have allowed := plan.loop.allowed
  have masked := plan_mask_le plan
  let maskWord := Solcore.Core.Word.ofNatModulo plan.mask
  let bound := input.bitAnd maskWord
  have maskVal : maskWord.val = plan.mask := ofNatModulo_val_small (by omega)
  have boundVal : bound.val = Evm.and input.val plan.mask := by
    rw [← maskVal]
    exact (evm_and input maskWord).symm
  have bounded : bound.val ≤ plan.mask := by
    rw [boundVal]
    exact Nat.and_le_right
  obtain ⟨final, guards, loop⟩ := boundedLoop_agrees behaves input bound bounded (by omega)
    bound.val 0 plan.mask input (by omega) (by omega)
  refine ⟨final, ?_, ?_⟩
  · have body : (plan.instantiate input).toCore.body = Solcore.Core.Wire.Expr.toCore
        (.apply (.letE (Solcore.Synthesis.Core.functionDAGExpression plan.graph.helpers
          plan.graph.entry) (.lambda .word .word
            (.letE (.binary .wordAnd (.var 0) (.word maskWord))
              (.letE (.newCell .word (.var 1)) (loopGuards plan.mask 0))))) (.word input)) := by
      show (Solcore.Synthesis.Core.BoundedLoop.appliedProgram plan.loop.step plan.loop.mask
        input).body.toCore = _
      rw [appliedProgram_body allowed, plan.step_program]
      rfl
    rw [body]
    simp only [Solcore.Core.Wire.Expr.toCore, Solcore.Core.Wire.BinaryOp.toCore]
    exact .apply (.letE (dag_evaluates plan.graph.entry plan.graph.helpers [] []) .lambda) .word
      (.letE (Solcore.Core.Evaluates.wordAnd (.var rfl) .word) (.letE (.newCell (.var rfl)) guards))
  · intro fuel enough
    rw [← boundVal]
    exact loop fuel (by omega)

/-! ### The step and the emitted file -/

/-- The step function behaves as the Core entry closure, as a helper does. -/
theorem stepDecl_behaves {functions : List (String × (List Value → Option Value))}
    {names : List String} {closures : List CoreValue} {entry : CoreExpr}
    {statements : List Stmt} {value : String} {last : Nat}
    (simulates : Simulates PrimitiveContext entry .word names ["sc_arg"] 0 last statements value)
    (admitted : PrimitiveContext ⟨functions, primitiveAliases⟩)
    (agree : FunctionsAgree ⟨functions, primitiveAliases⟩ names closures)
    (argument : Solcore.Core.Word) (store : Solcore.Core.Store) :
    ∃ result : Solcore.Core.Word,
      Solcore.Core.Evaluates (.word argument :: closures) store entry.toCore (.word result)
        store ∧
      (stepDecl statements value).denote ⟨functions, primitiveAliases⟩ [.word argument.val] =
        some (.word result.val) := by
  have localsAgree : LocalsAgree [[], [("sc_arg", .word argument.val)]] ["sc_arg"]
      (.word argument :: closures) := by
    intro index name found
    cases index with
    | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at found
        subst found
        exact ⟨argument, rfl, by simp [Frames.lookup, Scope.get?]⟩
    | succ index => simp at found
  obtain ⟨core, result, scope', outer', _, evaluates, represents, exec, lookup, _⟩ :=
    simulates ⟨functions, primitiveAliases⟩ (.word argument :: closures) store [] _ admitted
      localsAgree (by simp) (by simpa using agree)
  obtain ⟨word, rfl, rfl⟩ := represents
  refine ⟨word, evaluates, ?_⟩
  simp [stepDecl, FunctionDecl.denote, FunctionDecl.bindParameters, LocalType.admits, exec,
    Expr.eval, lookup]

theorem declareFunctions_append_single (aliases : List (String × String)) :
    ∀ (functions : List (String × (List Value → Option Value)))
      (declarations : List FunctionDecl) (last : FunctionDecl),
      declareFunctions aliases functions (declarations ++ [last]) =
        (last.name, last.denote ⟨declareFunctions aliases functions declarations, aliases⟩) ::
          declareFunctions aliases functions declarations
  | _, [], _ => rfl
  | functions, declaration :: rest, last =>
      declareFunctions_append_single aliases
        ((declaration.name, declaration.denote ⟨functions, aliases⟩) :: functions) rest last

/-! ### Preservation -/

/-- **Call-graph loop emitter preservation.** If the actual emitter succeeds,
its source text is the printing of a loop file with the raw opcode imports, one
free function per helper and the step function `sc_step`, and parses back to it.
For every runtime input, calling `run(uint256)` under the fuel-indexed source
semantics, with fuel above the mask, returns exactly the Word that the original
Core bounded loop, applied to that input, returns with its final store. -/
theorem CallGraphLoop.emit_preserves_meaning {plan : CheckedPlan} {emitted : EmittedProgram}
    (emitted_eq : CallGraphLoop.emit plan = .ok emitted) :
    ∃ file : LoopFile, emitted.source = file.print ∧
      parseLoopSource emitted.source = some file ∧
      ∀ input : Solcore.Core.Word, ∃ word : Solcore.Core.Word,
        (∀ fuel, plan.mask < fuel → file.call fuel "run" [input.val] = some word.val) ∧
        CoreReturnsWithStore (plan.instantiate input).toCore word := by
  obtain ⟨names, lines, entry, loop, entryEquation, source⟩ :=
    CallGraphLoop.emit_success emitted_eq
  obtain ⟨declarations, linesEq, namesEq, declarationsOk, admitted, agree⟩ :=
    helperLoop_spec callGraph_render_spec primitiveCallees_ok
      (fun _ index meaning admitted => admitted.extend index meaning) plan.graph.helpers 0 _
      names lines [] [] loop (helpers_accepted plan.graph.helperScopes) primitiveContext_aliases
      (fun _ _ found => by simp [helperNames] at found)
  have fresh : ∀ name ∈ ["sc_arg"], OlderThan 0 name := by
    intro name mem index same
    simp only [List.mem_singleton] at mem
    subst mem
    exact absurd same (argument_not_temporary index)
  obtain ⟨statements, entryLines, _, valueName, entryNames, simulates⟩ :=
    callGraph_render_spec plan.graph.entry names 1 plan.graph.helpers.length .word ["sc_arg"] 4
      0 entry plan.graph.entryScope entryEquation fresh
  let file := callGraphLoopFile declarations statements entry.value plan.mask
  have localsOk : ∀ local_ ∈ ["sc_arg"], ValidIdentifier local_ ∧
      isReserved local_ = false := by
    intro local_ mem
    simp only [List.mem_singleton] at mem
    subst mem
    exact ⟨keyword_valid (by decide), by decide⟩
  have functionNamesOk : ∀ name ∈ names, ValidIdentifier name ∧ isReserved name = false := by
    rw [namesEq]
    exact helperNames_ok
  have valueOk := rendered_name_ok localsOk valueName
  have stepOk : (stepDecl statements entry.value).NamesOk ∧
      ∀ name ∈ (stepDecl statements entry.value).identifiers, ValidIdentifier name := by
    have bodyOk := fun name mem =>
      rendered_identifier_ok localsOk functionNamesOk primitiveCallees_ok (entryNames name mem)
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
    have stepLines : (stepDecl statements entry.value).lines =
        ["function sc_step(sc_arg: word) returns (word) {"] ++ entry.lines ++
          ["    return " ++ entry.value ++ ";", "}", ""] := by
      simp only [stepDecl, FunctionDecl.lines, entryLines, List.cons_append, List.nil_append,
        List.cons.injEq]
      refine ⟨?_, ?_⟩
      · apply String.toList_inj.mp
        simp [FunctionDecl.parameterText, LocalType.spelling]
      · simp [Expr.print]
    have functionLine : "    function " ++ CallGraphLoop.methodName ++
        "(input: uint256) public returns (uint256) {" =
          "    function " ++ file.method.name ++ "(" ++
            Method.parameterText file.method.parameters ++ ") public returns (uint256) {" := by
      apply String.toList_inj.mp
      simp [file, callGraphLoopFile, Method.parameterText, CallGraphLoop.methodName]
    have returnLine : "        return uint256(sc_acc);" =
        "        return " ++ file.method.result.print ++ ";" := by
      apply String.toList_inj.mp
      simp [file, callGraphLoopFile, Expr.print]
    rw [source, LoopFile.print, LoopFile.lines, linesEq, functionLine, returnLine]
    simp [file, callGraphLoopFile, primitiveImportLines, CallGraphLoop.contractName,
      opcodeImport_eq, boundedBody_lines, stepLines]
  have parsed : parseLoopSource emitted.source = some file := by
    rw [printed]
    apply parseLoopSource_print
    · refine ⟨fun function mem => (functionsOk function mem).1, rfl, rfl, ?_,
        fun name mem => (boundedBody_names_ok plan.mask name mem).2, ?_⟩
      · intro parameter mem
        simp only [file, callGraphLoopFile, List.mem_singleton] at mem
        subst mem
        decide
      · intro name mem
        simp only [file, callGraphLoopFile, Expr.identifiers, List.mem_singleton] at mem
        subst mem
        decide
    · refine ⟨primitiveAliases_valid, fun function mem => (functionsOk function mem).2,
        keyword_valid (show validIdentifier "SynthesizedCallGraphLoops" = true by decide),
        keyword_valid (show validIdentifier "run" = true by decide), ?_,
        fun name mem => (boundedBody_names_ok plan.mask name mem).1, ?_⟩
      · intro parameter mem
        simp only [file, callGraphLoopFile, List.mem_singleton] at mem
        subst mem
        exact keyword_valid (by decide)
      · intro name mem
        simp only [file, callGraphLoopFile, Expr.identifiers, List.mem_singleton] at mem
        subst mem
        exact keyword_valid (by decide)
  refine ⟨file, printed, parsed, ?_⟩
  intro input
  have stepCall : ∀ arguments, file.context.call "sc_step" arguments =
      (stepDecl statements entry.value).denote
        ⟨declareFunctions primitiveAliases [] declarations, primitiveAliases⟩ arguments := by
    intro arguments
    show Context.call ⟨declareFunctions primitiveAliases []
      (declarations ++ [stepDecl statements entry.value]), primitiveAliases⟩ "sc_step"
        arguments = _
    rw [declareFunctions_append_single]
    exact Context.call_cons_same _ _ _ _ _
  have behaves : ∀ (argument : Solcore.Core.Word) (store : Solcore.Core.Store),
      ∃ result : Solcore.Core.Word,
        Solcore.Core.Evaluates (.word argument :: plan.graph.helpers.foldl closureStep [])
          store plan.graph.entry.toCore (.word result) store ∧
        file.context.call "sc_step" [.word argument.val] = some (.word result.val) := by
    intro argument store
    obtain ⟨result, evaluates, denoted⟩ :=
      stepDecl_behaves simulates admitted agree argument store
    exact ⟨result, evaluates, by rw [stepCall]; exact denoted⟩
  obtain ⟨final, evaluates, loopRun⟩ := boundedLoop_meaning behaves input
  refine ⟨final, ?_, runStateful_of_evaluates_store evaluates⟩
  intro fuel enough
  have masked : plan.mask < Evm.modulus := by
    have := plan_mask_le plan
    simp only [Evm.modulus]
    omega
  have parameters : Method.bindParameters ["input"] [input.val] =
      some [("input", .uint256 input.val)] := by
    simp [Method.bindParameters, word_lt_modulus]
  have execBody : LoopStmt.execList file.context fuel [[], [("input", .uint256 input.val)]]
      (boundedBody plan.mask) = some (loopFrames input.val (Evm.and input.val plan.mask)
        (Evm.and input.val plan.mask) final.val) := by
    rw [boundedBody_exec _ _ masked, loopRun fuel enough]
  simp only [file, callGraphLoopFile] at execBody
  simp [file, callGraphLoopFile, LoopFile.call, LoopMethod.run, parameters, execBody, Expr.eval,
    loopFrames, Frames.lookup, Scope.get?]

/-- **Call-graph loop emitter preservation, on the emitted text.** The emitted
`run` terminates on every input: with fuel above the mask, the loop meaning of
the text returns the Word that Core returns. All completed calls agree
(`loopSourceCall_unique`). -/
theorem CallGraphLoop.emit_source_meaning {plan : CheckedPlan} {emitted : EmittedProgram}
    (emitted_eq : CallGraphLoop.emit plan = .ok emitted) (input : Solcore.Core.Word) :
    ∃ word : Solcore.Core.Word,
      (∀ fuel, plan.mask < fuel →
        loopSourceCall fuel emitted.source "run" [input.val] = some word.val) ∧
      CoreReturnsWithStore (plan.instantiate input).toCore word := by
  obtain ⟨file, _, parsed, meaning⟩ := CallGraphLoop.emit_preserves_meaning emitted_eq
  obtain ⟨word, called, core⟩ := meaning input
  exact ⟨word, fun fuel enough => by simp [loopSourceCall, parsed, called fuel enough], core⟩

end Solcore.Synthesis.Source.ScalarMeaning
