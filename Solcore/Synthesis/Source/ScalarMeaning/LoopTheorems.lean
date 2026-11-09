import Solcore.Core.Internal.PrimitiveLaws
import Solcore.Core.Internal.WordComparisons
import Solcore.Synthesis.Internal.Loops
import Solcore.Synthesis.Source.ScalarMeaning.PureTheorems
import Solcore.Synthesis.Source.ScalarMeaning.LoopGrammar
import Solcore.Synthesis.Internal.LanguageFeatures

/-!
# Emitter meaning: loops and generics

The same for bounded loops and the generic selector. Main theorems:
`CallGraphLoop.emit_source_meaning`, `Loop.emit_source_meaning`, `Generic.emit_source_meaning`.
-/

section
-- leanmerge: from Solcore.Synthesis.Source.ScalarMeaning.CallGraphLoopEmitter
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
        ["pragma solcore;", "import * from std;", "import * from std.dispatch;",
          Primitive.opcodeImport, ""] =
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
    ["pragma solcore;", "import * from std;", "import * from std.dispatch;",
      Primitive.opcodeImport, ""] with
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
end

section
-- leanmerge: from Solcore.Synthesis.Source.ScalarMeaning.GenericEmitter
/-! Meaning preservation for the actual generic emitter (`Generic.emit`,
profile `runtime-generics`). The file declares the generic selector
`sc_select<a>`, then the helpers as for the aggregate emitter and the entry as
`sc_step`. The method applies `sc_step` to the input and to the input plus one,
and selects between them, by the input's low bit, at `word`, at
`(word, word)` or at `sum<word, word>`. The Core reference instead applies a
monomorphic curried selector closure. The step may allocate private cells,
which Core keeps in its store, so the result is stated with the final
store. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.ScalarMeaning

open Solcore.Synthesis.Core.Generic (CheckedPlan Variant)
open Solcore.Synthesis.Core.Aggregates (Local initializerKind?)
open Solcore.Synthesis.Source.AggregateRenderer (Binding)

/-! ### The emitted text -/

/-- The method lines after the flag, restated from the emitter: the
selection at each variant and the final `return`. -/
def genericResultLines : Variant → List String
  | .word => [
      "        let sc_selected: word = sc_select(sc_flag, sc_left_word, sc_right_word);",
      "        return uint256(sc_selected);"]
  | .pair => [
      "        let sc_left: (word, word) = (sc_left_word, sc_input);",
      "        let sc_right: (word, word) = (sc_right_word, sc_next);",
      "        let sc_selected: (word, word) = sc_select(sc_flag, sc_left, sc_right);",
      "        let sc_result: word = 0;",
      "        match (sc_selected) {",
      "            case (sc_first, sc_second) {",
      "                sc_result = sc_first + sc_second;",
      "            }", "        }",
      "        return uint256(sc_result);"]
  | .sum => [
      "        let sc_left: sum<word, word> = inl(sc_left_word);",
      "        let sc_right: sum<word, word> = inr(sc_right_word);",
      "        let sc_selected: sum<word, word> = sc_select(sc_flag, sc_left, sc_right);",
      "        let sc_result: word = 0;",
      "        match (sc_selected) {",
      "            case inl(sc_payload) {", "                sc_result = sc_payload;", "            }",
      "            case inr(sc_payload) {", "                sc_result = sc_payload + 1;", "            }",
      "        }", "        return uint256(sc_result);"]

theorem Generic.emit_success {plan : CheckedPlan} {emitted : EmittedProgram}
    (emitted_eq : Generic.emit plan = .ok emitted) :
    ∃ (names lines : List String) (entry : ARendered) (result : String),
      aggregateLoop plan.step.helpers 0 []
        (["pragma solcore;", "import * from std;", "import * from std.dispatch;"] ++
          aliasImportLines (aggregateAliases (plan.step.helpers ++ [plan.step.entry])) ++ ["",
          "function sc_select<a>(flag: bool, left: a, right: a) returns (a) {",
          "    if (flag) {", "        return left;", "    }", "    return right;", "}", ""]) =
        .ok (names, lines) ∧
      AggregateRenderer.render names .word [.word "sc_arg"] 4 0 plan.step.entry = .ok entry ∧
      entry.value = some result ∧
      emitted.source = String.intercalate "\n" (lines ++
        ["function sc_step(sc_arg: word) returns (word) {"] ++ entry.lines ++
        ["    return " ++ result ++ ";", "}", "",
          "contract " ++ Generic.contractName ++ " {",
          "    function " ++ Generic.methodName ++ "(input: uint256) public returns (uint256) {",
          "        let sc_input: word = Typedef.rep(input);",
          "        let sc_left_word: word = sc_step(sc_input);",
          "        let sc_next: word = sc_input + 1;",
          "        let sc_right_word: word = sc_step(sc_next);",
          "        let sc_flag: bool = ((sc_input & 1) == 1);"] ++
        genericResultLines plan.variant ++ ["    }", "}"]) ++ "\n" := by
  unfold Generic.emit at emitted_eq
  dsimp only at emitted_eq
  rw [forIn_aggregateLoop (fun _ _ _ _ => rfl), opcodeImports_eq] at emitted_eq
  cases loop : aggregateLoop plan.step.helpers 0 []
    (["pragma solcore;", "import * from std;", "import * from std.dispatch;"] ++
      aliasImportLines (aggregateAliases (plan.step.helpers ++ [plan.step.entry])) ++ ["",
      "function sc_select<a>(flag: bool, left: a, right: a) returns (a) {",
      "    if (flag) {", "        return left;", "    }", "    return right;", "}", ""]) with
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
              refine ⟨names, lines, rendered, result, rfl, entry, arequireValue_ok value, ?_⟩
              cases plan.variant <;> rfl

/-! ### The helpers and their names -/

/-- `aggregateLoop_spec`, also naming each printed helper `sc_fn<k>`. -/
theorem aggregateLoop_spec_named {aliases : List (String × String)} {uses : Bool}
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
      (∀ declaration ∈ declarations, ∃ index, declaration.name = Function.helperName index) ∧
      (uses = true →
        PrimitiveContext ⟨declareFunctions aliases functions declarations, aliases⟩) ∧
      MFunctionsAgree ⟨declareFunctions aliases functions declarations, aliases⟩ names'
        (bodies.foldl closureStep closures)
  | [], start, lines, names', lines', functions, closures, loop, _, primitive, agree => by
      simp only [aggregateLoop, Except.ok.injEq, Prod.mk.injEq] at loop
      obtain ⟨rfl, rfl⟩ := loop
      exact ⟨[], by simp, by simp, by simp, by simp, by simpa [declareFunctions] using primitive,
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
      obtain ⟨declarations, rest₁, rest₂, rest₃, restNamed, rest₄, rest₅⟩ :=
        aggregateLoop_spec_named aliasesOk rest (start + 1) _ names' lines' _ _ loop restAccepted
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
      refine ⟨declaration :: declarations, ?_, ?_, ?_, ?_, rest₄, rest₅⟩
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
      · intro other mem
        rcases List.mem_cons.mp mem with same | mem
        · subst same
          exact ⟨start, rfl⟩
        · exact restNamed other mem

/-- The generic selector the emitter prints before the helpers. -/
def selectorDecl : GenericDecl where
  name := "sc_select"
  typeParameters := ["a"]
  parameters := [("flag", .concrete .bool), ("left", .param "a"), ("right", .param "a")]
  resultType := .param "a"
  body := [.guard "flag" (.name "left")]
  result := .name "right"

/-- The method statements before the selection: the input, both step results
and the flag. -/
def genericPrefix : List InfixStmt :=
  [.leaf (.plain (.letDecl "sc_input" .word (.typedefRep (.name "input")))),
    .leaf (.plain (.letDecl "sc_left_word" .word (.call1 "sc_step" (.name "sc_input")))),
    .leaf (.letInfix "sc_next" .word .add (.name "sc_input") (.number 1)),
    .leaf (.plain (.letDecl "sc_right_word" .word (.call1 "sc_step" (.name "sc_next")))),
    .leaf (.plain (.letDecl "sc_flag" .bool
      (.binary .eq (.binary .bitAnd (.name "sc_input") (.number 1)) (.number 1))))]

/-- The selection and its Word result at each variant. -/
def genericSelection : Variant → List InfixStmt
  | .word =>
      [.leaf (.plain (.letDecl "sc_selected" .word (.call3 "sc_select" (.name "sc_flag")
        (.name "sc_left_word") (.name "sc_right_word"))))]
  | .pair =>
      [.leaf (.plain (.letDecl "sc_left" .wordPair
          (.tuple (.name "sc_left_word") (.name "sc_input")))),
        .leaf (.plain (.letDecl "sc_right" .wordPair
          (.tuple (.name "sc_right_word") (.name "sc_next")))),
        .leaf (.plain (.letDecl "sc_selected" .wordPair (.call3 "sc_select" (.name "sc_flag")
          (.name "sc_left") (.name "sc_right")))),
        .leaf (.plain (.letDecl "sc_result" .word (.number 0))),
        .matchPair (.name "sc_selected") "sc_first" "sc_second"
          [.assignInfix "sc_result" .add (.name "sc_first") (.name "sc_second")]]
  | .sum =>
      [.leaf (.plain (.letDecl "sc_left" .wordSum (.inl (.name "sc_left_word")))),
        .leaf (.plain (.letDecl "sc_right" .wordSum (.inr (.name "sc_right_word")))),
        .leaf (.plain (.letDecl "sc_selected" .wordSum (.call3 "sc_select" (.name "sc_flag")
          (.name "sc_left") (.name "sc_right")))),
        .leaf (.plain (.letDecl "sc_result" .word (.number 0))),
        .matchSum (.name "sc_selected") "sc_payload" [.plain (.assign "sc_result"
          (.name "sc_payload"))] "sc_payload"
          [.assignInfix "sc_result" .add (.name "sc_payload") (.number 1)]]

/-- The local the method returns. -/
def genericResultName : Variant → String
  | .word => "sc_selected"
  | .pair => "sc_result"
  | .sum => "sc_result"

/-- The generic file printed by the generic emitter. -/
def genericFile (aliases : List (String × String)) (declarations : List FunctionDecl)
    (statements : List Stmt) (value : String) (variant : Variant) : GenericFile where
  opcodeAliases := aliases
  generics := [selectorDecl]
  functions := declarations ++ [stepDecl statements value]
  contract := "SynthesizedGenerics"
  method := {
    name := "run"
    parameters := ["input"]
    body := genericPrefix ++ genericSelection variant
    result := .uint256 (.name (genericResultName variant)) }

/-- Lines are equal when their characters are. -/
theorem lines_eq_of_toList {first second : List String}
    (same : first.map String.toList = second.map String.toList) : first = second := by
  induction first generalizing second with
  | nil =>
      cases second with
      | nil => rfl
      | cons _ _ => simp at same
  | cons line rest ih =>
      cases second with
      | nil => simp at same
      | cons other more =>
          simp only [List.map_cons, List.cons.injEq] at same
          rw [String.toList_inj.mp same.1, ih same.2]

theorem selectorDecl_lines : selectorDecl.lines =
    ["function sc_select<a>(flag: bool, left: a, right: a) returns (a) {",
      "    if (flag) {", "        return left;", "    }", "    return right;", "}", ""] := by
  apply lines_eq_of_toList
  simp [selectorDecl, GenericDecl.lines, GuardStmt.listLines, GuardStmt.lines, indentLine,
    typeParameterText, genericParameterText, TypeRef.spelling, LocalType.spelling, Expr.print]

theorem toDigits_one : Nat.toDigits 10 1 = ['1'] := by decide

theorem genericMethod_lines (variant : Variant) (rest : List String) :
    InfixStmt.listLines 8 (genericPrefix ++ genericSelection variant) ++
      ("        return " ++ (Expr.uint256 (.name (genericResultName variant))).print ++ ";") ::
        rest =
    "        let sc_input: word = Typedef.rep(input);" ::
      "        let sc_left_word: word = sc_step(sc_input);" ::
      "        let sc_next: word = sc_input + 1;" ::
      "        let sc_right_word: word = sc_step(sc_next);" ::
      "        let sc_flag: bool = ((sc_input & 1) == 1);" :: (genericResultLines variant ++ rest) := by
  apply lines_eq_of_toList
  cases variant <;>
    simp [genericPrefix, genericSelection, genericResultName, genericResultLines,
      InfixStmt.listLines, InfixStmt.lines, InfixLeaf.listLines, InfixLeaf.lines, Stmt.lines,
      indentLine, infixText, Expr.print, LocalType.spelling, BinaryOp.spelling, toDigits_one]


/-! ### The Core reference -/

/-- The curried selector of `Generic.canonicalProgram`, restated: flag, left
and right. -/
def genericSelector (type : Solcore.Core.Wire.Ty) : CoreExpr :=
  .lambda .bool (.function type (.function type type))
    (.lambda type (.function type type) (.lambda type type (.ifE (.var 2) (.var 1) (.var 0))))

def genericLeft : Variant → CoreExpr
  | .word => .var 3
  | .pair => .pair (.var 3) (.var 4)
  | .sum => .inLeft .word (.var 3)

def genericRight : Variant → CoreExpr
  | .word => .var 2
  | .pair => .pair (.var 2) (.var 3)
  | .sum => .inRight .word (.var 2)

def genericResult : Variant → CoreExpr
  | .word => .var 0
  | .pair => .binary .wordAdd (.first (.var 0)) (.second (.var 0))
  | .sum =>
      .caseE (.var 0) (.var 0) (.binary .wordAdd (.var 0) (.word (Solcore.Core.Word.ofNatModulo 1)))

/-- The applied entry of `Generic.canonicalProgram`, restated: the left step
result, the input plus one, the right step result, the flag, both candidates,
the selection and the result. -/
def genericInner (variant : Variant) : CoreExpr :=
  .letE (.apply (.var 2) (.var 0))
    (.letE (.binary .wordAdd (.var 1) (.word (Solcore.Core.Word.ofNatModulo 1)))
      (.letE (.apply (.var 4) (.var 0))
        (.letE (.binary .wordEq (.binary .wordAnd (.var 3)
            (.word (Solcore.Core.Word.ofNatModulo 1))) (.word (Solcore.Core.Word.ofNatModulo 1)))
          (.letE (genericLeft variant)
            (.letE (genericRight variant)
              (.letE (.apply (.apply (.apply (.var 7) (.var 2)) (.var 1)) (.var 0))
                (genericResult variant)))))))

/-- The applied generic program, for every variant. -/
theorem genericApplied_body (step : Solcore.Synthesis.Core.Aggregates.CheckedDAG)
    (variant : Variant) (input : Solcore.Core.Word) :
    (Solcore.Synthesis.Core.Generic.appliedProgram step variant input).body =
      .apply (.letE step.program.body (.letE (genericSelector variant.payloadType)
        (.lambda .word .word (genericInner variant)))) (.word input) := by
  cases variant <;> rfl

/-- The Word the generic reference returns from its two step results. -/
def genericOutcome (variant : Variant) (flag : Bool) (input left right : Solcore.Core.Word) :
    Solcore.Core.Word :=
  match variant with
  | .word => if flag then left else right
  | .pair =>
      if flag then left.add input
      else right.add (input.add (Solcore.Core.Word.ofNatModulo 1))
  | .sum => if flag then left else right.add (Solcore.Core.Word.ofNatModulo 1)

/-- Applying the curried selector to the flag and both candidates selects
one. -/
theorem select_evaluates {environment : Solcore.Core.Environment}
    {store : Solcore.Core.Store} {flag : Bool} {first second : CoreValue}
    {p r a b c d : Solcore.Core.Ty} {captured : Solcore.Core.Environment}
    (selector : environment[7]? = some (.closure p r
      (.lambda a b (.lambda c d (.ifE (.var 2) (.var 1) (.var 0)))) captured))
    (flagAt : environment[2]? = some (.bool flag)) (firstAt : environment[1]? = some first)
    (secondAt : environment[0]? = some second) :
    Solcore.Core.Evaluates environment store
      (.apply (.apply (.apply (.var 7) (.var 2)) (.var 1)) (.var 0))
      (if flag then first else second) store := by
  refine .apply (.apply (.apply (.var selector) (.var flagAt) .lambda) (.var firstAt) .lambda)
    (.var secondAt) ?_
  cases flag
  · exact .ifFalse (.var rfl) (.var rfl)
  · exact .ifTrue (.var rfl) (.var rfl)

/-- The applied entry evaluates both step results in order, then selects
and returns the outcome. -/
theorem genericInner_evaluates (variant : Variant) {closures : List CoreValue}
    {entry : CoreExpr} {p r a b c d : Solcore.Core.Ty} {captured : Solcore.Core.Environment}
    {input left right : Solcore.Core.Word} {store store₁ store₂ : Solcore.Core.Store}
    (leftStep : Solcore.Core.Evaluates (.word input :: closures) store entry.toCore
      (.word left) store₁)
    (rightStep : Solcore.Core.Evaluates
      (.word (input.add (Solcore.Core.Word.ofNatModulo 1)) :: closures) store₁ entry.toCore
      (.word right) store₂) :
    Solcore.Core.Evaluates
      [.word input, .closure p r (.lambda a b (.lambda c d (.ifE (.var 2) (.var 1) (.var 0))))
        captured, .closure (Solcore.Core.Wire.Ty.toCore .word) (Solcore.Core.Wire.Ty.toCore .word)
        entry.toCore closures] store (genericInner variant).toCore
      (.word (genericOutcome variant
        (input.bitAnd (Solcore.Core.Word.ofNatModulo 1) == Solcore.Core.Word.ofNatModulo 1)
        input left right)) store₂ := by
  cases variant <;>
    simp only [genericInner, genericLeft, genericRight, genericResult,
      Solcore.Core.Wire.Expr.toCore, Solcore.Core.Wire.BinaryOp.toCore] <;>
    refine .letE (.apply (.var rfl) (.var rfl) leftStep) (.letE (.binary (.var rfl) .word rfl)
      (.letE (.apply (.var rfl) (.var rfl) rightStep) (.letE (.binary (.binary (.var rfl) .word rfl)
        .word rfl) ?_))) <;>
    cases flag : (input.bitAnd (Solcore.Core.Word.ofNatModulo 1) ==
      Solcore.Core.Word.ofNatModulo 1)
  · exact .letE (.var rfl) (.letE (.var rfl) (.letE (select_evaluates rfl rfl rfl rfl) (.var rfl)))
  · exact .letE (.var rfl) (.letE (.var rfl) (.letE (select_evaluates rfl rfl rfl rfl) (.var rfl)))
  · exact .letE (.pair (.var rfl) (.var rfl)) (.letE (.pair (.var rfl) (.var rfl))
      (.letE (select_evaluates rfl rfl rfl rfl)
        (.binary (.first (.var rfl)) (.second (.var rfl)) rfl)))
  · exact .letE (.pair (.var rfl) (.var rfl)) (.letE (.pair (.var rfl) (.var rfl))
      (.letE (select_evaluates rfl rfl rfl rfl)
        (.binary (.first (.var rfl)) (.second (.var rfl)) rfl)))
  · exact .letE (.inLeft (.var rfl)) (.letE (.inRight (.var rfl))
      (.letE (select_evaluates rfl rfl rfl rfl)
        (.caseRight (.var rfl) (.binary (.var rfl) .word rfl))))
  · exact .letE (.inLeft (.var rfl)) (.letE (.inRight (.var rfl))
      (.letE (select_evaluates rfl rfl rfl rfl) (.caseLeft (.var rfl) (.var rfl))))


/-! ### The source method -/

theorem evm_add_one (word : Solcore.Core.Word) :
    Evm.add word.val 1 = (word.add (Solcore.Core.Word.ofNatModulo 1)).val := by
  have := evm_add word (Solcore.Core.Word.ofNatModulo 1)
  rwa [ofNatModulo_val_small (by decide)] at this

theorem evm_flag (word : Solcore.Core.Word) :
    toBool (Evm.eq (Evm.and word.val 1) 1) =
      (word.bitAnd (Solcore.Core.Word.ofNatModulo 1) == Solcore.Core.Word.ofNatModulo 1) := by
  have conjunction := evm_and word (Solcore.Core.Word.ofNatModulo 1)
  have equality := evm_eq (word.bitAnd (Solcore.Core.Word.ofNatModulo 1))
    (Solcore.Core.Word.ofNatModulo 1)
  rw [ofNatModulo_val_small (by decide)] at conjunction equality
  rw [conjunction]
  exact equality

/-- The method computes the outcome from the two `sc_step` results and the
selector, in every call context where they mean what they compute. -/
theorem genericMethod_run (context : Context) (variant : Variant)
    (input left right : Solcore.Core.Word)
    (stepLeft : context.call "sc_step" [.word input.val] = some (.word left.val))
    (stepRight : context.call "sc_step"
      [.word (input.add (Solcore.Core.Word.ofNatModulo 1)).val] = some (.word right.val))
    (select : ∀ flag first second, context.call "sc_select" [.bool flag, first, second] =
      some (if flag then first else second)) :
    InfixMethod.run context {
        name := "run", parameters := ["input"], body := genericPrefix ++ genericSelection variant,
        result := .uint256 (.name (genericResultName variant)) } [input.val] =
      some (genericOutcome variant
        (input.bitAnd (Solcore.Core.Word.ofNatModulo 1) == Solcore.Core.Word.ofNatModulo 1)
        input left right).val := by
  have zero : 0 < Evm.modulus := by decide
  cases variant <;>
    cases flag : (input.bitAnd (Solcore.Core.Word.ofNatModulo 1) ==
      Solcore.Core.Word.ofNatModulo 1) <;>
    simp [InfixMethod.run, Method.bindParameters, word_lt_modulus, genericPrefix,
      genericSelection, genericResultName, genericOutcome, InfixStmt.execList, InfixStmt.exec,
      InfixLeaf.exec, InfixLeaf.execList, Stmt.exec, Expr.eval, Frames.lookup, Scope.get?,
      LocalType.admits, Frames.declare, Frames.assign, Scope.set?, Value.sameType,
      BinaryOp.apply, stepLeft, evm_add_one, stepRight, evm_flag, flag, select, evm_add,
      one_lt_modulus, zero]

/-! ### Preservation -/

theorem helperName_ne_select (index : Nat) : Function.helperName index ≠ "sc_select" := by
  intro same
  have chars := congrArg String.toList same
  simp [Function.helperName] at chars

/-- Declaring a function whose name is no alias or `tobool` keeps the aliases
and `tobool` reachable. -/
theorem PrimitiveContext.cons_fresh {functions : List (String × (List Value → Option Value))}
    (admitted : PrimitiveContext ⟨functions, primitiveAliases⟩) {name : String}
    (fresh : name ∉ primitiveCallees) (meaning : List Value → Option Value) :
    PrimitiveContext ⟨(name, meaning) :: functions, primitiveAliases⟩ := by
  refine ⟨fun alias mem arguments => ?_, fun arguments => ?_⟩
  · have different : name ≠ alias.2 := fun same =>
      fresh (same ▸ List.mem_cons_of_mem _ (List.mem_map_of_mem mem))
    rw [Context.call_cons_other different]
    exact admitted.1 alias mem arguments
  · have different : name ≠ "tobool" := fun same => fresh (by simp [same, primitiveCallees])
    rw [Context.call_cons_other different]
    exact admitted.2 arguments

/-- A call to a name that no later declaration has reaches the earlier
functions. -/
theorem Context.call_declareFunctions_other (aliases : List (String × String)) :
    ∀ (functions : List (String × (List Value → Option Value)))
      (declarations : List FunctionDecl) (callee : String) (arguments : List Value),
      (∀ declaration ∈ declarations, declaration.name ≠ callee) →
      Context.call ⟨declareFunctions aliases functions declarations, aliases⟩ callee arguments =
        Context.call ⟨functions, aliases⟩ callee arguments
  | _, [], _, _, _ => rfl
  | functions, declaration :: rest, callee, arguments, different => by
      simp only [declareFunctions]
      rw [Context.call_declareFunctions_other aliases _ rest callee arguments
        (fun other mem => different other (List.mem_cons_of_mem _ mem))]
      exact Context.call_cons_other (different declaration (by simp)) _ _ _ _

theorem selectorDecl_denote (context : Context) (flag : Bool) (first second : Value) :
    selectorDecl.denote context [.bool flag, first, second] =
      some (if flag then first else second) := by
  cases flag <;>
    simp [selectorDecl, GenericDecl.denote, GenericDecl.bindParameters, TypeRef.admits,
      LocalType.admits, GuardStmt.execList, GuardStmt.exec, Frames.lookup, Scope.get?,
      Expr.eval]

theorem genericBody_names_ok (variant : Variant) :
    ∀ name ∈ InfixStmt.listIdentifiers (genericPrefix ++ genericSelection variant),
      ValidIdentifier name ∧ isReserved name = false := by
  have checked : ∀ name ∈ ["sc_input", "input", "sc_left_word", "sc_step", "sc_next",
      "sc_right_word", "sc_flag", "sc_selected", "sc_select", "sc_left", "sc_right",
      "sc_result", "sc_first", "sc_second", "sc_payload"],
      validIdentifier name = true ∧ isReserved name = false := by
    decide
  have within : ∀ name ∈ InfixStmt.listIdentifiers (genericPrefix ++ genericSelection variant),
      name ∈ ["sc_input", "input", "sc_left_word", "sc_step", "sc_next", "sc_right_word",
        "sc_flag", "sc_selected", "sc_select", "sc_left", "sc_right", "sc_result", "sc_first",
        "sc_second", "sc_payload"] := by
    cases variant <;>
      simp [genericPrefix, genericSelection, InfixStmt.listIdentifiers, InfixStmt.identifiers,
        InfixLeaf.listIdentifiers, InfixLeaf.identifiers, Stmt.identifiers, Expr.identifiers]
  intro name mem
  have found := within name mem
  exact ⟨keyword_valid (checked name found).1, (checked name found).2⟩

theorem genericBody_canonical (variant : Variant) :
    ∀ statement ∈ genericPrefix ++ genericSelection variant, statement.Canonical := by
  cases variant <;> simp [genericPrefix, genericSelection, InfixStmt.Canonical]

theorem selectorDecl_ok : selectorDecl.NamesOk ∧
    ∀ name ∈ selectorDecl.identifiers, ValidIdentifier name := by
  have checked : ∀ name ∈ selectorDecl.identifiers,
      validIdentifier name = true ∧ isReserved name = false := by
    decide
  exact ⟨⟨fun name mem => (checked name mem).2, by decide⟩,
    fun name mem => keyword_valid (checked name mem).1⟩


/-- **Generic emitter preservation.** If the actual emitter succeeds, its source
text is the printing of a generic file with the selector `sc_select<a>`, one
free function per helper and the step function `sc_step`, importing the raw
opcode aliases exactly when a rendered body uses one, and parses back to it.
For every runtime input, calling `run(uint256)` under the generic source
semantics returns exactly the Word that the original Core reference, applied to
that input, returns with its final store. -/
theorem Generic.emit_preserves_meaning {plan : CheckedPlan} {emitted : EmittedProgram}
    (emitted_eq : Generic.emit plan = .ok emitted) :
    ∃ file : GenericFile, emitted.source = file.print ∧
      parseGenericSource emitted.source = some file ∧
      ∀ input : Solcore.Core.Word, ∃ word : Solcore.Core.Word,
        file.call "run" [input.val] = some word.val ∧
        CoreReturnsWithStore (plan.instantiate input).toCore word := by
  obtain ⟨names, lines, entry, result, loop, entryEquation, resultFound, source⟩ :=
    Generic.emit_success emitted_eq
  let bodies := plan.step.helpers ++ [plan.step.entry]
  let uses := bodies.any AggregateRenderer.usesOpcodeAliases
  let selectorMeaning := selectorDecl.denote ⟨[], aggregateAliases bodies⟩
  have aliasesOk : uses = true → aggregateAliases bodies = primitiveAliases := by
    intro used
    simp only [aggregateAliases]
    rw [if_pos used]
  have bodyUses : ∀ body ∈ bodies, AggregateRenderer.usesOpcodeAliases body = true →
      uses = true := fun body mem used => List.any_eq_true.mpr ⟨body, mem, used⟩
  have startPrimitive : uses = true →
      PrimitiveContext ⟨[("sc_select", selectorMeaning)], aggregateAliases bodies⟩ := by
    intro used
    rw [aliasesOk used]
    exact PrimitiveContext.cons_fresh primitiveContext_aliases (by decide) _
  obtain ⟨declarations, linesEq, namesEq, declarationsOk, declarationsNamed, primitive, agree⟩ :=
    aggregateLoop_spec_named aliasesOk plan.step.helpers 0 _ names lines
      [("sc_select", selectorMeaning)] [] loop
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
  let file := genericFile (aggregateAliases bodies) declarations statements result plan.variant
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
  have genericsOk : ∀ declaration ∈ file.generics, declaration.NamesOk ∧
      ∀ name ∈ declaration.identifiers, ValidIdentifier name := by
    intro declaration mem
    simp only [file, genericFile, List.mem_singleton] at mem
    subst mem
    exact selectorDecl_ok
  have resultNameOk : ∀ name ∈ (Expr.uint256 (.name (genericResultName plan.variant))).identifiers,
      ValidIdentifier name ∧ isReserved name = false := by
    intro name mem
    simp only [Expr.identifiers, List.mem_singleton] at mem
    subst mem
    cases plan.variant <;> exact ⟨keyword_valid (by decide), by decide⟩
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
    have functionLine : "    function " ++ Generic.methodName ++
        "(input: uint256) public returns (uint256) {" =
          "    function " ++ file.method.name ++ "(" ++
            Method.parameterText file.method.parameters ++ ") public returns (uint256) {" := by
      apply String.toList_inj.mp
      simp [file, genericFile, Method.parameterText, Generic.methodName]
    rw [source, GenericFile.print, GenericFile.lines, linesEq, functionLine]
    simp [file, genericFile, Generic.contractName, selectorDecl_lines, stepLines, bodies,
      genericMethod_lines]
  have parsed : parseGenericSource emitted.source = some file := by
    rw [printed]
    apply parseGenericSource_print
    · refine ⟨fun declaration mem => (genericsOk declaration mem).1,
        fun function mem => (functionsOk function mem).1, rfl, rfl, ?_,
        fun name mem => (genericBody_names_ok plan.variant name mem).2,
        genericBody_canonical plan.variant, fun name mem => (resultNameOk name mem).2⟩
      intro parameter mem
      simp only [file, genericFile, List.mem_singleton] at mem
      subst mem
      decide
    · refine ⟨aggregateAliases_valid bodies, fun declaration mem => (genericsOk declaration mem).2,
        fun function mem => (functionsOk function mem).2,
        keyword_valid (show validIdentifier "SynthesizedGenerics" = true by decide),
        keyword_valid (show validIdentifier "run" = true by decide), ?_,
        fun name mem => (genericBody_names_ok plan.variant name mem).1,
        fun name mem => (resultNameOk name mem).1⟩
      intro parameter mem
      simp only [file, genericFile, List.mem_singleton] at mem
      subst mem
      exact keyword_valid (by decide)
  refine ⟨file, printed, parsed, ?_⟩
  intro input
  have stepCall : ∀ arguments, file.context.call "sc_step" arguments =
      (stepDecl statements result).denote ⟨declareFunctions (aggregateAliases bodies)
        [("sc_select", selectorMeaning)] declarations, aggregateAliases bodies⟩ arguments := by
    intro arguments
    show Context.call ⟨declareFunctions (aggregateAliases bodies)
      [("sc_select", selectorMeaning)] (declarations ++ [stepDecl statements result]),
        aggregateAliases bodies⟩ "sc_step" arguments = _
    rw [declareFunctions_append_single]
    exact Context.call_cons_same _ _ _ _ _
  have selectCall : ∀ flag first second,
      file.context.call "sc_select" [.bool flag, first, second] =
        some (if flag then first else second) := by
    intro flag first second
    show Context.call ⟨declareFunctions (aggregateAliases bodies)
      [("sc_select", selectorMeaning)] (declarations ++ [stepDecl statements result]),
        aggregateAliases bodies⟩ "sc_select" [.bool flag, first, second] = _
    rw [declareFunctions_append_single,
      Context.call_cons_other (show (stepDecl statements result).name ≠ "sc_select" by
        simp [stepDecl]),
      Context.call_declareFunctions_other _ _ _ _ _ (fun declaration mem => by
        obtain ⟨index, same⟩ := declarationsNamed declaration mem
        rw [same]
        exact helperName_ne_select index),
      Context.call_cons_same]
    exact selectorDecl_denote _ flag first second
  have behaves : ∀ (argument : Solcore.Core.Word) (store : Solcore.Core.Store),
      ∃ (value : Solcore.Core.Word) (store' : Solcore.Core.Store),
        Solcore.Core.Evaluates (.word argument :: plan.step.helpers.foldl closureStep [])
          store plan.step.entry.toCore (.word value) store' ∧
        file.context.call "sc_step" [.word argument.val] = some (.word value.val) := by
    intro argument store
    obtain ⟨core, store', scope', outer', _, evaluates, represents, exec, _, _, _⟩ :=
      simulates ⟨declareFunctions (aggregateAliases bodies) [("sc_select", selectorMeaning)]
          declarations, aggregateAliases bodies⟩
        (.word argument :: plan.step.helpers.foldl closureStep []) store []
        [[("sc_arg", .word argument.val)]] primitive
        (single_abinding_agree (by simp [Frames.lookup, Scope.get?]) _ store)
        (single_abinding_cells _ _ _) (by simp) (by simpa using agree)
    rw [resultFound, Option.bind_some] at represents
    obtain ⟨_, lookup, value, rfl, rfl⟩ := represents
    refine ⟨value, store', evaluates, ?_⟩
    rw [stepCall]
    simp [stepDecl, FunctionDecl.denote, FunctionDecl.bindParameters, LocalType.admits, exec,
      Expr.eval, lookup]
  obtain ⟨left, store₁, leftCore, leftSource⟩ := behaves input []
  obtain ⟨right, store₂, rightCore, rightSource⟩ :=
    behaves (input.add (Solcore.Core.Word.ofNatModulo 1)) store₁
  refine ⟨genericOutcome plan.variant (input.bitAnd (Solcore.Core.Word.ofNatModulo 1) ==
    Solcore.Core.Word.ofNatModulo 1) input left right, ?_,
    runStateful_of_evaluates_store (store := store₂) ?_⟩
  · show (if file.method.name = "run" then file.method.run file.context [input.val]
      else none) = _
    rw [if_pos (show file.method.name = "run" from rfl)]
    exact genericMethod_run file.context plan.variant input left right leftSource rightSource
      selectCall
  · show Solcore.Core.Evaluates [] []
      (Solcore.Synthesis.Core.Generic.appliedProgram plan.step plan.variant input).body.toCore _ _
    rw [genericApplied_body]
    simp only [Solcore.Core.Wire.Expr.toCore, genericSelector]
    exact .apply (.letE (dag_evaluates plan.step.entry plan.step.helpers [] []) (.letE .lambda
      .lambda)) .word (genericInner_evaluates plan.variant leftCore rightCore)

/-- **Generic emitter preservation, on the emitted text.** -/
theorem Generic.emit_source_meaning {plan : CheckedPlan} {emitted : EmittedProgram}
    (emitted_eq : Generic.emit plan = .ok emitted) (input : Solcore.Core.Word) :
    ∃ word : Solcore.Core.Word,
      genericSourceCall emitted.source "run" [input.val] = some word.val ∧
      CoreReturnsWithStore (plan.instantiate input).toCore word := by
  obtain ⟨file, _, parsed, meaning⟩ := Generic.emit_preserves_meaning emitted_eq
  obtain ⟨word, called, core⟩ := meaning input
  exact ⟨word, by simp [genericSourceCall, parsed, called], core⟩

end Solcore.Synthesis.Source.ScalarMeaning
end

section
-- leanmerge: from Solcore.Synthesis.Source.ScalarMeaning.LoopEmitter
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
        (["pragma solcore;", "import * from std;", "import * from std.dispatch;"] ++
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
    (["pragma solcore;", "import * from std;", "import * from std.dispatch;"] ++
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
end
