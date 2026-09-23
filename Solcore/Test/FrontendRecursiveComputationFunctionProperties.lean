import Solcore.Frontend.RecursiveComputationFunction
import Solcore.Frontend.Computation
import Solcore.Frontend.RecursiveComputationReturnTree
import Solcore.Frontend.RecursiveLocalComputation
import Solcore.Frontend.RuntimeComputationFunction
import Solcore.Frontend.LocalFunctionApplication
import Solcore.Core.FuelResumptionProperties

/-! Original symbolic declarations, independent actual bindings and handwritten
paths. Operational factorization is tested separately from semantic provenance. -/
set_option autoImplicit false
namespace Tests.FrontendRecursiveComputationFunction
open Solcore Solcore.Frontend
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"RecursiveEntry", by decide⟩], by decide⟩⟩, 55⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "recursive-entry.sol"⟩, 255, 4⟩
private def named (name : String) : Syntax.TypeExpr := ⟨span, .named ⟨span, ⟨⟨⟨span, name⟩, []⟩⟩⟩ none⟩
private def types (a : Core.Ty) : TypeNameTable := [(["Fn"], .function a a), (["Payload"], a)]
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def calls : Nat → Syntax.Expr
  | 0 => ref "x"
  | n + 1 => ⟨span, .call (ref "f") ⟨span, [calls n]⟩⟩
private def callCore : Nat → Core.Expr
  | 0 => .var 1
  | n + 1 => .apply (.var 2) (callCore n)
private def body (n : Nat) : Syntax.Block := ⟨span, [⟨span, .letDecl ⟨span, "r"⟩ none (some (calls n))⟩,
  ⟨span, .expression (ref "r") true⟩, ⟨span, .returnStmt (some (ref "r"))⟩]⟩
private def parameter (name type : String) : Syntax.FunctionParameter := ⟨span, .typed none ⟨span, name⟩ (named type)⟩
private def parameters := [parameter "f" "Fn", parameter "x" "Payload", parameter "y" "Payload"]
private def entry (n : Nat) (original : Syntax.Block := body n) : Syntax.FunctionDecl := ⟨span,
  ⟨⟨span, ⟨span, "nested"⟩, none, ⟨span, parameters⟩, ⟨none, none⟩,
    some ⟨span, ⟨span, [named "Payload"]⟩⟩, none⟩, original⟩⟩
private def initial (a : Core.Ty) : LocalTypeInputs :=
  ((LocalTypeInputs.empty.bindFresh owner "f" (.function a a)).bindFresh owner "x" a).bindFresh owner "y" a
private def tailCore : Core.Expr := .letE (.var 0) (.var 1)
private def core (n : Nat) : Core.Expr := .letE (callCore n) tailCore
private def compiled (n : Nat) (a : Core.Ty) : CompiledRuntimeFunction := ⟨initial a, core n, a⟩
private theorem header (n : Nat) (a : Core.Ty) : RuntimeFunctionHeader (types a) (entry n).value.signature a :=
  ⟨rfl, rfl, rfl, rfl, .single (.named (.tail (by decide) .head))⟩
private theorem declared (a : Core.Ty) : RuntimeParametersDeclare (types a) owner parameters (initial a) :=
  .cons (.named .head) (by simp [LocalTypeInputs.empty, LocalTypeInputs.names])
    (.cons (.named (.tail (by decide) .head)) (by change "x" ∉ ["f"]; decide)
      (.cons (.named (.tail (by decide) .head)) (by change "y" ∉ ["x", "f"]; decide) .nil))
private theorem child (n : Nat) (a : Core.Ty) :
    RecursiveLocalComputationElaborates (initial a).names (initial a).context (calls n) (callCore n) a := by
  induction n with
  | zero =>
      exact .pure (.identifier (.tail (by change "y" ≠ "x"; decide) .head))
        (.var (.tail (by change (⟨owner, 2⟩ : Resolved.LocalId) ≠ ⟨owner, 1⟩; decide) .head))
        (.var (.tail (by change (⟨owner, 2⟩ : Resolved.LocalId) ≠ ⟨owner, 1⟩; decide) .head))
  | succ n ih =>
      exact .application (.pure (.identifier (.tail (by change "y" ≠ "f"; decide) (.tail (by change "x" ≠ "f"; decide) .head)))
        (.var (.tail (by change (⟨owner, 2⟩ : Resolved.LocalId) ≠ ⟨owner, 0⟩; decide) (.tail (by change (⟨owner, 1⟩ : Resolved.LocalId) ≠ ⟨owner, 0⟩; decide) .head)))
        (.var (.tail (by change (⟨owner, 2⟩ : Resolved.LocalId) ≠ ⟨owner, 0⟩; decide) (.tail (by change (⟨owner, 1⟩ : Resolved.LocalId) ≠ ⟨owner, 0⟩; decide) .head)))) ih
private theorem provenance (n : Nat) (a : Core.Ty) :
    RecursiveComputationReturnTreeElaborates (types a) owner (initial a) (body n) (core n) a := by
  have shift : (Core.Expr.var 0).weakenAt 0 = .var 1 := by simp [Core.Expr.weakenAt]
  simp only [body, core, tailCore, ← shift]
  refine .inferred (child n a) ?_
  exact .discard (.pure (.identifier .head) (.var .head) (.var .head))
    (.expression (.pure (.identifier .head) (.var .head) (.var .head)))
private theorem compilation (n : Nat) (a : Core.Ty) : RecursiveComputationFunctionCompiles (types a) owner (entry n) (compiled n a) :=
  ⟨header n a, declared a, provenance n a⟩
private abbrev Actual (a : Core.Ty) := {v : Core.Value // Core.ValueHasType v a}
private structure Capture where
  values : Core.Environment
  types : Core.Context
  typed : Core.EnvironmentHasTypes values types
private def delay : Nat → Nat → Core.Expr
  | 0, index => .var index
  | m + 1, index => .letE (.var 0) (delay m (index + 1))
private theorem delayTyped (m index : Nat) (a : Core.Ty) (rest : Core.Context) (found : (a :: rest)[index]? = some a) :
    Core.HasType (a :: rest) (delay m index) a := by
  induction m generalizing index rest with
  | zero => exact .var found
  | succ m ih => exact .letE (.var rfl) (ih (index + 1) (a :: rest) (by simpa using found))
private def closure (m : Nat) (a : Core.Ty) (cap : Capture) : Core.Value := .closure a a (delay m 0) cap.values
private theorem closureTyped (m : Nat) (a : Core.Ty) (cap : Capture) : Core.ValueHasType (closure m a cap) (.function a a) :=
  .closure cap.typed (delayTyped m 0 a cap.types rfl)
private def arguments {a : Core.Ty} (m : Nat) (cap : Capture) (x y : Actual a) : List TypedRuntimeArgument :=
  [⟨.function a a, closure m a cap, closureTyped m a cap⟩, ⟨a, x.val, x.property⟩, ⟨a, y.val, y.property⟩]
private def inputs {a : Core.Ty} (m : Nat) (cap : Capture) (x y : Actual a) : LocalInputs :=
  ((LocalInputs.empty.bindFresh owner "f" (.function a a) (closure m a cap) (closureTyped m a cap)).bindFresh owner "x" a x.val x.property).bindFresh owner "y" a y.val y.property
private def prepared {a : Core.Ty} (n m : Nat) (cap : Capture) (x y : Actual a) : PreparedRuntimeFunction := ⟨inputs m cap x y, core n, a⟩
private theorem bound {a : Core.Ty} (m : Nat) (cap : Capture) (x y : Actual a) :
    RuntimeParametersBind (types a) owner parameters (arguments m cap x y) (inputs m cap x y) :=
  .cons (.named .head) (by simp [LocalInputs.empty, LocalInputs.names])
    (.cons (.named (.tail (by decide) .head)) (by change "x" ∉ ["f"]; decide)
      (.cons (.named (.tail (by decide) .head)) (by change "y" ∉ ["x", "f"]; decide) .nil))
private theorem preparation {a : Core.Ty} (n m : Nat) (cap : Capture) (x y : Actual a) :
    RecursiveComputationFunctionPrepares (types a) owner (entry n) (arguments m cap x y) (prepared n m cap x y) :=
  ⟨header n a, bound m cap x y, provenance n a⟩
private theorem delayed (m index : Nat) (value : Core.Value) (rest : Core.Environment) (s : Core.Store) (k : List Core.Frame)
    (found : (value :: rest)[index]? = some value) :
    Core.Steps (3 * m + 1) ⟨.eval (delay m index) (value :: rest), k, s⟩ ⟨.ret value, k, s⟩ := by
  induction m generalizing index rest k with
  | zero => exact .cons (.var found) .refl
  | succ m ih =>
      simpa [delay, Nat.mul_add, Nat.add_assoc] using Core.Steps.cons .enterLet
        (.cons (.var rfl) (.cons .bindLet (ih (index + 1) (value :: rest) k (by simpa using found))))
private def charge (n m : Nat) := n * (3 * m + 5) + 1
private theorem childCost {a : Core.Ty} (n m : Nat) (cap : Capture) (x y : Actual a) (s : Core.Store) :
    RecursiveLocalComputationEvaluatesWithCost (inputs m cap x y).names (inputs m cap x y).environment s (calls n) x.val s (charge n m) := by
  induction n with
  | zero => simp only [charge, Nat.zero_mul, Nat.zero_add]; exact .pure (.identifier (.tail (by change "y" ≠ "x"; decide) .head)
      (.tail (by change (⟨owner, 2⟩ : Resolved.LocalId) ≠ ⟨owner, 1⟩; decide) .head))
  | succ n ih =>
      have count : charge (n + 1) m = 1 + charge n m + (3 * m + 1) + 3 := by simp [charge, Nat.add_mul]; omega
      rw [count]
      exact .application (.pure (.identifier (.tail (by change "y" ≠ "f"; decide) (.tail (by change "x" ≠ "f"; decide) .head))
        (.tail (by change (⟨owner, 2⟩ : Resolved.LocalId) ≠ ⟨owner, 0⟩; decide) (.tail (by change (⟨owner, 1⟩ : Resolved.LocalId) ≠ ⟨owner, 0⟩; decide) .head))))
        ih (delayed m 0 x.val cap.values s [] rfl)
private theorem childPath {a : Core.Ty} (n m : Nat) (cap : Capture) (x y : Actual a) (s : Core.Store) (k : List Core.Frame) :
    Core.Steps (charge n m) ⟨.eval (callCore n) (inputs m cap x y).environment.values, k, s⟩ ⟨.ret x.val, k, s⟩ := by
  induction n generalizing k with
  | zero => simp only [charge, Nat.zero_mul, Nat.zero_add]; exact .cons (.var rfl) .refl
  | succ n ih =>
      have count : charge (n + 1) m = 1 + charge n m + (3 * m + 1) + 3 := by simp [charge, Nat.add_mul]; omega
      rw [count]; exact CostStepComposition.apply (.cons (.var rfl) .refl) (ih _) (delayed m 0 x.val cap.values s [] rfl)
private theorem counted {a : Core.Ty} (n m : Nat) (cap : Capture) (x y : Actual a) (s : Core.Store) :
    RecursiveComputationReturnTreeEvaluatesWithCost owner (inputs m cap x y).names (inputs m cap x y).environment s (body n) x.val s (charge n m + 6) := by
  refine ComputationReturnTreeEvaluatesWithCost.inferred (ChildCost := RecursiveLocalComputationEvaluatesWithCost)
    (initializerCost := charge n m) (tailCost := 4) (childCost n m cap x y s) ?_
  exact ComputationReturnTreeEvaluatesWithCost.discard (ChildCost := RecursiveLocalComputationEvaluatesWithCost)
    (.pure (.identifier .head .head)) (.expression (.pure (.identifier .head .head)))
private theorem manual {a : Core.Ty} (n m : Nat) (cap : Capture) (x y : Actual a) (s : Core.Store) (k : List Core.Frame) :
    Core.Steps (charge n m + 6) ⟨.eval (core n) (inputs m cap x y).environment.values, k, s⟩ ⟨.ret x.val, k, s⟩ := by
  simpa [core, Nat.add_assoc] using CostStepComposition.letE (childPath n m cap x y s _)
    (.cons .enterLet (.cons (.var rfl) (.cons .bindLet (.cons (.var rfl) .refl))) :
      Core.Steps 4 ⟨.eval tailCore (x.val :: (inputs m cap x y).environment.values), k, s⟩ ⟨.ret x.val, k, s⟩)

private theorem compileSome (n : Nat) (a : Core.Ty) :
    compileRecursiveComputationFunction? (types a) owner (entry n) = some (compiled n a) :=
  (compileComputationFunction?_iff (checkChild := elaborateRecursiveLocalComputation?)
    (ChildElab := RecursiveLocalComputationElaborates) elaborateRecursiveLocalComputation?_iff).mpr (compilation n a)
private theorem prepareSome {a : Core.Ty} (n m : Nat) (cap : Capture) (x y : Actual a) :
    prepareRecursiveComputationFunction? (types a) owner (entry n) (arguments m cap x y) = some (prepared n m cap x y) :=
  (prepareComputationFunction?_iff (checkChild := elaborateRecursiveLocalComputation?)
    (ChildElab := RecursiveLocalComputationElaborates) elaborateRecursiveLocalComputation?_iff).mpr (preparation n m cap x y)

theorem exact_original_records_in_both_directions (n : Nat) (a : Core.Ty) :
    compileRecursiveComputationFunction? (types a) owner (entry n) = some (compiled n a) ∧
    RecursiveComputationFunctionCompiles (types a) owner (entry n) (compiled n a) ∧
    ∀ m cap (x y : Actual a), prepareRecursiveComputationFunction? (types a) owner (entry n) (arguments m cap x y) = some (prepared n m cap x y) ∧
      RecursiveComputationFunctionPrepares (types a) owner (entry n) (arguments m cap x y) (prepared n m cap x y) :=
  ⟨compileSome n a, (compileComputationFunction?_iff (checkChild := elaborateRecursiveLocalComputation?)
    (ChildElab := RecursiveLocalComputationElaborates) elaborateRecursiveLocalComputation?_iff).mp (compileSome n a),
    fun m cap x y => ⟨prepareSome n m cap x y, (prepareComputationFunction?_iff (checkChild := elaborateRecursiveLocalComputation?)
      (ChildElab := RecursiveLocalComputationElaborates) elaborateRecursiveLocalComputation?_iff).mp (prepareSome n m cap x y)⟩⟩

theorem full_option_projection_uses_original_order (n : Nat) (a : Core.Ty) (args : List TypedRuntimeArgument) :
    (prepareRecursiveComputationFunction? (types a) owner (entry n) args).map PreparedRuntimeFunction.toCompiled =
      if args.map (·.type) = [.function a a, a, a] then some (compiled n a) else none := by
  simpa only [compileSome n a, bind, Option.bind_some,
    show (compiled n a).inputs.context.values.reverse = [.function a a, a, a] from rfl] using
    prepareComputationFunction?_factorization elaborateRecursiveLocalComputation? (types a) owner (entry n) args
private theorem runEq {a : Core.Ty} (n m : Nat) (cap : Capture) (x y : Actual a) (fuel : Nat) (s : Core.Store) :
    runRecursiveComputationFunction? (types a) owner (entry n) (arguments m cap x y) fuel s =
      some (a, Core.runStateful fuel (.initial (core n) (inputs m cap x y).environment.values s)) := by
  simpa only [compileSome n a, bind, Option.bind_some,
    show (arguments m cap x y).map (·.type) = (compiled n a).inputs.context.values.reverse from rfl, ↓reduceIte,
    show (compiled n a).core = core n from rfl, show (compiled n a).returnType = a from rfl,
    show (arguments m cap x y).reverse.map (·.value) = (inputs m cap x y).environment.values from rfl] using
    runComputationFunction?_factorization elaborateRecursiveLocalComputation? (types a) owner (entry n) (arguments m cap x y) fuel s

theorem independent_cost_and_all_fuel_results {a : Core.Ty} (n m fuel : Nat) (cap : Capture) (x y : Actual a) (s : Core.Store) :
    RecursiveComputationReturnTreeEvaluatesWithCost owner (inputs m cap x y).names (inputs m cap x y).environment s (body n) x.val s (charge n m + 6) ∧
    (∀ k, Core.Steps (charge n m + 6) ⟨.eval (core n) (inputs m cap x y).environment.values, k, s⟩ ⟨.ret x.val, k, s⟩) ∧
    (runRecursiveComputationFunction? (types a) owner (entry n) (arguments m cap x y) fuel s = some (a, .done x.val s) ↔ charge n m + 6 ≤ fuel) ∧
    runRecursiveComputationFunction? (types a) owner (entry n) (arguments m cap x y) fuel s =
      some (a, Core.runStateful fuel (.initial (core n) ((arguments m cap x y).reverse.map (·.value)) s)) := by
  refine ⟨counted n m cap x y s, manual n m cap x y s, ?_, runEq n m cap x y fuel s⟩
  rw [runEq, Option.some.injEq, Prod.mk.injEq]; simp only [true_and]
  exact (manual n m cap x y s []).runStateful_done_iff

private def checkpoint {a : Core.Ty} (n m : Nat) (cap : Capture) (x y : Actual a) (s : Core.Store) : Core.State :=
  ⟨.ret (closure m a cap), [.applyArgument (callCore n) (inputs m cap x y).environment.values,
    .letBody tailCore (inputs m cap x y).environment.values], s⟩
theorem actual_checkpoint_keeps_the_full_result_tag {a : Core.Ty} (n m additional : Nat) (cap : Capture) (x y : Actual a) (s : Core.Store) :
    runRecursiveComputationFunction? (types a) owner (entry (n + 1)) (arguments m cap x y) 3 s = some (a, .outOfFuel (checkpoint n m cap x y s)) ∧
    Core.Steps (charge (n + 1) m + 6 - 3) (checkpoint n m cap x y s) (.final x.val s) ∧
    runRecursiveComputationFunction? (types a) owner (entry (n + 1)) (arguments m cap x y) (3 + additional) s =
      some (a, Core.runStateful additional (checkpoint n m cap x y s)) := by
  have stopped : Core.runStateful 3 (.initial (core (n + 1)) (inputs m cap x y).environment.values s) = .outOfFuel (checkpoint n m cap x y s) := rfl
  refine ⟨(runEq (n + 1) m cap x y 3 s).trans (congrArg (fun result => some (a, result)) stopped),
    ((manual (n + 1) m cap x y s []).residual_of_outOfFuel stopped).2, ?_⟩
  rw [runEq, Core.runStateful_resume stopped additional]

private def emptyCapture : Capture := ⟨[], [], .nil⟩
private def word (n : Nat) : Actual .word := ⟨.word (Core.Word.ofNatModulo n), .word⟩
theorem same_typed_actual_swap_is_accepted_and_changes_the_result (s : Core.Store) :
    (prepared 2 0 emptyCapture (word 9) (word 14)).toCompiled = (prepared 2 0 emptyCapture (word 14) (word 9)).toCompiled ∧
    prepareRecursiveComputationFunction? (types .word) owner (entry 2) (arguments 0 emptyCapture (word 9) (word 14)) = some (prepared 2 0 emptyCapture (word 9) (word 14)) ∧
    prepareRecursiveComputationFunction? (types .word) owner (entry 2) (arguments 0 emptyCapture (word 14) (word 9)) = some (prepared 2 0 emptyCapture (word 14) (word 9)) ∧
    runRecursiveComputationFunction? (types .word) owner (entry 2) (arguments 0 emptyCapture (word 9) (word 14)) 17 s = some (.word, .done (word 9).val s) ∧
    runRecursiveComputationFunction? (types .word) owner (entry 2) (arguments 0 emptyCapture (word 14) (word 9)) 17 s = some (.word, .done (word 14).val s) ∧
    (word 9).val ≠ (word 14).val := by
  refine ⟨rfl, prepareSome _ _ _ _ _, prepareSome _ _ _ _ _,
    (independent_cost_and_all_fuel_results 2 0 17 _ _ _ s).2.2.1.mpr (by decide),
    (independent_cost_and_all_fuel_results 2 0 17 _ _ _ s).2.2.1.mpr (by decide), ?_⟩
  intro same; have numbers := congrArg Fin.val (Core.Value.word.inj same); change 9 = 14 at numbers; cases numbers

theorem nominal_compilation_is_value_free (n : Nat) (nominal : Core.DataTypeId) :
    compileRecursiveComputationFunction? (types (.namedData nominal)) owner (entry n) = some (compiled n (.namedData nominal)) ∧
    ¬ ∃ value, Core.ValueHasType value (.namedData nominal) := by
  refine ⟨compileSome n _, ?_⟩
  rintro ⟨value, typed⟩; cases typed with
  | constructed found _ => simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found

theorem same_source_with_different_actual_body_costs (limit : Nat) (s : Core.Store) :
    ∃ m, RecursiveComputationReturnTreeEvaluatesWithCost owner (inputs m emptyCapture (word 9) (word 14)).names
      (inputs m emptyCapture (word 9) (word 14)).environment s (body 2) (word 9).val s (charge 2 m + 6) ∧ limit < charge 2 m + 6 :=
  ⟨limit, counted 2 limit _ _ _ s, by simp [charge]; omega⟩

theorem independently_accepted_old_entry_embeds (a : Core.Ty) :
    compileRuntimeComputationFunction? (types a) owner (entry 0) = some (compiled 0 a) ∧
    compileRecursiveComputationFunction? (types a) owner (entry 0) = some (compiled 0 a) := by
  have oldChild : LocalComputationElaborates (initial a).names (initial a).context (calls 0) (callCore 0) a := by
    cases child 0 a with
    | pure resolution lowered typing => exact .pure resolution lowered typing
  have oldBody : LocalComputationReturnTreeElaborates (types a) owner (initial a) (body 0) (core 0) a := by
    have shift : (Core.Expr.var 0).weakenAt 0 = .var 1 := by simp [Core.Expr.weakenAt]
    simp only [body, core, tailCore, ← shift]
    refine .inferred (by change "r" ∉ ["y", "x", "f"]; decide) oldChild ?_
    exact .discard (.pure (.identifier .head) (.var .head) (.var .head))
      (.expression (.pure (.identifier .head) (.var .head) (.var .head)))
  exact ⟨compileRuntimeComputationFunction?_iff.mpr ⟨header 0 a, declared a, oldBody⟩,
    (compileComputationFunction?_iff (checkChild := elaborateRecursiveLocalComputation?)
      (ChildElab := RecursiveLocalComputationElaborates) elaborateRecursiveLocalComputation?_iff).mpr
        ⟨header 0 a, declared a, oldBody.toRecursiveComputationReturnTree⟩⟩

theorem data_only_record_does_not_supply_provenance (n : Nat) (a : Core.Ty) :
    Core.HasType (initial a).context.values (.var 0) a ∧
    ¬ RecursiveComputationFunctionCompiles (types a) owner (entry n) { compiled n a with core := .var 0 } := by
  refine ⟨.var rfl, ?_⟩
  intro forged
  have accepted := (compileComputationFunction?_iff (checkChild := elaborateRecursiveLocalComputation?)
    (ChildElab := RecursiveLocalComputationElaborates) elaborateRecursiveLocalComputation?_iff).mpr forged
  have impossible := congrArg CompiledRuntimeFunction.core (Option.some.inj (accepted.symm.trans (compileSome n a)))
  cases impossible

private def invalidChecker : LocalNameTable → Resolved.Context → Syntax.Expr → Option (Core.Expr × Core.Ty) := fun _ _ _ => some (.var 999, .word)
private def invalidEntry := entry 0 ⟨span, [⟨span, .returnStmt (some (ref "x"))⟩]⟩
private def invalidCompiled : CompiledRuntimeFunction := ⟨initial .word, .var 999, .word⟩
private theorem invalidCompiledSome : compileComputationFunction? invalidChecker (types .word) owner invalidEntry = some invalidCompiled := by
  have h : interpretRuntimeFunctionHeader? (types .word) invalidEntry.value.signature = some .word := interpretRuntimeFunctionHeader?_iff.mpr (header 0 .word)
  simp only [compileComputationFunction?, h, bind, Option.bind_some]
  simp [invalidEntry, entry, (declared .word).complete, elaborateComputationReturnTree?, invalidChecker, invalidCompiled]
/-- These are operational equalities for a deliberately invalid checker, not source semantics. -/
theorem arbitrary_checker_factorization_keeps_faults (s : Core.Store) :
    (prepareComputationFunction? invalidChecker (types .word) owner invalidEntry (arguments 0 emptyCapture (word 9) (word 14))).map PreparedRuntimeFunction.toCompiled = some invalidCompiled ∧
    runComputationFunction? invalidChecker (types .word) owner invalidEntry (arguments 0 emptyCapture (word 9) (word 14)) 1 s =
      some (.word, .fault (.unboundVariable 999) (.initial (.var 999) (inputs 0 emptyCapture (word 9) (word 14)).environment.values s)) := by
  constructor
  · rw [prepareComputationFunction?_factorization, invalidCompiledSome]; rfl
  · rw [runComputationFunction?_factorization, invalidCompiledSome]; rfl

end Tests.FrontendRecursiveComputationFunction
