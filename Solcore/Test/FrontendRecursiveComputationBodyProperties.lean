import Solcore.Frontend.RecursiveComputationReturnTreeEmbeddingProperties
import Solcore.Frontend.ComputationReturnTreeProperties
import Solcore.Frontend.ComputationReturnTreeTypingProperties
import Solcore.Frontend.ComputationReturnTreeEvaluationProperties
import Solcore.Frontend.ComputationReturnTreeExecutionProperties
import Solcore.Frontend.ComputationReturnTreeCostProperties
import Solcore.Frontend.ComputationBodyFragmentInsertionPaths
import Solcore.Frontend.RecursiveLocalComputationProperties
import Solcore.Frontend.RecursiveLocalComputationExecutionProperties
import Solcore.Frontend.RecursiveLocalComputationFragmentProperties
import Solcore.Frontend.RecursiveLocalComputationFragmentInsertionProperties
import Solcore.Frontend.RecursiveLocalComputationFragmentInsertionPaths
import Solcore.Core.FuelResumptionProperties

/-! Independent original mixed-body evidence instantiates the separate child
contracts. Hidden Core binders do not become source names or actual captures. -/
set_option autoImplicit false
namespace Tests.FrontendRecursiveComputationBody
open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"Shared", by decide⟩], by decide⟩⟩, 54⟩
private def fid : Resolved.LocalId := ⟨owner, 17⟩
private def xid : Resolved.LocalId := ⟨{ owner with declarationIndex := 91 }, 999⟩
private def cid : Resolved.LocalId := ⟨owner, 2⟩
private def gid : Resolved.LocalId := ⟨owner, 8⟩
private def rid : Resolved.LocalId := ⟨owner, 18⟩
private def inputs (a : Core.Ty) : LocalTypeInputs :=
  ⟨[⟨"x", xid, a⟩, ⟨"f", fid, .function a a⟩, ⟨"c", cid, .bool⟩, ⟨"f", gid, .unit⟩], by change [xid, fid, cid, gid].Nodup; decide⟩
private def types (a : Core.Ty) : TypeNameTable := [(["Payload"], a)]
private def span : Syntax.SourceSpan := ⟨⟨.main, "shared-body.sol"⟩, 254, 3⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def annotation : Syntax.TypeExpr := ⟨span, .named ⟨span, ⟨⟨⟨span, "Payload"⟩, []⟩⟩⟩ none⟩
private def calls : Nat → Syntax.Expr
  | 0 => ref "x"
  | n + 1 => ⟨span, .call (ref "f") ⟨span, [calls n]⟩⟩
private def callCore : Nat → Core.Expr
  | 0 => .var 0
  | n + 1 => .apply (.var 1) (callCore n)
private def returned (name : String) : Syntax.Block := ⟨span, [⟨span, .returnStmt (some (ref name))⟩]⟩
private def tail : List Syntax.Statement := [⟨span, .expression (ref "r") true⟩,
  ⟨span, .ifThen (ref "c") (returned "r") (some (returned "x"))⟩]
private def body (annotated : Bool) (n : Nat) : Syntax.Block :=
  ⟨span, [⟨span, .block (⟨span, .letDecl ⟨span, "r"⟩ (if annotated then some annotation else none) (some (calls n))⟩ :: tail)⟩]⟩
private def tailCore : Core.Expr := .letE (.var 0) (.ifE (.var 4) (.var 1) (.var 2))
private def core (n : Nat) : Core.Expr := .letE (callCore n) tailCore
private theorem childElab (n : Nat) (a : Core.Ty) :
    RecursiveLocalComputationElaborates (inputs a).names (inputs a).context (calls n) (callCore n) a := by
  induction n with
  | zero => exact .pure (.identifier .head) (.var .head) (.var .head)
  | succ n ih => exact .application (.pure (.identifier (.tail (by change "x" ≠ "f"; decide) .head))
      (.var (.tail (by change xid ≠ fid; decide) .head)) (.var (.tail (by change xid ≠ fid; decide) .head))) ih
private theorem tailElab (a : Core.Ty) :
    RecursiveComputationReturnTreeElaborates (types a) owner ((inputs a).bindFresh owner "r" a) ⟨span, tail⟩ tailCore a := by
  have branch : RecursiveComputationReturnTreeElaborates (types a) owner ((inputs a).bindFresh owner "r" a)
      ⟨span, [⟨span, .ifThen (ref "c") (returned "r") (some (returned "x"))⟩]⟩ (.ifE (.var 3) (.var 0) (.var 1)) a := by
    exact .conditional (.pure (.identifier (.tail (by change "r" ≠ "c"; decide) (.tail (by change "x" ≠ "c"; decide) (.tail (by change "f" ≠ "c"; decide) .head))))
      (.var (.tail (by change rid ≠ cid; decide) (.tail (by change xid ≠ cid; decide) (.tail (by change fid ≠ cid; decide) .head))))
      (.var (.tail (by change rid ≠ cid; decide) (.tail (by change xid ≠ cid; decide) (.tail (by change fid ≠ cid; decide) .head)))))
      (computationBlockPreservesNames_iff.mp (by simp only [returned, computationBlockPreservesNames]))
      (.expression (.pure (.identifier .head) (.var .head) (.var .head)))
      (.expression (.pure (.identifier (.tail (by change "r" ≠ "x"; decide) .head)) (.var (.tail (by change rid ≠ xid; decide) .head))
        (.var (.tail (by change rid ≠ xid; decide) .head))))
  have first : RecursiveLocalComputationElaborates ((inputs a).bindFresh owner "r" a).names
      ((inputs a).bindFresh owner "r" a).context (ref "r") (.var 0) a := .pure (.identifier .head) (.var .head) (.var .head)
  simpa [tail, tailCore, Core.Expr.weakenAt] using ComputationReturnTreeElaborates.discard first branch
private theorem provenance (annotated : Bool) (n : Nat) (a : Core.Ty) :
    RecursiveComputationReturnTreeElaborates (types a) owner (inputs a) (body annotated n) (core n) a := by
  cases annotated
  · exact .block (.inferred (childElab n a) (tailElab a))
  · exact .block (.binding (.named .head) (childElab n a) (tailElab a))
private def delay : Nat → Nat → Core.Expr
  | 0, index => .var index
  | n + 1, index => .letE (.var 0) (delay n (index + 1))
private def env (m : Nat) (value : Core.Value) (captures : Core.Environment) (flag : Bool) : Resolved.Environment :=
  [(xid, value), (fid, .closure .unit .unit (delay m 0) captures), (cid, .bool flag), (gid, .unit)]
private def charge (n m : Nat) : Nat := n * (3 * m + 5) + 1
private theorem delayed (m index : Nat) (value : Core.Value) (rest : Core.Environment) (store : Core.Store)
    (k : List Core.Frame) (found : (value :: rest)[index]? = some value) :
    Core.Steps (3 * m + 1) ⟨.eval (delay m index) (value :: rest), k, store⟩ ⟨.ret value, k, store⟩ := by
  induction m generalizing index rest k with
  | zero => exact .cons (.var found) .refl
  | succ m ih =>
      simpa [delay, Nat.mul_add, Nat.add_assoc] using Core.Steps.cons .enterLet
        (.cons (.var rfl) (.cons .bindLet (ih (index + 1) (value :: rest) k (by simpa using found))))
private theorem childCost (n m : Nat) (value : Core.Value) (captures : Core.Environment) (flag : Bool) (store : Core.Store) :
    RecursiveLocalComputationEvaluatesWithCost (inputs .unit).names (env m value captures flag) store (calls n) value store (charge n m) := by
  induction n with
  | zero => simp only [charge, Nat.zero_mul, Nat.zero_add]; exact .pure (.identifier .head .head)
  | succ n ih =>
      have count : charge (n + 1) m = 1 + charge n m + (3 * m + 1) + 3 := by simp [charge, Nat.add_mul]; omega
      rw [count]
      exact .application (.pure (.identifier (.tail (by decide) .head) (.tail (by decide) .head))) ih (delayed m 0 value captures store [] rfl)
private theorem childPath (n m : Nat) (value : Core.Value) (captures : Core.Environment) (flag : Bool) (store : Core.Store) (k : List Core.Frame) :
    Core.Steps (charge n m) ⟨.eval (callCore n) (env m value captures flag).values, k, store⟩ ⟨.ret value, k, store⟩ := by
  induction n generalizing k with
  | zero => simp only [charge, Nat.zero_mul, Nat.zero_add]; exact .cons (.var rfl) .refl
  | succ n ih =>
      have count : charge (n + 1) m = 1 + charge n m + (3 * m + 1) + 3 := by simp [charge, Nat.add_mul]; omega
      rw [count]
      exact CostStepComposition.apply (.cons (.var rfl) .refl) (ih _) (delayed m 0 value captures store [] rfl)
private theorem tailCost (m : Nat) (value : Core.Value) (captures : Core.Environment) (flag : Bool) (store : Core.Store) :
    RecursiveComputationReturnTreeEvaluatesWithCost owner (("r", rid) :: (inputs .unit).names)
      ((rid, value) :: env m value captures flag) store ⟨span, tail⟩ value store 7 := by
  refine ComputationReturnTreeEvaluatesWithCost.discard (ChildCost := RecursiveLocalComputationEvaluatesWithCost)
    (expressionCost := 1) (tailCost := 4) (middleStore := store) (discardedValue := value) ?_ ?_
  · exact .pure (.identifier .head .head)
  cases flag
  · refine ComputationReturnTreeEvaluatesWithCost.ifFalse (ChildCost := RecursiveLocalComputationEvaluatesWithCost)
      (middleStore := store) (conditionCost := 1) (branchCost := 1) ?_ ?_
    · exact .pure (.identifier (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))
        (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
    · exact .expression (.pure (.identifier (.tail (by decide) .head) (.tail (by decide) .head)))
  · refine ComputationReturnTreeEvaluatesWithCost.ifTrue (ChildCost := RecursiveLocalComputationEvaluatesWithCost)
      (middleStore := store) (conditionCost := 1) (branchCost := 1) ?_ ?_
    · exact .pure (.identifier (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))
        (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
    · exact .expression (.pure (.identifier .head .head))
private theorem counted (annotated : Bool) (n m : Nat) (value : Core.Value) (captures : Core.Environment) (flag : Bool) (store : Core.Store) :
    RecursiveComputationReturnTreeEvaluatesWithCost owner (inputs .unit).names (env m value captures flag)
      store (body annotated n) value store (charge n m + 9) := by
  cases annotated <;> apply ComputationReturnTreeEvaluatesWithCost.block
  · exact .inferred (childCost n m value captures flag store) (tailCost m value captures flag store)
  · exact .binding (childCost n m value captures flag store) (tailCost m value captures flag store)
private theorem manual (n m : Nat) (value : Core.Value) (captures : Core.Environment) (flag : Bool) (store : Core.Store) (k : List Core.Frame) :
    Core.Steps (charge n m + 9) ⟨.eval (core n) (env m value captures flag).values, k, store⟩ ⟨.ret value, k, store⟩ := by
  have tailPath : Core.Steps 7 ⟨.eval tailCore (value :: (env m value captures flag).values), k, store⟩ ⟨.ret value, k, store⟩ := by
    cases flag <;> exact .cons .enterLet (.cons (.var rfl) (.cons .bindLet
      (.cons .enterIf (.cons (.var rfl) (.cons (by constructor) (.cons (.var rfl) .refl))))))
  simpa [core, Nat.add_assoc] using CostStepComposition.letE (childPath n m value captures flag store _) tailPath

theorem independent_original_body_and_actual_cost (annotated : Bool) (n m : Nat) (a : Core.Ty)
    (value : Core.Value) (captures : Core.Environment) (flag : Bool) (store : Core.Store) :
    RecursiveComputationReturnTreeElaborates (types a) owner (inputs a) (body annotated n) (core n) a ∧
    RecursiveComputationReturnTreeEvaluatesWithCost owner (inputs .unit).names (env m value captures flag)
      store (body annotated n) value store (charge n m + 9) ∧
    ∀ k, Core.Steps (charge n m + 9) ⟨.eval (core n) (env m value captures flag).values, k, store⟩ ⟨.ret value, k, store⟩ :=
  ⟨provenance annotated n a, counted annotated n m value captures flag store, manual n m value captures flag store⟩

theorem independent_static_contracts (annotated : Bool) (n : Nat) (a : Core.Ty) :
    elaborateRecursiveComputationReturnTree? (types a) owner (inputs a) (body annotated n) = some (core n, a) ∧
    RecursiveComputationReturnTreeHasType (types a) owner (inputs a) (body annotated n) a ∧
    Core.HasType (inputs a).context.values (core n) a :=
  ⟨(elaborateComputationReturnTree?_iff elaborateRecursiveLocalComputation?_iff).mpr (provenance annotated n a),
    (computationReturnTreeHasType_iff_elaborates recursiveLocalComputationHasType_iff_elaborates).mpr ⟨_, provenance annotated n a⟩,
    (provenance annotated n a).core_hasType RecursiveLocalComputationElaborates.core_hasType⟩

theorem sparse_foreign_ids_and_first_spelling (a : Core.Ty) :
    Resolved.freshLocalId owner (inputs a).ids = rid ∧
    (inputs a).names.lookup? "f" = some fid ∧ ((inputs a).bindFresh owner "r" a).ids = rid :: (inputs a).ids := by
  exact ⟨rfl, rfl, rfl⟩

theorem raw_cost_without_runtime_typing (annotated : Bool) (n m : Nat) (v : Core.Value) (cap : Core.Environment) (flag : Bool) (s : Core.Store) :
    RecursiveComputationReturnTreeEvaluates owner (inputs .unit).names (env m v cap flag) s (body annotated n) v s ∧
    ∀ w t c, RecursiveComputationReturnTreeEvaluatesWithCost owner (inputs .unit).names (env m v cap flag) s (body annotated n) w t c →
      v = w ∧ s = t ∧ charge n m + 9 = c := by
  have known := counted annotated n m v cap flag s
  exact ⟨(computationReturnTreeEvaluates_iff_exists_cost recursiveLocalComputationEvaluates_iff_exists_cost).mpr ⟨_, known⟩,
    fun _ _ _ other => ComputationReturnTreeEvaluatesWithCost.deterministic (ChildCost := RecursiveLocalComputationEvaluatesWithCost)
      RecursiveLocalComputationEvaluatesWithCost.deterministic known other⟩

theorem separate_child_execution_laws (annotated : Bool) (n m : Nat) (v : Core.Value) (cap : Core.Environment) (flag : Bool) (s : Core.Store) :
    Core.Evaluates (env m v cap flag).values s (core n) v s ∧
    RecursiveComputationReturnTreeEvaluatesWithCost owner (inputs .unit).names (env m v cap flag) s (body annotated n) v s (charge n m + 9) ∧
    ∀ k, Core.Steps (charge n m + 9) ⟨.eval (core n) (env m v cap flag).values, k, s⟩ ⟨.ret v, k, s⟩ := by
  have e := provenance annotated n .unit
  have rawIff := ComputationReturnTreeElaborates.evaluates_iff (F := RecursiveLocalComputationFragment)
    (ChildElab := RecursiveLocalComputationElaborates) (ChildEval := RecursiveLocalComputationEvaluates)
    RecursiveLocalComputationElaborates.core_fragment RecursiveLocalComputationFragment.weakenAt
    RecursiveLocalComputationFragment.evaluates_insert_iff RecursiveLocalComputationElaborates.evaluates_iff e (environment := env m v cap flag) rfl
    (initialStore := s) (finalStore := s) (value := v)
  have costIff := ComputationReturnTreeElaborates.evaluatesWithCost_iff_steps (F := RecursiveLocalComputationFragment)
    (ChildElab := RecursiveLocalComputationElaborates) (ChildEval := RecursiveLocalComputationEvaluates) (ChildCost := RecursiveLocalComputationEvaluatesWithCost)
    RecursiveLocalComputationElaborates.core_fragment RecursiveLocalComputationFragment.weakenAt
    RecursiveLocalComputationFragment.evaluates_insert_iff RecursiveLocalComputationElaborates.evaluates_iff
    recursiveLocalComputationEvaluates_iff_exists_cost RecursiveLocalComputationFragment.insertion_paths
    RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation e (environment := env m v cap flag) rfl
    (initialStore := s) (finalStore := s) (value := v) (cost := charge n m + 9)
  exact ⟨rawIff.mp (raw_cost_without_runtime_typing annotated n m v cap flag s).1,
    costIff.mpr (manual n m v cap flag s []), fun k =>
      ComputationReturnTreeEvaluatesWithCost.toStepsWithContinuation (F := RecursiveLocalComputationFragment)
        (ChildElab := RecursiveLocalComputationElaborates) (ChildCost := RecursiveLocalComputationEvaluatesWithCost)
        RecursiveLocalComputationElaborates.core_fragment RecursiveLocalComputationFragment.weakenAt
        RecursiveLocalComputationFragment.insertion_paths RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation
        (counted annotated n m v cap flag s) e rfl k⟩

theorem arbitrary_inserted_value_and_kept_prefix (n m : Nat) (v inserted : Core.Value) (cap : Core.Environment) (flag : Bool) (s : Core.Store)
    (leading suffix : Core.Environment) (split : leading ++ suffix = (env m v cap flag).values) :
    ComputationBodyFragment RecursiveLocalComputationFragment ((core n).weakenAt leading.length) ∧
    (Core.Evaluates (leading ++ inserted :: suffix) s ((core n).weakenAt leading.length) v s ↔ Core.Evaluates (leading ++ suffix) s (core n) v s) ∧
    ∀ k, Core.Steps (charge n m + 9) ⟨.eval ((core n).weakenAt leading.length) (leading ++ inserted :: suffix), k, s⟩ ⟨.ret v, k, s⟩ := by
  have fragment := ComputationReturnTreeElaborates.core_fragment (ChildElab := RecursiveLocalComputationElaborates) (F := RecursiveLocalComputationFragment)
    RecursiveLocalComputationElaborates.core_fragment RecursiveLocalComputationFragment.weakenAt (provenance false n .unit)
  have original : Core.Steps (charge n m + 9) (.initial (core n) (leading ++ suffix) s) (.final v s) := split ▸ manual n m v cap flag s []
  obtain ⟨actual, paths⟩ := ComputationBodyFragment.insertion_paths RecursiveLocalComputationFragment.insertion_paths fragment leading suffix inserted (Core.steps_from_initial_sound original)
  have same := (original.final_unique (paths []).1).1
  exact ⟨fragment.weakenAt RecursiveLocalComputationFragment.weakenAt _,
    fragment.evaluates_insert_iff RecursiveLocalComputationFragment.evaluates_insert_iff leading suffix inserted,
    fun k => same.symm ▸ (paths k).2⟩

theorem all_fuel_and_genuine_checkpoint (n m fuel spent : Nat) (v : Core.Value) (cap : Core.Environment) (flag : Bool) (s : Core.Store)
    (checkpoint : Core.State) (genuine : Core.runStateful spent (.initial (core n) (env m v cap flag).values s) = .outOfFuel checkpoint) :
    (Core.runStateful fuel (.initial (core n) (env m v cap flag).values s) = .done v s ↔ charge n m + 9 ≤ fuel) ∧
    Core.Steps (charge n m + 9 - spent) checkpoint (.final v s) ∧
    ∀ additional, Core.runStateful additional checkpoint = Core.runStateful (spent + additional) (.initial (core n) (env m v cap flag).values s) :=
  ⟨(manual n m v cap flag s []).runStateful_done_iff, ((manual n m v cap flag s []).residual_of_outOfFuel genuine).2,
    Core.runStateful_resume genuine⟩

private def oldBody : Syntax.Block := ⟨span, [⟨span, .expression ⟨span, .tuple ⟨span, []⟩⟩ true⟩, ⟨span, .returnStmt none⟩]⟩
theorem old_exact_evidence_embeds_unchanged (a : Core.Ty) (environment : Resolved.Environment) (s : Core.Store) :
    RecursiveComputationReturnTreeElaborates (types a) owner (inputs a) oldBody (.letE .unit .unit) .unit ∧
    RecursiveComputationReturnTreeEvaluatesWithCost owner (inputs a).names environment s oldBody .unit s 4 := by
  have old : LocalComputationReturnTreeElaborates (types a) owner (inputs a) oldBody (.letE .unit .unit) .unit := by
    simpa [oldBody, Core.Expr.weakenAt] using LocalComputationReturnTreeElaborates.discard
      (blockSpan := span) (statementSpan := span) (types := types a) (owner := owner) (inputs := inputs a)
      (.pure (.unit (span := span) (tupleSpan := span)) .unit .unit) (.bare (returnSpan := span))
  have actual : LocalComputationReturnTreeEvaluatesWithCost owner (inputs a).names environment s oldBody .unit s 4 := .discard (.pure .unit) .bare
  exact ⟨old.toRecursiveComputationReturnTree, actual.toRecursiveComputationReturnTree⟩

theorem same_typed_core_is_not_provenance (annotated : Bool) (n : Nat) (a : Core.Ty) :
    Core.HasType (inputs a).context.values (.var 0) a ∧
    ¬ RecursiveComputationReturnTreeElaborates (types a) owner (inputs a) (body annotated n) (.var 0) a := by
  refine ⟨.var rfl, ?_⟩
  intro forged
  have bad := (elaborateComputationReturnTree?_iff (checkChild := elaborateRecursiveLocalComputation?)
    (ChildElab := RecursiveLocalComputationElaborates) elaborateRecursiveLocalComputation?_iff).mpr forged
  change elaborateRecursiveComputationReturnTree? (types a) owner (inputs a) (body annotated n) = some (.var 0, a) at bad
  rw [(independent_static_contracts annotated n a).1] at bad
  cases bad

theorem missing_annotation_is_static_not_raw (n m : Nat) (v : Core.Value) (cap : Core.Environment) (flag : Bool) (s : Core.Store) :
    elaborateRecursiveComputationReturnTree? [] owner (inputs .unit) (body true n) = none ∧
    RecursiveComputationReturnTreeEvaluatesWithCost owner (inputs .unit).names (env m v cap flag) s (body true n) v s (charge n m + 9) := by
  refine ⟨?_, counted true n m v cap flag s⟩
  simp [elaborateRecursiveComputationReturnTree?, body, elaborateComputationReturnTree?, inputs,
    LocalTypeInputs.names, annotation, interpretStructuralType?, TypeNameTable.lookup?]

private def checkpoint (n m : Nat) (v : Core.Value) (cap : Core.Environment) (flag : Bool) (s : Core.Store) : Core.State :=
  ⟨.ret (.closure .unit .unit (delay m 0) cap),
    [.applyArgument (callCore n) (env m v cap flag).values, .letBody tailCore (env m v cap flag).values], s⟩
theorem actual_checkpoint_before_nested_argument (n m : Nat) (v : Core.Value) (cap : Core.Environment) (flag : Bool) (s : Core.Store) :
    Core.runStateful 3 (.initial (core (n + 1)) (env m v cap flag).values s) = .outOfFuel (checkpoint n m v cap flag s) ∧
    Core.Steps (charge (n + 1) m + 9 - 3) (checkpoint n m v cap flag s) (.final v s) ∧
    ∀ additional, Core.runStateful additional (checkpoint n m v cap flag s) =
      Core.runStateful (3 + additional) (.initial (core (n + 1)) (env m v cap flag).values s) := by
  have genuine : Core.runStateful 3 (.initial (core (n + 1)) (env m v cap flag).values s) = .outOfFuel (checkpoint n m v cap flag s) := rfl
  exact ⟨genuine, ((manual (n + 1) m v cap flag s []).residual_of_outOfFuel genuine).2, Core.runStateful_resume genuine⟩

theorem same_source_has_no_capture_body_cost_bound (limit : Nat) (s : Core.Store) :
    ∃ m, RecursiveComputationReturnTreeEvaluatesWithCost owner (inputs .unit).names (env m .unit [] true) s (body false 1) .unit s (charge 1 m + 9) ∧
      limit < charge 1 m + 9 := by
  exact ⟨limit, counted false 1 limit .unit [] true s, by simp [charge]; omega⟩

theorem continuation_endpoint_is_not_a_safety_claim (n m : Nat) (s : Core.Store) :
    Core.Steps (charge n m + 9) ⟨.eval (core n) (env m .unit [] true).values, [.unaryApply .wordNot], s⟩
      ⟨.ret .unit, [.unaryApply .wordNot], s⟩ ∧
    Core.runStateful 0 ⟨.ret .unit, [.unaryApply .wordNot], s⟩ =
      .fault (.invalidUnaryOperand .wordNot .unit) ⟨.ret .unit, [.unaryApply .wordNot], s⟩ :=
  ⟨manual n m .unit [] true s _, rfl⟩

end Tests.FrontendRecursiveComputationBody
