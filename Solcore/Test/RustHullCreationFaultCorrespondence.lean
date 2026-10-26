import Solcore.Test.RustHullCreationAdmittedCorrespondence

/-! Admitted CREATE and CREATE2 attempts that fault after the creator nonce
advance reach the actual lowering, transport and installed create handler
through the call-mode public theorem. Each scenario stores the attempt's result
word and returns it; the attempt faults first and stops the frame. A target
absent from an incomplete world and a recorded target with unknown code are
language fault 7. An endowment that would overflow the target balance is
language fault 12. The faults restore the checkpoint taken after the nonce
advance. -/
set_option autoImplicit false
set_option maxRecDepth 8192
namespace Tests.RustHullCreationFaultCorrespondence
open Solcore Solcore.Frontend.RustHull Correspondence DerivationCorrespondence
open Tests.RustHullCreationAdmittedCorrespondence (emptyHash createTarget create2Target createTarget_derived
  create2Target_derived rootBytes)

inductive Scenario where
  | absent | unknownCode | overflow | overflow2
  deriving DecidableEq, Repr

private abbrev w := Core.Word.ofNatModulo
private def word (text : String) : Expr := ⟨.word, .word text, none⟩
private def call (type : Ty) (name : String) (arguments : List Expr) : Expr := ⟨type, .call name arguments, none⟩
private def expression (value : Expr) : Stmt := ⟨.expression value, none⟩

def target : Scenario → Core.Word
  | .absent | .overflow => createTarget
  | .unknownCode | .overflow2 => create2Target
/-- The CREATE2 target is recorded with a zero nonce and unknown code. -/
def occupant : Scenario → List AccountState.Account
  | .unknownCode => [{address := create2Target, code := none}]
  | _ => []
/-- The overflow targets already hold the largest balance. -/
def held : Scenario → Core.WordMapping.Entries
  | .overflow => [(createTarget, w (Core.wordModulus - 1))]
  | .overflow2 => [(create2Target, w (Core.wordModulus - 1))]
  | _ => []
def context (scenario : Scenario) : Contract.Context :=
  {balance := w 3, availableGas := some (w 100), completeWorld := scenario != .absent,
    world := occupant scenario, accounts := held scenario}
def scheme : Scenario → CreationAddressSemantics.Scheme
  | .absent | .overflow => .create
  | .unknownCode | .overflow2 => .create2 (w 7)
def endowment : Scenario → Core.Word
  | .overflow | .overflow2 => w 1
  | _ => w 0
def reason : Scenario → Core.Word
  | .absent | .unknownCode => w 7
  | .overflow | .overflow2 => w 12
def invoked : Scenario → Expr
  | .absent => call .word "create" [word "0", word "0", word "0"]
  | .overflow => call .word "create" [word "1", word "0", word "0"]
  | .unknownCode => call .word "create2" [word "0", word "0", word "0", word "7"]
  | .overflow2 => call .word "create2" [word "1", word "0", word "0", word "7"]
def stored (scenario : Scenario) : Expr := call .unit "mstore" [word "0", invoked scenario]
def returned : Expr := call .unit "return" [word "0", word "32"]
def code (scenario : Scenario) : CodeBlock := {
  stmts := [expression (stored scenario), expression returned], functions := []}
def program (scenario : Scenario) : Program :=
  {entryPoints := [], functions := [], objects := [.object "Creator" (code scenario) []]}
def functions (scenario : Scenario) : List Function := [AccountRuntime.frameFunction (code scenario)]
def effects : Semantics.ExternalSemantics RuntimeCallModeSemantics.State :=
  ChildFrameModeSemantics.effectsAt [] 1 (some rootBytes)

abbrev SourceState := Semantics.State RuntimeCallModeSemantics.State
def frame (state : SourceState) := state.external.runtime.runtime.runtime.runtime.runtime
def initial (object : Contract.CompiledObject) (scenario : Scenario) : SourceState :=
  ⟨[], ContractCallCorrespondence.contextInitialState (some rootBytes) object (Contract.normalizeContext (context scenario))⟩

/-- The creator's record in the initial world. -/
def creatorAccount (object : Contract.CompiledObject) (scenario : Scenario) : AccountState.Account :=
  match StorageSemantics.lookup (CreationSemantics.creator (initial object scenario).external)
      (frame (initial object scenario)).storage.world with
  | some account => account
  | none => {address := Core.Word.zero}

/-- The frame state after the attempt: only the creator nonce advance remains,
memory covers the empty init range and return data is cleared. -/
def finalState (object : Contract.CompiledObject) (scenario : Scenario) : SourceState :=
  ⟨[], CreationSemantics.refused
    (CreationSemantics.advanced (initial object scenario).external (creatorAccount object scenario)) Core.Word.zero⟩
def result (scenario : Scenario) : Semantics.Result Semantics.Value := .fault (.language (reason scenario))

private theorem address_zero (object : Contract.CompiledObject) (scenario : Scenario) :
    (frame (initial object scenario)).storage.address = Contract.normalizeAddress Core.Word.zero := rfl

private theorem creator_zero (object : Contract.CompiledObject) (scenario : Scenario) :
    CreationSemantics.creator (initial object scenario).external = Core.Word.zero := by
  change (frame (initial object scenario)).storage.address.bitAnd _ = _
  rw [address_zero]
  decide

private theorem creator_lookup (object : Contract.CompiledObject) (scenario : Scenario) :
    StorageSemantics.lookup (CreationSemantics.creator (initial object scenario).external)
      (frame (initial object scenario)).storage.world = some (creatorAccount object scenario) := by
  unfold creatorAccount
  cases looked : StorageSemantics.lookup (CreationSemantics.creator (initial object scenario).external)
      (frame (initial object scenario)).storage.world with
  | some account => rfl
  | none =>
      rw [creator_zero] at looked
      cases scenario <;> cases looked

private theorem creator_found (object : Contract.CompiledObject) (scenario : Scenario) :
    StorageSemantics.get (frame (initial object scenario)).storage.world
      (CreationSemantics.creator (initial object scenario).external)
      (frame (initial object scenario)).storage.complete = .ok (creatorAccount object scenario) := by
  simp only [StorageSemantics.get, creator_lookup]

private theorem creator_nonce (object : Contract.CompiledObject) (scenario : Scenario) :
    (creatorAccount object scenario).nonce = w 1 := by
  unfold creatorAccount
  rw [creator_zero]
  cases scenario <;> rfl

private theorem balances_initial (object : Contract.CompiledObject) (scenario : Scenario) :
    (RuntimeCallEffectsSemantics.shared (initial object scenario).external).balances =
      held scenario ++ [(Contract.normalizeAddress Core.Word.zero, w 3)] := by
  cases scenario <;> rfl

private theorem admission (object : Contract.CompiledObject) (scenario : Scenario) :
    CreationSemantics.Admission (endowment scenario) (w 0) (w 0) (initial object scenario).external Core.Word.zero
      (creatorAccount object scenario) := by
  refine ⟨rfl, by decide, ⟨w 100, rfl⟩, rfl, ?_, ?_, creator_found object scenario, ?_⟩
  · change Core.Word.zero.val < CreationSemantics.depthLimit
    decide
  · change (endowment scenario).val ≤ (StorageSemantics.readWord (CreationSemantics.creator (initial object scenario).external)
      (RuntimeCallEffectsSemantics.shared (initial object scenario).external).balances).val
    rw [creator_zero, balances_initial]
    cases scenario <;> decide
  · rw [creator_nonce]
    decide

private theorem advanced_lookup (object : Contract.CompiledObject) (scenario : Scenario) :
    StorageSemantics.lookup (target scenario)
      (CreationSemantics.frame (CreationSemantics.advanced (initial object scenario).external
        (creatorAccount object scenario))).storage.world = (occupant scenario).head? := by
  change StorageSemantics.lookup (target scenario) (StorageSemantics.put
    (CreationSemantics.creator (initial object scenario).external) _ _) = _
  rw [creator_zero]
  cases scenario <;> rfl

private theorem overflowed (object : Contract.CompiledObject) (scenario : Scenario)
    (overflowing : scenario = .overflow ∨ scenario = .overflow2) :
    AccountCallSemantics.transfer (CreationSemantics.creator (initial object scenario).external) (target scenario)
      (endowment scenario) (RuntimeCallEffectsSemantics.shared (initial object scenario).external).balances =
      .error (w 12) := by
  rw [creator_zero, balances_initial]
  rcases overflowing with rfl | rfl <;> rfl

private theorem derived_create (object : Contract.CompiledObject) (scenario : Scenario) :
    CreationAddressSemantics.Derived (CreationSemantics.creator (initial object scenario).external)
      (creatorAccount object scenario).nonce [] (w 0) .create createTarget := by
  rw [creator_zero, creator_nonce, ← createTarget_derived]
  exact .create (CreationPreimage.shortDigest_keccak (by decide +kernel))

private theorem derived_create2 (object : Contract.CompiledObject) (scenario : Scenario) :
    CreationAddressSemantics.Derived (CreationSemantics.creator (initial object scenario).external)
      (creatorAccount object scenario).nonce [] (w 0) (.create2 (w 7)) create2Target := by
  rw [creator_zero, ← create2Target_derived]
  exact .create2 (initHash := emptyHash) (.last _ _ _ (by decide)) (CreationPreimage.shortDigest_keccak (by decide +kernel))

/-- The independent admitted rule of each attempt. -/
private theorem admitted_rule (object : Contract.CompiledObject) (scenario : Scenario) :
    CreationSemantics.Admitted (scheme scenario) (endowment scenario) (w 0) (w 0) (initial object scenario).external
      (result scenario) (finalState object scenario).external := by
  have admitted := admission object scenario
  have looked := advanced_lookup object scenario
  cases scenario
  · exact .unknown admitted (.empty _ _ _ _) (derived_create object _) (.absent looked rfl)
  · exact .unknown admitted (.empty _ _ _ _) (derived_create2 object _) (.unknownCode looked rfl rfl)
  · exact .overflow admitted (.empty _ _ _ _) (derived_create object _) looked rfl
      (overflowed object _ (.inl rfl))
  · exact .overflow admitted (.empty _ _ _ _) (derived_create2 object _) looked rfl
      (overflowed object _ (.inr rfl))

private theorem attempt_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr (functions scenario) effects [] (invoked scenario) (initial object scenario)
      (result scenario) (finalState object scenario) := by
  have computed := admitted_rule object scenario
  cases scenario
  · exact .call rfl (.cons (.word (text := "0") rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := "0") rfl) .nil)))
      (.external (by rfl) rfl (.createAdmitted computed))
  · exact .call rfl (.cons (.word (text := "0") rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := "0") rfl)
      (.cons (.word (text := "7") rfl) .nil))))
      (.external (by rfl) rfl (.create2Admitted (salt := w 7) computed))
  · exact .call rfl (.cons (.word (text := "1") rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := "0") rfl) .nil)))
      (.external (by rfl) rfl (.createAdmitted computed))
  · exact .call rfl (.cons (.word (text := "1") rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := "0") rfl)
      (.cons (.word (text := "7") rfl) .nil))))
      (.external (by rfl) rfl (.create2Admitted (salt := w 7) computed))

private theorem store_fault (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr (functions scenario) effects [] (stored scenario) (initial object scenario)
      (result scenario) (finalState object scenario) :=
  .callFault rfl (.cons (.word (text := "0") rfl) (.fault (attempt_source object scenario)))

theorem source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalFunction (functions scenario) effects (AccountRuntime.frameFunction (code scenario)) []
      (initial object scenario) (result scenario) (finalState object scenario) := by
  apply Semantics.EvalFunction.body (control := .fault (.language (reason scenario))) rfl
  exact .stop (by intros; intro impossible; cases impossible) (.expressionFault rfl (store_fault object scenario))
    (by intro impossible; cases impossible)

def usedNames : List String := ["mstore", "create", "create2", "return"]

private theorem atoms {supported : String → Prop} (functions : List Function) (type : Ty) (name : String)
    (texts : List String) (available : supported name) (notFunction : functions.find? (·.name == name) = none) :
    ExecutableExpression supported functions (call type name (texts.map word)) := by
  apply ExecutableExpression.external available notFunction
  intro argument member
  obtain ⟨text, _, rfl⟩ := List.mem_map.mp member
  exact .word _ _ _

theorem eligible (scenario : Scenario) {supported : String → Prop}
    (available : ∀ name ∈ usedNames, supported name) :
    ExecutableProgram supported (functions scenario) := by
  intro function member statement statementMember
  simp only [functions, List.mem_cons, List.not_mem_nil, or_false] at member
  subst function
  simp only [AccountRuntime.frameFunction, code, List.mem_cons, List.not_mem_nil, or_false] at statementMember
  rcases statementMember with rfl | rfl
  all_goals simp only [expression, ExecutableStatement]
  · apply ExecutableExpression.external (name := "mstore") (available _ (by simp [usedNames])) (by rfl)
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact .word _ _ _
    · cases scenario <;> first
        | exact atoms _ .word "create" ["0", "0", "0"] (available _ (by simp [usedNames])) (by rfl)
        | exact atoms _ .word "create" ["1", "0", "0"] (available _ (by simp [usedNames])) (by rfl)
        | exact atoms _ .word "create2" ["0", "0", "0", "7"] (available _ (by simp [usedNames])) (by rfl)
        | exact atoms _ .word "create2" ["1", "0", "0", "7"] (available _ (by simp [usedNames])) (by rfl)
  · exact atoms _ .unit "return" ["0", "32"] (available _ (by simp [usedNames])) (by rfl)

private theorem names_supported : ∀ name ∈ usedNames, ContractCallModeCorrespondence.supported true name := by
  intro name member
  simp only [usedNames, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl ⟨.store, rfl⟩)))))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inl rfl))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr rfl))))))
  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inr ⟨.returned, rfl⟩))))))

private theorem empty_connection : ModeChildCatalogExecutionCorrespondence.CatalogConnection [] [] [] := by
  intro address source selected
  simp [ChildFrameSemantics.select] at selected

private theorem empty_links (object : Contract.CompiledObject) (scenario : Scenario) :
    ContractCallModeCorrespondence.InitialContextLinks (some rootBytes) [] object (context scenario) [] := by
  intro anchor member
  simp at member

/-- Public consumer of the call-mode theorem for admitted CREATE and CREATE2
attempts that fault after the nonce advance: an absent target in an incomplete
world, a target with unknown code, and two endowment overflows. -/
theorem public_resumes (scenario : Scenario) {object : Contract.CompiledObject}
    (accepted : Contract.compileObject (program scenario) ["Creator"] 64 (some rootBytes) [] = .ok object) :
    ∃ value, ContractCallModeCorrespondence.PublicMessageRel (context scenario) (result scenario)
        (finalState object scenario).external value ∧
      ∃ required, ∀ initialFuel additional limit last,
        Contract.ReceiptResumes limit (Contract.runWithReceipt (object.instantiate (context scenario)) initialFuel limit)
          additional last →
        (last = Contract.finish limit value ↔ required ≤ initialFuel + additional) ∧
        ((∃ checkpoint, last.outcome = .outOfFuel checkpoint) ↔ initialFuel + additional < required) := by
  exact ContractCallModeCorrespondence.compileObject_resumes_exact (height := 0) (code := code scenario) (by rfl)
    accepted rfl (eligible scenario names_supported) empty_connection (context scenario)
    (by cases scenario <;> rfl) (empty_links object scenario) (source object scenario)

private def check (scenario : Scenario) : IO Unit := do
  let object ← match Contract.compileObject (program scenario) ["Creator"] 64 (some rootBytes) [] with
    | .ok object => pure object
    | .error error => throw (IO.userError s!"creation fault: compile failed: {reprStr error}")
  let prepared := object.instantiate (context scenario)
  let checkpoint ← match (Contract.runWithReceipt prepared 0).outcome with
    | .outOfFuel checkpoint => pure checkpoint
    | outcome => throw (IO.userError s!"creation fault: zero fuel completed: {reprStr outcome}")
  for receipt in [Contract.runWithReceipt prepared 1000000, Contract.resumeWithReceipt checkpoint 1000000] do
    match receipt.outcome with
    | .languageFailure failure =>
        unless failure == .word (reason scenario) do
          throw (IO.userError s!"creation fault: wrong reason for {reprStr scenario}: {reprStr failure}")
    | outcome =>
        throw (IO.userError s!"creation fault: unexpected outcome for {reprStr scenario}: {reprStr outcome}")

def run : IO Unit := do
  for scenario in [Scenario.absent, .unknownCode, .overflow, .overflow2] do
    check scenario

end Tests.RustHullCreationFaultCorrespondence
