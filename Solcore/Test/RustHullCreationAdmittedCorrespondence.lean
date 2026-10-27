import Solcore.Frontend.RustHull.ContractCallModeExecutionCorrespondence
import Solcore.Frontend.RustHull.ContractCallModeSupported

/-! Admitted CREATE and CREATE2 attempts that run no init frame reach the
actual lowering, transport and installed create handler through the call-mode
public theorem. Each scenario stores the attempt's result word and returns it.
Two deployments of empty init code create a new account with nonce one, one of
them with an endowment; a nonzero nonce and nonempty code at the derived
address are collisions that return zero. Every attempt advances the creator
nonce. The derived addresses are checked in the kernel against the
independent RLP and Keccak specification. -/
set_option autoImplicit false
set_option maxRecDepth 8192
namespace Tests.RustHullCreationAdmittedCorrespondence
open Solcore Solcore.Frontend.RustHull Correspondence DerivationCorrespondence

inductive Scenario where
  | deployed | deployed2 | collision | collision2
  deriving DecidableEq, Repr

private abbrev w := Core.Word.ofNatModulo
private def word (text : String) : Expr := ⟨.word, .word text, none⟩
private def call (type : Ty) (name : String) (arguments : List Expr) : Expr := ⟨type, .call name arguments, none⟩
private def expression (value : Expr) : Stmt := ⟨.expression value, none⟩

def emptyHash : Core.Word := CreationPreimage.shortDigest []
def createTarget : Core.Word := w 515330412878651974478734746372204808145222434547
def create2Target : Core.Word := w 376623410840471690759715731732645848578652475442

theorem createTarget_derived : CreationAddressSemantics.address
    (CreationPreimage.shortDigest (CreationAddressSemantics.createPreimage Core.Word.zero (w 1))) = createTarget := by
  decide +kernel

theorem create2Target_derived : CreationAddressSemantics.address
    (CreationPreimage.shortDigest (CreationAddressSemantics.create2Preimage Core.Word.zero (w 7) emptyHash)) =
      create2Target := by
  decide +kernel

def rootBytes : List UInt8 := [0]
def target : Scenario → Core.Word
  | .deployed | .collision => createTarget
  | .deployed2 | .collision2 => create2Target
/-- An account at the CREATE address with a nonzero nonce, and one at the
CREATE2 address with code. -/
def occupant : Scenario → List AccountState.Account
  | .collision => [{address := createTarget, nonce := w 1}]
  | .collision2 => [{address := create2Target, code := some [254]}]
  | _ => []
def context (scenario : Scenario) : Contract.Context :=
  {balance := w 3, availableGas := some (w 100), completeWorld := true, world := occupant scenario}
def scheme : Scenario → CreationAddressSemantics.Scheme
  | .deployed | .collision => .create
  | .deployed2 | .collision2 => .create2 (w 7)
def endowment : Scenario → Core.Word
  | .deployed => w 2
  | _ => w 0
def invoked : Scenario → Expr
  | .deployed => call .word "create" [word "2", word "0", word "0"]
  | .collision => call .word "create" [word "0", word "0", word "0"]
  | .deployed2 | .collision2 => call .word "create2" [word "0", word "0", word "0", word "7"]
def stored (scenario : Scenario) : Expr := call .unit "mstore" [word "0", invoked scenario]
def returned : Expr := call .unit "return" [word "0", word "32"]
def code (scenario : Scenario) : CodeBlock := {
  stmts := [expression (stored scenario), expression returned], functions := []}
def program (scenario : Scenario) : Program :=
  {entryPoints := [], functions := [], objects := [.object "Creator" (code scenario) []]}
def functions (scenario : Scenario) : List Function := [AccountRuntime.frameFunction (code scenario)]
def effects : Semantics.ExternalSemantics RuntimeCallModeSemantics.State :=
  ChildFrameModeSemantics.effectsAt [] {} 1 (some rootBytes)

abbrev SourceState := Semantics.State RuntimeCallModeSemantics.State
def frame (state : SourceState) := state.external.runtime.runtime.runtime.runtime.runtime
def withMemory (state : SourceState) (memory : MemorySemantics.State) : SourceState :=
  ⟨[], {state.external with runtime := (RuntimeReturnDataEffectsSemantics.withRuntime state.external.runtime
    {frame state with memory := memory})}⟩
def initial (object : Contract.CompiledObject) (scenario : Scenario) : SourceState :=
  ⟨[], ContractCallCorrespondence.contextInitialState (some rootBytes) object (Contract.normalizeContext (context scenario))⟩

/-- The creator's record in the initial world. -/
def creatorAccount (object : Contract.CompiledObject) (scenario : Scenario) : AccountState.Account :=
  match StorageSemantics.get (frame (initial object scenario)).storage.world
      (CreationSemantics.creator (initial object scenario).external) true with
  | .ok account => account
  | .error _ => {address := Core.Word.zero}

def deploys : Scenario → Bool
  | .deployed | .deployed2 => true
  | _ => false
def endowed : Scenario → StorageSemantics.Words
  | .deployed => [(w 0, w 1), (createTarget, w 2)]
  | _ => [(w 0, w 3)]
def created (scenario : Scenario) : Core.Word := if deploys scenario then target scenario else Core.Word.zero

/-- The frame state after the attempt: the creator nonce advanced, and either
a new account with its endowment or a collision. -/
def afterAttempt (object : Contract.CompiledObject) (scenario : Scenario) : SourceState :=
  let advanced := CreationSemantics.advanced (initial object scenario).external (creatorAccount object scenario)
  if deploys scenario then ⟨[], CreationSemantics.deployed advanced (target scenario) (endowed scenario) Core.Word.zero⟩
  else ⟨[], CreationSemantics.refused advanced Core.Word.zero⟩
def afterStore (object : Contract.CompiledObject) (scenario : Scenario) : SourceState :=
  withMemory (afterAttempt object scenario)
    (MemorySemantics.mstore (frame (afterAttempt object scenario)).memory (w 0) (created scenario)).2
def finalState (object : Contract.CompiledObject) (scenario : Scenario) : SourceState :=
  let state := (afterStore object scenario).external
  ⟨[], {state with runtime := (RuntimeReturnDataEffectsSemantics.withRuntime state.runtime
    (TerminationSemantics.terminate state.runtime.runtime.runtime.runtime.runtime 1 (w 0) (w 32)).2)}⟩
def result : Semantics.Result Semantics.Value := .fault (.language Core.Word.maximum)

private theorem address_zero (object : Contract.CompiledObject) (scenario : Scenario) :
    (frame (initial object scenario)).storage.address = Contract.normalizeAddress Core.Word.zero := rfl

private theorem creator_zero (object : Contract.CompiledObject) (scenario : Scenario) :
    CreationSemantics.creator (initial object scenario).external = Core.Word.zero := by
  change (frame (initial object scenario)).storage.address.bitAnd _ = _
  rw [address_zero]
  decide

private theorem creator_found (object : Contract.CompiledObject) (scenario : Scenario) :
    StorageSemantics.get (frame (initial object scenario)).storage.world
      (CreationSemantics.creator (initial object scenario).external)
      (frame (initial object scenario)).storage.complete = .ok (creatorAccount object scenario) := by
  have complete : (frame (initial object scenario)).storage.complete = true := by cases scenario <;> rfl
  rw [complete]
  unfold creatorAccount
  cases found : StorageSemantics.get (frame (initial object scenario)).storage.world
      (CreationSemantics.creator (initial object scenario).external) true with
  | ok account => rfl
  | error reason =>
      unfold StorageSemantics.get at found
      split at found <;> simp at found

private theorem creator_nonce (object : Contract.CompiledObject) (scenario : Scenario) :
    (creatorAccount object scenario).nonce = w 1 := by
  cases scenario <;> rfl


private theorem balances_initial (object : Contract.CompiledObject) (scenario : Scenario) :
    (RuntimeCallEffectsSemantics.shared (initial object scenario).external).balances =
      [(Contract.normalizeAddress Core.Word.zero, w 3)] := rfl

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

private theorem transferred (object : Contract.CompiledObject) (scenario : Scenario) :
    AccountCallSemantics.transfer (CreationSemantics.creator (initial object scenario).external) (target scenario)
      (endowment scenario) (RuntimeCallEffectsSemantics.shared (initial object scenario).external).balances =
      .ok (endowed scenario) := by
  rw [creator_zero, balances_initial]
  cases scenario <;> rfl


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
      (.value (.word (created scenario))) (afterAttempt object scenario).external := by
  have admitted := admission object scenario
  have looked := advanced_lookup object scenario
  have moved := transferred object scenario
  cases scenario
  · exact .deployed admitted (.empty _ _ _ _) (derived_create object _) looked rfl rfl moved
  · exact .deployed admitted (.empty _ _ _ _) (derived_create2 object _) looked rfl rfl moved
  · exact .collision admitted (.empty _ _ _ _) (derived_create object _) looked (.inl (by decide))
  · exact .collision admitted (.empty _ _ _ _) (derived_create2 object _) looked (.inr (by decide))

private theorem attempt_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr (functions scenario) effects [] (invoked scenario) (initial object scenario)
      (.value (.word (created scenario))) (afterAttempt object scenario) := by
  have computed := admitted_rule object scenario
  cases scenario
  · exact .call rfl (.cons (.word (text := "2") rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := "0") rfl) .nil)))
      (.external (by rfl) rfl (.createAdmitted computed))
  · exact .call rfl (.cons (.word (text := "0") rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := "0") rfl)
      (.cons (.word (text := "7") rfl) .nil))))
      (.external (by rfl) rfl (.create2Admitted (salt := w 7) computed))
  · exact .call rfl (.cons (.word (text := "0") rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := "0") rfl) .nil)))
      (.external (by rfl) rfl (.createAdmitted computed))
  · exact .call rfl (.cons (.word (text := "0") rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := "0") rfl)
      (.cons (.word (text := "7") rfl) .nil))))
      (.external (by rfl) rfl (.create2Admitted (salt := w 7) computed))

private theorem store_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr (functions scenario) effects [] (stored scenario) (initial object scenario)
      (.value .unit) (afterStore object scenario) := by
  cases scenario
  all_goals
    apply Semantics.EvalExpr.call rfl
    · exact .cons (.word (text := "0") rfl) (.cons (attempt_source object _) .nil)
    · exact .external (by rfl) rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime rfl))))))))

private theorem return_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr (functions scenario) effects [] returned (afterStore object scenario) result
      (finalState object scenario) := by
  apply Semantics.EvalExpr.call rfl
  · exact .cons (.word (text := "0") rfl) (.cons (.word (text := "32") rfl) .nil)
  · exact .external (by rfl) rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.termination rfl)))))))

theorem source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalFunction (functions scenario) effects (AccountRuntime.frameFunction (code scenario)) []
      (initial object scenario) result (finalState object scenario) := by
  apply Semantics.EvalFunction.body (control := .fault _) rfl
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible)
    (.expression rfl (store_source object scenario))
  exact .stop (by intros; intro impossible; cases impossible) (.expressionFault rfl (return_source object scenario))
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
        | exact atoms _ .word "create" ["2", "0", "0"] (available _ (by simp [usedNames])) (by rfl)
        | exact atoms _ .word "create" ["0", "0", "0"] (available _ (by simp [usedNames])) (by rfl)
        | exact atoms _ .word "create2" ["0", "0", "0", "7"] (available _ (by simp [usedNames])) (by rfl)
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
attempts without an init frame: two deployments of empty init code, one with
an endowment, and two collisions. -/
theorem public_resumes (scenario : Scenario) {object : Contract.CompiledObject}
    (accepted : Contract.compileObject (program scenario) ["Creator"] 64 (some rootBytes) [] = .ok object) :
    ∃ value, ContractCallModeCorrespondence.PublicMessageRel (context scenario) result
        (finalState object scenario).external value ∧
      ∃ required, ∀ initialFuel additional limit last,
        Contract.ReceiptResumes limit (Contract.runWithReceipt (object.instantiate (context scenario)) initialFuel limit)
          additional last →
        (last = Contract.finish limit value ↔ required ≤ initialFuel + additional) ∧
        ((∃ checkpoint, last.outcome = .outOfFuel checkpoint) ↔ initialFuel + additional < required) := by
  exact ContractCallModeCorrespondence.compileObject_resumes_exact (height := 0) (code := code scenario) (by rfl)
    accepted rfl (eligible scenario names_supported) empty_connection (InitCatalogCorrespondence.InitCatalogConnection.empty rfl (by decide)) (context scenario)
    (by cases scenario <;> rfl) (empty_links object scenario) (source object scenario)

private def addressBytes (value : Core.Word) : List UInt8 :=
  (List.range 32).map fun index => UInt8.ofNat (value.val / 256 ^ (31 - index) % 256)

private def check (scenario : Scenario) : IO Unit := do
  let object ← match Contract.compileObject (program scenario) ["Creator"] 64 (some rootBytes) [] with
    | .ok object => pure object
    | .error error => throw (IO.userError s!"admitted creation: compile failed: {reprStr error}")
  let prepared := object.instantiate (context scenario)
  let checkpoint ← match (Contract.runWithReceipt prepared 0).outcome with
    | .outOfFuel checkpoint => pure checkpoint
    | outcome => throw (IO.userError s!"admitted creation: zero fuel completed: {reprStr outcome}")
  for receipt in [Contract.runWithReceipt prepared 1000000, Contract.resumeWithReceipt checkpoint 1000000] do
    match receipt.outcome with
    | .returned bytes storage =>
        let creatorRecord := receipt.world.find? (·.address == Core.Word.zero)
        let targetRecord := receipt.world.find? (·.address == target scenario)
        let targetExpected := if deploys scenario || scenario = .collision then some (w 1) else some (w 0)
        unless bytes == addressBytes (created scenario) && storage.isEmpty && receipt.logs.isEmpty &&
            receipt.balances == endowed scenario && receipt.world.length == 2 &&
            creatorRecord.map (·.nonce) == some (w 2) && targetRecord.map (·.nonce) == targetExpected &&
            targetRecord.map (·.code) == some (if scenario = .collision2 then some [254] else some []) do
          throw (IO.userError s!"admitted creation: wrong receipt for {reprStr scenario}: {reprStr receipt}")
    | outcome =>
        throw (IO.userError s!"admitted creation: unexpected outcome for {reprStr scenario}: {reprStr outcome}")

def run : IO Unit := do
  for scenario in [Scenario.deployed, .deployed2, .collision, .collision2] do
    check scenario

end Tests.RustHullCreationAdmittedCorrespondence
