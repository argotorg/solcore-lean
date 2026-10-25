import Solcore.Frontend.RustHull.RuntimeCodeCorrespondence
import Solcore.Frontend.RustHull.RuntimeFrameCorrespondence
import Solcore.Frontend.RustHull.ContractExecutionCorrespondence

/-! Completion of the actual message wrapper preserves account finalization
and forwards the resulting runtime value to public receipts. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.Correspondence
open CodeBuilder ScalarExecution

 theorem CodeValue.first {depth : Nat} {environment : Core.Environment} {code : Code}
    {left right : Core.Value} (related : CodeValue depth environment code (.pair left right)) :
    CodeValue depth environment (AccountRuntime.first code) left :=
  fun extra store => .first (related extra store)

 theorem CodeValue.second {depth : Nat} {environment : Core.Environment} {code : Code}
    {left right : Core.Value} (related : CodeValue depth environment code (.pair left right)) :
    CodeValue depth environment (AccountRuntime.second code) right :=
  fun extra store => .second (related extra store)

 theorem StorageCorrespondence.get_complete (accounts : StorageCorrespondence.Accounts) (address : Core.Word) :
    ∃ account identity, StorageCorrespondence.get accounts address true = .ok (account, identity) := by
  unfold StorageCorrespondence.get
  cases StorageCorrespondence.lookup address accounts with
  | none => exact ⟨_, _, rfl⟩
  | some account => exact ⟨account.1, account.2, rfl⟩

 def finalizedSnapshotValue (values : String → Core.Value) (account : AccountState.Account)
    (accounts : StorageCorrespondence.Accounts) (balances : StorageSemantics.Words) : Core.Value :=
  frameSnapshotValue
    (fun name => if name = "balances" then Core.WordMapping.encode balances
      else if name = "world" then StorageCorrespondence.world accounts else values name)
    (Core.WordMapping.encode account.storage)

 theorem messageFinalize_evaluates {depth : Nat} {environment : Core.Environment}
    {shared : AccountRuntime.References} {target result : Code}
    {status oldStorage : Core.Value} {values : String → Core.Value} {address : Core.Word}
    {worldLocation balancesLocation : Nat} {initial : Core.Store}
    (accounts : StorageCorrespondence.Accounts) (balances : StorageSemantics.Words)
    (worldReference : CodeValue depth environment (AccountRuntime.reference shared "world")
      (.cellRef AccountState.type worldLocation))
    (balancesReference : CodeValue depth environment (AccountRuntime.reference shared "balances")
      (.cellRef Core.WordMapping.type balancesLocation))
    (targetValue : CodeValue depth environment target (.word address))
    (resultValue : CodeValue depth environment result (.pair status (frameSnapshotValue values oldStorage)))
    (worldFound : initial.read? worldLocation = some (StorageCorrespondence.world accounts))
    (balancesFound : initial.read? balancesLocation = some (Core.WordMapping.encode balances)) :
    ∃ account identity final,
      StorageCorrespondence.get (StorageCorrespondence.finalize accounts balances).1 address true = .ok (account, identity) ∧
      Core.Evaluates environment initial (AccountRuntime.finalize shared target result depth)
        (.pair status (finalizedSnapshotValue values account
          (StorageCorrespondence.finalize accounts balances).1 (StorageCorrespondence.finalize accounts balances).2)) final ∧
      final.read? worldLocation = some (StorageCorrespondence.world (StorageCorrespondence.finalize accounts balances).1) ∧
      final.read? balancesLocation = some (Core.WordMapping.encode (StorageCorrespondence.finalize accounts balances).2) ∧
      StorageCorrespondence.FinalizeFrame worldLocation balancesLocation initial final := by
  obtain ⟨completed, finalized, worldUpdated, balancesUpdated, frame⟩ :=
    StorageCorrespondence.finalize_evaluates accounts balances worldLocation balancesLocation
      (.pair (worldReference.evaluates initial) (balancesReference.evaluates initial)) worldFound balancesFound
  obtain ⟨account, identity, found⟩ := StorageCorrespondence.get_complete
    (StorageCorrespondence.finalize accounts balances).1 address
  let finalizedValue := Core.Value.inRight .word .unit
  let fetchedValue := StorageCorrespondence.getValue (.ok (account, identity))
  let getEnvironment := Core.Value.unit :: finalizedValue :: environment
  let final := StorageCorrespondence.getStore (StorageCorrespondence.finalize accounts balances).1
    address true getEnvironment completed
  have fetched := StorageCorrespondence.get_evaluates
    (environment := getEnvironment) (StorageCorrespondence.finalize accounts balances).1 address true
    (.loadCell (worldReference [Core.Value.unit, finalizedValue] completed) worldUpdated)
    (targetValue [Core.Value.unit, finalizedValue] completed) Core.Evaluates.bool
  rw [found] at fetched
  obtain ⟨suffix, _, extension⟩ := StorageCorrespondence.getStore_extension
    (StorageCorrespondence.finalize accounts balances).1 address true getEnvironment completed
  have retained : StoreRetains completed final := by
    rw [show final = completed ++ suffix from extension]
    exact StoreRetains.append _ _
  have worldFinal := retained.read worldLocation (List.getElem?_eq_some_iff.mp worldUpdated).1
  have balancesFinal := retained.read balancesLocation (List.getElem?_eq_some_iff.mp balancesUpdated).1
  rw [worldUpdated] at worldFinal
  rw [balancesUpdated] at balancesFinal
  refine ⟨account, identity, final, found, ?_, worldFinal, balancesFinal, ?_⟩
  · unfold AccountRuntime.finalize CodeBuilder.bind
    apply Core.Evaluates.letE finalized
    apply Core.Evaluates.caseRight (leftType := .word) (payload := .unit) (.var (by simp))
    apply Core.Evaluates.letE fetched
    apply Core.Evaluates.caseRight (leftType := .word) (payload := StorageCorrespondence.record account identity)
      (.var (by simp [StorageCorrespondence.getValue]))
    let extra := [StorageCorrespondence.record account identity, fetchedValue, Core.Value.unit, finalizedValue]
    have evaluated := resultValue extra final
    have projected (index : Nat) (value : Core.Value)
        (selected : [values "exit", values "returnOffset", values "returnSize", values "memory",
          oldStorage, values "logs", values "logSize", values "balances", values "world"][index]? = some value) :=
      projectArgument_evaluates (.second evaluated) selected
    have stored : Core.Evaluates (extra ++ environment) final
        (part 0 9 (fun here => Core.Expr.var (here - (depth + 1 + 1 + 1) - 1)) (depth + 1 + 1 + 1 + 1))
        (Core.WordMapping.encode account.storage) final :=
      projectArgument_evaluates (Core.Evaluates.var (by simp [extra, StorageCorrespondence.record])) (by rfl :
        [Core.WordMapping.encode account.storage, Core.WordMapping.encode account.transient,
          Core.Value.word account.nonce, .word (Core.Word.ofNatModulo identity),
          Core.WordMapping.encode (Memory.packBytes (account.code.getD [])),
          .word (Core.Word.ofNatModulo (account.code.getD []).length),
          .bool account.code.isSome, .bool account.created, .bool account.destroyed][0]? = some _)
    exact .pair (.first evaluated)
      (.pair (projected 0 _ rfl) (.pair (projected 1 _ rfl) (.pair (projected 2 _ rfl)
        (.pair (projected 3 _ rfl) (.pair stored (.pair (projected 5 _ rfl)
          (.pair (projected 6 _ rfl) (.pair
            (.loadCell (balancesReference extra final) balancesFinal)
            (.loadCell (worldReference extra final) worldFinal)))))))))
  · constructor
    · exact Nat.le_trans frame.length_le retained.length_le
    · intro location value differentWorld differentBalances read
      rw [retained.read location (List.getElem?_eq_some_iff.mp
        (frame.preserved location value differentWorld differentBalances read)).1]
      exact frame.preserved location value differentWorld differentBalances read

inductive MessageStatus : Core.Value → Bool → Prop where
  | success : MessageStatus (.inRight .word .unit) true
  | failure (reason : Core.Value) : MessageStatus (.inLeft .unit reason) false

def messageSucceeded (exit : Core.Word) (status : Bool) : Bool :=
  if exit == Core.Word.ofNatModulo 1 then true
  else if exit == Core.Word.ofNatModulo 0 then status else false

theorem messageSuccessful_evaluates {depth : Nat} {environment : Core.Environment}
    {result : Code} {status oldStorage : Core.Value} {values : String → Core.Value}
    {exit : Core.Word} {succeeded : Bool}
    (resultValue : CodeValue depth environment result (.pair status (frameSnapshotValue values oldStorage)))
    (statusRelated : MessageStatus status succeeded) (exitValue : values "exit" = .word exit)
    (store : Core.Store) :
    Core.Evaluates environment store (AccountRuntime.messageSuccessful result depth)
      (.bool (messageSucceeded exit succeeded)) store := by
  have evaluated := resultValue.evaluates store
  have projected := projectArgument_evaluates (.second evaluated)
    (by simpa only [List.getElem?_cons_zero] using congrArg some exitValue :
      [values "exit", values "returnOffset", values "returnSize", values "memory", oldStorage,
       values "logs", values "logSize", values "balances", values "world"][0]? = some (.word exit))
  unfold AccountRuntime.messageSuccessful CodeBuilder.choose messageSucceeded
  cases one : exit == Core.Word.ofNatModulo 1
  · simp only [Bool.false_eq_true, ↓reduceIte]
    apply Core.Evaluates.ifFalse (.binary projected .word (by simp only [Core.BinaryOp.apply, one]))
    cases zero : exit == Core.Word.ofNatModulo 0
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact .ifFalse (.binary projected .word (by simp only [Core.BinaryOp.apply, zero])) .bool
    · simp only [↓reduceIte]
      apply Core.Evaluates.ifTrue (.binary projected .word (by simp only [Core.BinaryOp.apply, zero]))
      cases statusRelated
      · exact .caseRight (.first evaluated) .bool
      · exact .caseLeft (.first evaluated) .bool
  · simp only [↓reduceIte]
    exact .ifTrue (.binary projected .word (by simp only [Core.BinaryOp.apply, one])) .bool

theorem completeMessage_failure {depth : Nat} {environment : Core.Environment}
    {shared : AccountRuntime.References} {images : List (Nat × List UInt8)} {target deploying result : Code}
    {status oldStorage : Core.Value} {values : String → Core.Value} {exit : Core.Word} {succeeded : Bool}
    (resultValue : CodeValue depth environment result (.pair status (frameSnapshotValue values oldStorage)))
    (statusRelated : MessageStatus status succeeded) (exitValue : values "exit" = .word exit)
    (failed : messageSucceeded exit succeeded = false) (store : Core.Store) :
    Core.Evaluates environment store (AccountRuntime.completeMessage shared images target deploying result depth)
      (.pair status (frameSnapshotValue values oldStorage)) store := by
  have checked := messageSuccessful_evaluates resultValue statusRelated exitValue store
  rw [failed] at checked
  exact .ifFalse checked (resultValue.evaluates store)

theorem completeMessage_success {depth : Nat} {environment : Core.Environment}
    {shared : AccountRuntime.References} {images : List (Nat × List UInt8)} {target deploying result : Code}
    {status oldStorage : Core.Value} {values : String → Core.Value} {address exit : Core.Word} {succeeded : Bool}
    {worldLocation balancesLocation : Nat} {initial : Core.Store}
    (accounts : StorageCorrespondence.Accounts) (balances : StorageSemantics.Words)
    (worldReference : CodeValue depth environment (AccountRuntime.reference shared "world")
      (.cellRef AccountState.type worldLocation))
    (balancesReference : CodeValue depth environment (AccountRuntime.reference shared "balances")
      (.cellRef Core.WordMapping.type balancesLocation))
    (targetValue : CodeValue depth environment target (.word address))
    (deployingValue : CodeValue depth environment deploying (.bool false))
    (resultValue : CodeValue depth environment result (.pair status (frameSnapshotValue values oldStorage)))
    (statusRelated : MessageStatus status succeeded) (exitValue : values "exit" = .word exit)
    (successful : messageSucceeded exit succeeded = true)
    (worldFound : initial.read? worldLocation = some (StorageCorrespondence.world accounts))
    (balancesFound : initial.read? balancesLocation = some (Core.WordMapping.encode balances)) :
    ∃ account identity final,
      StorageCorrespondence.get (StorageCorrespondence.finalize accounts balances).1 address true = .ok (account, identity) ∧
      Core.Evaluates environment initial (AccountRuntime.completeMessage shared images target deploying result depth)
        (.pair status (finalizedSnapshotValue values account
          (StorageCorrespondence.finalize accounts balances).1 (StorageCorrespondence.finalize accounts balances).2)) final ∧
      final.read? worldLocation = some (StorageCorrespondence.world (StorageCorrespondence.finalize accounts balances).1) ∧
      final.read? balancesLocation = some (Core.WordMapping.encode (StorageCorrespondence.finalize accounts balances).2) ∧
      StorageCorrespondence.FinalizeFrame worldLocation balancesLocation initial final := by
  obtain ⟨account, identity, final, found, evaluated, worldFinal, balancesFinal, frame⟩ :=
    messageFinalize_evaluates accounts balances worldReference balancesReference targetValue resultValue worldFound balancesFound
  have checked := messageSuccessful_evaluates resultValue statusRelated exitValue initial
  rw [successful] at checked
  exact ⟨account, identity, final, found,
    .ifTrue checked (.ifFalse (deployingValue.evaluates initial) evaluated), worldFinal, balancesFinal, frame⟩

def completedMessageValue (status : Core.Value) (succeeded : Bool) (exit : Core.Word)
    (values : String → Core.Value) (storage : Core.Value)
    (accounts : StorageCorrespondence.Accounts) (address : Core.Word) (balances : StorageSemantics.Words) : Core.Value :=
  if messageSucceeded exit succeeded then
    match StorageCorrespondence.get (StorageCorrespondence.finalize accounts balances).1 address true with
    | .ok (account, _) => .pair status (finalizedSnapshotValue values account
        (StorageCorrespondence.finalize accounts balances).1 (StorageCorrespondence.finalize accounts balances).2)
    | .error _ => .pair status (frameSnapshotValue values storage)
  else .pair status (frameSnapshotValue values storage)

theorem completeMessage_evaluates {depth : Nat} {environment : Core.Environment}
    {shared : AccountRuntime.References} {images : List (Nat × List UInt8)} {target deploying result : Code}
    {status oldStorage : Core.Value} {values : String → Core.Value} {address exit : Core.Word} {succeeded : Bool}
    {worldLocation balancesLocation : Nat} {initial : Core.Store}
    (accounts : StorageCorrespondence.Accounts) (balances : StorageSemantics.Words)
    (worldReference : CodeValue depth environment (AccountRuntime.reference shared "world")
      (.cellRef AccountState.type worldLocation))
    (balancesReference : CodeValue depth environment (AccountRuntime.reference shared "balances")
      (.cellRef Core.WordMapping.type balancesLocation))
    (targetValue : CodeValue depth environment target (.word address))
    (deployingValue : CodeValue depth environment deploying (.bool false))
    (resultValue : CodeValue depth environment result (.pair status (frameSnapshotValue values oldStorage)))
    (statusRelated : MessageStatus status succeeded) (exitValue : values "exit" = .word exit)
    (worldFound : initial.read? worldLocation = some (StorageCorrespondence.world accounts))
    (balancesFound : initial.read? balancesLocation = some (Core.WordMapping.encode balances)) :
    ∃ final, Core.Evaluates environment initial (AccountRuntime.completeMessage shared images target deploying result depth)
      (completedMessageValue status succeeded exit values oldStorage accounts address balances) final := by
  cases successful : messageSucceeded exit succeeded with
  | false =>
      have evaluated := completeMessage_failure (shared := shared) (images := images) (target := target) (deploying := deploying)
        resultValue statusRelated exitValue successful initial
      exact ⟨initial, by simpa only [completedMessageValue, successful, Bool.false_eq_true, ↓reduceIte] using evaluated⟩
  | true =>
      obtain ⟨account, identity, final, found, evaluated, _, _, _⟩ :=
        completeMessage_success (images := images) accounts balances worldReference balancesReference
          targetValue deployingValue resultValue statusRelated exitValue successful worldFound balancesFound
      exact ⟨final, by simpa only [completedMessageValue, successful, ↓reduceIte, found] using evaluated⟩

/-- Successful public compilation returns the exact object wrapper around
its successfully compiled entry frame. -/
theorem compileObject_components {program : Program} {path : List String} {fuel : Nat}
    {codeBytes : Option (List UInt8)} {catalog : List AccountRuntime.CodeDefinition} {expression : Core.Expr}
    (accepted : AccountRuntime.compileObject program path fuel codeBytes catalog = .ok expression) :
    ∃ code compiled others,
      AccountRuntime.compileFrame program code
        (Effects.slots ++ (if codeBytes.isSome || !catalog.isEmpty then Effects.codeSlots else [])) fuel = .ok compiled ∧
      expression = AccountRuntime.objectExpression
        (Effects.slots ++ (if codeBytes.isSome || !catalog.isEmpty then Effects.codeSlots else []))
        compiled others ((codeBytes.toList.map (1, ·)) ++
          (catalog.zipIdx.filterMap fun (definition, index) =>
            if definition.isInit then none else some (index + 2, definition.bytes))) codeBytes catalog := by
  unfold AccountRuntime.compileObject at accepted
  obtain ⟨code, _, accepted⟩ := lower_bind_eq_ok.mp accepted
  obtain ⟨compiled, compiledOk, accepted⟩ := lower_bind_eq_ok.mp accepted
  obtain ⟨others, _, accepted⟩ := lower_bind_eq_ok.mp accepted
  obtain ⟨_, _, accepted⟩ := lower_bind_eq_ok.mp accepted
  obtain ⟨guard, _, accepted⟩ := lower_bind_eq_ok.mp accepted
  cases guard
  cases accepted
  exact ⟨code, compiled, others, compiledOk, rfl⟩

theorem compileObject_empty_catalog {program : Program} {path : List String} {fuel : Nat}
    {codeBytes : Option (List UInt8)} {expression : Core.Expr}
    (accepted : AccountRuntime.compileObject program path fuel codeBytes [] = .ok expression) :
    ∃ code compiled,
      AccountRuntime.compileFrame program code
        (Effects.slots ++ (if codeBytes.isSome then Effects.codeSlots else [])) fuel = .ok compiled ∧
      expression = AccountRuntime.objectExpression
        (Effects.slots ++ (if codeBytes.isSome then Effects.codeSlots else []))
        compiled [] (codeBytes.toList.map (1, ·)) codeBytes [] := by
  unfold AccountRuntime.compileObject at accepted
  obtain ⟨code, _, accepted⟩ := lower_bind_eq_ok.mp accepted
  obtain ⟨compiled, compiledOk, accepted⟩ := lower_bind_eq_ok.mp accepted
  obtain ⟨others, mapped, accepted⟩ := lower_bind_eq_ok.mp accepted
  have empty : others = [] := by simpa using (Except.ok.inj mapped).symm
  subst others
  obtain ⟨_, _, accepted⟩ := lower_bind_eq_ok.mp accepted
  obtain ⟨guard, _, accepted⟩ := lower_bind_eq_ok.mp accepted
  cases guard
  cases accepted
  exact ⟨code, compiled, by simpa using compiledOk, by simp⟩

/-- Applying the exact object expression introduces the real context argument
and executes its emitted runtime body. -/
theorem objectExpression_evaluates {slots : List (String × Core.Ty)} {compiled : Core.Expr}
    {others : List Core.Expr} {images : List (Nat × List UInt8)}
    {codeBytes : Option (List UInt8)} {catalog : List AccountRuntime.CodeDefinition}
    {argument : Core.Expr} {context result : Core.Value} {environment : Core.Environment}
    {initial allocated final : Core.Store}
    (supplied : Core.Evaluates environment initial argument context allocated)
    (evaluated : Core.Evaluates (context :: environment) allocated
      (AccountRuntime.objectRuntime slots compiled others images codeBytes catalog (fun here => .var (here - 0 - 1)) 1)
      result final) :
    Core.Evaluates environment initial
      (.apply (AccountRuntime.objectExpression slots compiled others images codeBytes catalog) argument) result final :=
  .apply .lambda supplied evaluated

end Solcore.Frontend.RustHull.Correspondence
