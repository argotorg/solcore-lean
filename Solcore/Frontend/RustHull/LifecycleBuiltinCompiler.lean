import Solcore.Frontend.RustHull.EffectBuiltinCorrespondenceSupport
import Solcore.Frontend.RustHull.AccountLifecycleCorrespondence

/-! Successful SELFDESTRUCT lowering resolves account references and both
termination branches before it emits the static guard and shared updates. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.LifecycleBuiltinCorrespondence
open Core Correspondence PureCallCorrespondence EffectBuiltinCorrespondence

structure References where
  world : Core.Expr
  balances : Core.Expr
  address : Core.Expr
  complete : Core.Expr
  isStatic : Core.Expr

structure CompiledReferences (scope : Scope) (references : References) : Prop where
  world : Effects.reference scope "world" AccountState.type = .ok references.world
  balances : Effects.reference scope "balances" WordMapping.type = .ok references.balances
  address : Effects.reference scope "address" .word = .ok references.address
  complete : Effects.reference scope "worldComplete" .bool = .ok references.complete
  isStatic : Effects.reference scope "isStatic" .bool = .ok references.isStatic

def expression (references : References) (beneficiary invalid stopped : Core.Expr) : Core.Expr :=
  .ifE (.loadCell references.isStatic) invalid
    (LocalSequence.discard .unit
      (AccountLifecycle.destroy references.world references.balances (.loadCell references.address)
        beneficiary (.loadCell references.complete)) stopped)

theorem inner_arity {scope : Scope} {arguments : List Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope "selfdestruct" arguments = .ok lowered) :
    arguments.length = 1 := by
  rcases arguments with _ | ⟨first, _ | ⟨second, rest⟩⟩
  all_goals first
    | rfl
    | change Except.error _ = Except.ok lowered at compiled
      cases compiled

theorem inner_components {scope : Scope} {beneficiary : Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope "selfdestruct" [beneficiary] = .ok lowered) :
    ∃ references invalid stopped, CompiledReferences scope references ∧
      Effects.terminate scope 3 (.word Word.zero) (.word Word.zero) = .ok invalid ∧
      Effects.terminate scope 1 (.word Word.zero) (.word Word.zero) = .ok stopped ∧
      lowered = ⟨.unit, expression references beneficiary invalid stopped⟩ := by
  change (do
    let world ← Effects.reference scope "world" AccountState.type
    let balances ← Effects.reference scope "balances" WordMapping.type
    let address ← Effects.reference scope "address" .word
    let complete ← Effects.reference scope "worldComplete" .bool
    let isStatic ← Effects.reference scope "isStatic" .bool
    let invalid ← Effects.terminate scope 3 (.word Word.zero) (.word Word.zero)
    let stopped ← Effects.terminate scope 1 (.word Word.zero) (.word Word.zero)
    pure (Lowered.mk .unit (expression ⟨world, balances, address, complete, isStatic⟩ beneficiary invalid stopped))) = .ok lowered at compiled
  obtain ⟨world, worldCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨balances, balancesCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨address, addressCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨complete, completeCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨isStatic, staticCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨invalid, invalidCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨stopped, stoppedCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
  exact ⟨⟨world, balances, address, complete, isStatic⟩, invalid, stopped,
    ⟨worldCompiled, balancesCompiled, addressCompiled, completeCompiled, staticCompiled⟩,
    invalidCompiled, stoppedCompiled, (Except.ok.inj returned).symm⟩

def References.rename (references : References) (mapping : Renaming) : References :=
  ⟨references.world.rename mapping, references.balances.rename mapping, references.address.rename mapping,
    references.complete.rename mapping, references.isStatic.rename mapping⟩

open CodeBuilder in
private def destroyCode (worldReference balancesReference currentAddress beneficiary complete : Core.Expr) : Core.Expr :=
  (bind (constant (bundle [worldReference, balancesReference, currentAddress, beneficiary, complete])) fun args =>
    let world := part 0 5 args
    let balances := part 1 5 args
    bind (address (part 2 5 args)) fun current =>
    bind (address (part 3 5 args)) fun recipient =>
    bindResult .unit (fun depth => AccountState.get (load world depth) (current depth)
      (part 4 5 args depth)) fun record =>
    let finish := AccountLifecycleCorrespondence.publishCode world balances current record
    bindResult .unit (lookup (load balances) current) fun amount =>
    choose (binary .wordEq current recipient)
      (choose (part 7 9 record)
        (choose (binary .wordEq amount (number 0)) (finish (load balances))
          (bindResult .unit (insert (load balances) current (number 0)) finish))
        (success unit))
      (choose (binary .wordEq amount (number 0)) (finish (load balances))
        (bindResult .unit (lookup (load balances) recipient) fun recipientBalance =>
          choose (binary .wordGt recipientBalance (binary .wordSub (number (wordModulus - 1)) amount))
            (failure .unit (constant (.word AccountLifecycle.balanceOverflowReason)))
            (bindResult .unit (insert (load balances) current (number 0)) fun debited =>
              bindResult .unit (insert debited recipient (binary .wordAdd recipientBalance amount)) finish)))) 0


set_option linter.unusedSimpArgs false in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
theorem destroy_rename (world balances address beneficiary complete : Core.Expr) (mapping : Renaming) :
    (AccountLifecycle.destroy world balances address beneficiary complete).rename mapping =
      AccountLifecycle.destroy (world.rename mapping) (balances.rename mapping) (address.rename mapping)
        (beneficiary.rename mapping) (complete.rename mapping) := by
  change (destroyCode world balances address beneficiary complete).rename mapping =
    destroyCode (world.rename mapping) (balances.rename mapping) (address.rename mapping)
      (beneficiary.rename mapping) (complete.rename mapping)
  simp only [destroyCode, CodeBuilder.bind, CodeBuilder.constant, bundle, Core.Expr.rename]
  congr 1
  simp [CodeBuilder.bind, CodeBuilder.bindResult, CodeBuilder.part, CodeBuilder.load,
    CodeBuilder.address, CodeBuilder.binary, CodeBuilder.number, CodeBuilder.constant,
    CodeBuilder.choose, CodeBuilder.success, CodeBuilder.failure, CodeBuilder.boolean,
    CodeBuilder.lookup, CodeBuilder.insert, CodeBuilder.store, CodeBuilder.unit, projectArgument,
    AccountState.get, AccountState.lookup, AccountState.defaultRecord, AccountState.put,
    AccountLifecycleCorrespondence.publishCode, AccountState.replace, AccountState.field, bundle, LanguageResult.bind, LanguageResult.success, LanguageResult.failure,
    OrderedMapping.lookup, OrderedMapping.lookupBody, OrderedMapping.optionValue, OrderedMapping.invoke,
    OrderedMapping.runHelper, WordMapping.lookup, WordMapping.lookupBody, WordMapping.insert,
    WordMapping.insertBody, WordMapping.runHelper, WordMapping.invoke, WordMapping.empty, WordMapping.cons,
    OrderedMapping.insert, OrderedMapping.insertBody, OrderedMapping.cons,
    AccountState.equal, OptionalCell.allocate, OptionalCell.read, Core.Expr.rename, Core.Expr.renameList,
    Core.Renaming.lift, Core.Expr.weakenAt]
  all_goals (repeat' apply And.intro)
  all_goals rfl

theorem expression_rename (references : References) (beneficiary invalid stopped : Core.Expr) (mapping : Renaming) :
    (expression references beneficiary invalid stopped).rename mapping =
      expression (references.rename mapping) (beneficiary.rename mapping) (invalid.rename mapping) (stopped.rename mapping) := by
  simp only [expression, Core.Expr.rename, LocalSequence.discard, LanguageResult.bind,
    destroy_rename, References.rename]
  congr 2
  rw [← Core.Expr.rename_insertion, ← Core.Expr.rename_insertion, Core.Expr.rename_comp, Core.Expr.rename_comp]
  congr 1

end Solcore.Frontend.RustHull.LifecycleBuiltinCorrespondence
