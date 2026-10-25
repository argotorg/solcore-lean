import Solcore.Frontend.RustHull.AccountInspection
import Solcore.Frontend.RustHull.MemoryCopyCorrespondence
import Solcore.Frontend.RustHull.KeccakHashCorrespondence

/-! Account inspection builders respect the renaming introduced by the actual
outer builtin compiler. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.AccountInspectionCorrespondence
open Core

set_option linter.unusedSimpArgs false in
theorem size_rename (world complete target : Core.Expr) (mapping : Renaming) :
    (AccountInspection.size world complete target).rename mapping =
      AccountInspection.size (world.rename mapping) (complete.rename mapping) (target.rename mapping) := by
  simp only [AccountInspection.size, CodeBuilder.bind, CodeBuilder.constant, bundle, Core.Expr.rename]
  congr 1
  simp [CodeBuilder.bind, AccountInspection.known, CodeBuilder.bindResult, CodeBuilder.part, CodeBuilder.load,
    CodeBuilder.address, CodeBuilder.binary, CodeBuilder.number, CodeBuilder.constant,
    CodeBuilder.choose, CodeBuilder.success, CodeBuilder.failure, projectArgument,
    AccountState.get, AccountState.lookup, AccountState.defaultRecord, bundle,
    LanguageResult.bind, LanguageResult.success, LanguageResult.failure,
    OrderedMapping.lookup, OrderedMapping.lookupBody, OrderedMapping.optionValue, OrderedMapping.invoke,
    OrderedMapping.runHelper, WordMapping.runHelper, WordMapping.invoke, WordMapping.empty, AccountState.equal, OptionalCell.allocate, OptionalCell.read,
    Core.Expr.rename, Core.Expr.renameList, Core.Renaming.lift, Core.Expr.weakenAt]
  all_goals rfl

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 10000 in
theorem copy_rename (world complete memory size target destination source length : Core.Expr) (mapping : Renaming) :
    (AccountInspection.copy world complete memory size target destination source length).rename mapping =
      AccountInspection.copy (world.rename mapping) (complete.rename mapping) (memory.rename mapping)
        (size.rename mapping) (target.rename mapping) (destination.rename mapping)
        (source.rename mapping) (length.rename mapping) := by
  simp only [AccountInspection.copy, CodeBuilder.bind, CodeBuilder.constant, bundle, Core.Expr.rename]
  congr 1
  simp [CodeBuilder.bind, AccountInspection.known, CodeBuilder.bindResult, CodeBuilder.part, CodeBuilder.load,
    CodeBuilder.address, CodeBuilder.binary, CodeBuilder.number, CodeBuilder.constant,
    CodeBuilder.choose, CodeBuilder.failure, projectArgument,
    AccountState.get, AccountState.lookup, AccountState.defaultRecord, bundle,
    MemoryCopyCorrespondence.copyPackedFrom_rename,
    LanguageResult.bind, LanguageResult.success, LanguageResult.failure,
    OrderedMapping.lookup, OrderedMapping.lookupBody, OrderedMapping.optionValue, OrderedMapping.invoke,
    OrderedMapping.runHelper, WordMapping.runHelper, WordMapping.invoke, WordMapping.empty, AccountState.equal, OptionalCell.allocate, OptionalCell.read,
    Core.Expr.rename, Core.Expr.renameList, Core.Renaming.lift, Core.Expr.weakenAt]
  all_goals rfl

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 10000 in
theorem hash_rename (world complete balances target : Core.Expr) (mapping : Renaming) :
    (AccountInspection.hash world complete balances target).rename mapping =
      AccountInspection.hash (world.rename mapping) (complete.rename mapping)
        (balances.rename mapping) (target.rename mapping) := by
  simp only [AccountInspection.hash, CodeBuilder.bind, CodeBuilder.constant, bundle, Core.Expr.rename]
  congr 1
  simp [CodeBuilder.bind, AccountInspection.known, CodeBuilder.bindResult, CodeBuilder.part, CodeBuilder.load,
    CodeBuilder.address, CodeBuilder.binary, CodeBuilder.number, CodeBuilder.constant,
    CodeBuilder.choose, CodeBuilder.success, CodeBuilder.failure, CodeBuilder.boolean,
    CodeBuilder.allocate, CodeBuilder.lookup, projectArgument,
    AccountState.get, AccountState.lookup, AccountState.defaultRecord, bundle,
    KeccakHashCorrespondence.hash_rename,
    LanguageResult.bind, LanguageResult.success, LanguageResult.failure,
    OrderedMapping.lookup, OrderedMapping.lookupBody, OrderedMapping.optionValue, OrderedMapping.invoke,
    OrderedMapping.runHelper, WordMapping.lookup, WordMapping.lookupBody, WordMapping.runHelper,
    WordMapping.invoke, WordMapping.empty, AccountState.equal, OptionalCell.allocate, OptionalCell.read,
    Core.Expr.rename, Core.Expr.renameList, Core.Renaming.lift, Core.Expr.weakenAt]
  all_goals rfl

end Solcore.Frontend.RustHull.AccountInspectionCorrespondence
