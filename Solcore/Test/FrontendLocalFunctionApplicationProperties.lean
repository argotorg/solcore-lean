import Solcore.Frontend.LocalFunctionApplicationProperties
import Solcore.Frontend.ReturnBody
import Solcore.Core.LocalFragment
import Solcore.Core.FuelResumptionProperties

/-! Original single arguments and independent child provenance determine the
application. Static contexts are separate from actual values and store safety. -/
set_option autoImplicit false
namespace Tests.FrontendLocalFunctionApplication
open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"Application", by decide⟩], by decide⟩⟩, 4⟩
private def foreign : Resolved.DeclarationId := { owner with declarationIndex := 91 }
private def fid : Resolved.LocalId := ⟨owner, 17⟩
private def aid : Resolved.LocalId := ⟨foreign, 999⟩
private def gid : Resolved.LocalId := ⟨owner, 3⟩
private def cid : Resolved.LocalId := ⟨foreign, 2⟩
private def names : LocalNameTable := [("f", fid), ("f", gid), ("x", aid), ("c", cid)]
private def context (a b : Core.Ty) : Resolved.Context :=
  [(aid, a), (fid, .function a b), (gid, .function a b), (cid, .bool), (fid, .word)]
private structure Ranges where
  root : Syntax.SourceSpan
  arguments : Syntax.SourceSpan
  callee : Syntax.SourceSpan
  calleeName : Syntax.SourceSpan
  argument : Syntax.SourceSpan
  argumentName : Syntax.SourceSpan
private def badSpan : Syntax.SourceSpan := ⟨⟨.main, "local-call.sol"⟩, 37, 2⟩
private def ranges : Ranges := ⟨badSpan, badSpan, badSpan, badSpan, badSpan, badSpan⟩
private def ref (span nameSpan : Syntax.SourceSpan) (name : String) : Syntax.Expr :=
  ⟨span, .identifier ⟨nameSpan, name⟩⟩
private def groups : List Syntax.SourceSpan → Syntax.Expr → Syntax.Expr
  | [], source => source
  | span :: rest, source => ⟨span, .group (groups rest source)⟩
private theorem groupResolution {table : LocalNameTable} {source : Syntax.Expr} {resolved : Resolved.Expr}
    (evidence : ResolvesLocalExpression table source resolved) (spans : List Syntax.SourceSpan) :
    ResolvesLocalExpression table (groups spans source) resolved := by
  induction spans with
  | nil => exact evidence
  | cons _ _ ih => exact .group ih
private theorem groupTyping {table : LocalNameTable} {ctx : Resolved.Context} {source : Syntax.Expr} {type : Core.Ty}
    (evidence : LocalExpressionHasType table ctx source type) (spans : List Syntax.SourceSpan) :
    LocalExpressionHasType table ctx (groups spans source) type := by
  induction spans with
  | nil => exact evidence
  | cons _ _ ih => exact .group ih
private def source (r : Ranges) (fs xs : List Syntax.SourceSpan) : Syntax.Expr :=
  ⟨r.root, .call (groups fs (ref r.callee r.calleeName "f"))
    ⟨r.arguments, [groups xs (ref r.argument r.argumentName "x")]⟩⟩
private def core : Core.Expr := .apply (.var 1) (.var 0)
private theorem exactCall (a b : Core.Ty) (r : Ranges) (fs xs : List Syntax.SourceSpan) :
    LocalFunctionApplicationElaborates names (context a b) (source r fs xs) core b :=
  .call (parameterType := a)
    (groupResolution (table := names) (source := ref r.callee r.calleeName "f") (.identifier .head) fs)
    (.var (.tail (by change aid ≠ fid; decide) .head)) (.var (.tail (by change aid ≠ fid; decide) .head))
    (groupResolution (table := names) (source := ref r.argument r.argumentName "x")
      (.identifier (.tail (by change "f" ≠ "x"; decide) (.tail (by change "f" ≠ "x"; decide) .head))) xs) (.var .head) (.var .head)
private theorem typedCall (a b : Core.Ty) (r : Ranges) (fs xs : List Syntax.SourceSpan) :
    LocalFunctionApplicationHasType names (context a b) (source r fs xs) b :=
  .call (parameterType := a)
    (groupTyping (table := names) (ctx := context a b) (source := ref r.callee r.calleeName "f")
      (.identifier .head (.tail (by change aid ≠ fid; decide) .head)) fs)
    (groupTyping (table := names) (ctx := context a b) (source := ref r.argument r.argumentName "x")
      (.identifier (.tail (by change "f" ≠ "x"; decide) (.tail (by change "f" ≠ "x"; decide) .head)) .head) xs)

theorem arbitrary_groups_spans_and_types_retain_exact_original_children
    (a b : Core.Ty) (r : Ranges) (fs xs : List Syntax.SourceSpan) (definitions : Core.DataEnvironment) :
    LocalFunctionApplicationElaborates names (context a b) (source r fs xs) core b ∧
    LocalFunctionApplicationHasType names (context a b) (source r fs xs) b ∧
    elaborateLocalFunctionApplication? names (context a b) (source r fs xs) = some (core, b) ∧
    Core.HasType (Resolved.LocalScope.values (context a b)) core b definitions :=
  ⟨exactCall a b r fs xs, typedCall a b r fs xs, (exactCall a b r fs xs).complete,
    .apply (.var rfl) (.var rfl)⟩

theorem sparse_and_duplicate_rows_are_first_match_not_freshness_preconditions (a b : Core.Ty) :
    ¬ (names.map Prod.fst).Nodup ∧ ¬ (Resolved.LocalScope.ids (context a b)).Nodup ∧
    names.lookup? "f" = some fid ∧ (context a b).lookup? fid = some (.function a b) ∧
    elaborateLocalFunctionApplication? names (context a b) (source ranges [] []) = some (core, b) :=
  ⟨by decide, by simp [context, Resolved.LocalScope.ids, fid, aid, gid, cid, owner, foreign], rfl, rfl,
    (exactCall a b ranges [] []).complete⟩

theorem same_typed_other_function_is_not_the_original_application
    (a b : Core.Ty) (r : Ranges) (fs xs : List Syntax.SourceSpan) (definitions : Core.DataEnvironment) :
    Core.HasType (Resolved.LocalScope.values (context a b)) (.apply (.var 2) (.var 0)) b definitions ∧
    ¬ LocalFunctionApplicationElaborates names (context a b) (source r fs xs) (.apply (.var 2) (.var 0)) b := by
  refine ⟨.apply (.var rfl) (.var rfl), ?_⟩
  intro wrong
  have same := (exactCall a b r fs xs).result_unique wrong
  cases same.1

theorem all_static_correspondences_keep_the_candidate_core_and_type
    (a b : Core.Ty) (r : Ranges) (fs xs : List Syntax.SourceSpan) (candidate : Core.Expr) (result : Core.Ty) :
    (elaborateLocalFunctionApplication? names (context a b) (source r fs xs) = some (candidate, result) ↔
      candidate = core ∧ result = b) ∧
    (LocalFunctionApplicationHasType names (context a b) (source r fs xs) result ↔ result = b) ∧
    Core.HasType (Resolved.LocalScope.values (context a b)) core b ∧
    Core.infer? (Resolved.LocalScope.values (context a b)) core = some b := by
  have original := exactCall a b r fs xs
  refine ⟨⟨fun accepted => (elaborateLocalFunctionApplication?_sound accepted).result_unique original,
    ?_⟩, ⟨fun typing => typing.type_unique original.hasType, ?_⟩,
    elaborateLocalFunctionApplication?_core_hasType original.complete, Core.infer_complete original.core_hasType⟩
  · rintro ⟨rfl, rfl⟩
    exact elaborateLocalFunctionApplication?_iff.mpr original
  · intro same; cases same
    exact localFunctionApplicationHasType_iff_elaborates.mpr (typedCall a b r fs xs).elaborates_exact

theorem original_child_decomposition_keeps_order_and_the_unique_argument
    (a b : Core.Ty) (r : Ranges) (fs xs : List Syntax.SourceSpan) :
    elaborateLocalExpression? names (context a b) (groups fs (ref r.callee r.calleeName "f")) =
      some (.var 1, .function a b) ∧
    elaborateLocalExpression? names (context a b) (groups xs (ref r.argument r.argumentName "x")) = some (.var 0, a) := by
  obtain ⟨functionCore, argumentCore, parameterType, functionChecked, argumentChecked, shape⟩ :=
    elaborateLocalFunctionApplication?_children.mp (exactCall a b r fs xs).complete
  have indices := Core.Expr.apply.inj shape
  cases indices.1; cases indices.2
  have actualArgument := elaborateLocalExpression?_complete (table := names) (context := context a b)
    (groupResolution (table := names) (source := ref r.argument r.argumentName "x")
      (.identifier (.tail (by change "f" ≠ "x"; decide) (.tail (by change "f" ≠ "x"; decide) .head))) xs)
    (.var (.head : Resolved.LocalScope.IndexOf (Resolved.LocalScope.ids (context a b)) aid 0))
    (.var (.head : Resolved.LocalScope.Lookup (context a b) aid a))
  have same := Prod.mk.inj (Option.some.inj (argumentChecked.symm.trans actualArgument))
  cases same.2
  exact ⟨functionChecked, argumentChecked⟩

theorem nominal_static_types_do_not_supply_runtime_arguments (a b : Core.DataTypeId) :
    elaborateLocalFunctionApplication? names (context (.namedData a) (.namedData b)) (source ranges [] []) =
      some (core, .namedData b) ∧
    Core.ValueHasType (.closure (.namedData a) (.namedData a) (.var 0) [])
      (.function (.namedData a) (.namedData a)) ∧ ¬ ∃ value, Core.ValueHasType value (.namedData a) := by
  refine ⟨(exactCall _ _ ranges [] []).complete, .closure .nil (.var rfl), ?_⟩
  rintro ⟨value, typed⟩
  cases typed with
  | constructed found _ => simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found

private def unit : Syntax.Expr := ⟨badSpan, .tuple ⟨badSpan, []⟩⟩
private def pair : Syntax.Expr := ⟨badSpan, .tuple ⟨badSpan, [unit, unit]⟩⟩
private def call (args : List Syntax.Expr) : Syntax.Expr :=
  ⟨badSpan, .call (ref badSpan badSpan "f") ⟨badSpan, args⟩⟩
private theorem unitCall (b : Core.Ty) :
    LocalFunctionApplicationElaborates names (context .unit b) (call [unit]) (.apply (.var 1) .unit) b :=
  .call (.identifier .head) (.var (.tail (by decide) .head)) (.var (.tail (by decide) .head)) .unit .unit .unit
private theorem pairCall (b : Core.Ty) : LocalFunctionApplicationElaborates names (context (.product .unit .unit) b)
    (call [pair]) (.apply (.var 1) (.pair .unit .unit)) b :=
  .call (.identifier .head) (.var (.tail (by decide) .head)) (.var (.tail (by decide) .head))
    (.pair .unit .unit) (.pair .unit .unit) (.pair .unit .unit)
theorem a_unit_or_product_argument_is_one_written_argument (b : Core.Ty) :
    elaborateLocalFunctionApplication? names (context .unit b) (call [unit]) = some (.apply (.var 1) .unit, b) ∧
    elaborateLocalFunctionApplication? names (context (.product .unit .unit) b) (call [pair]) =
      some (.apply (.var 1) (.pair .unit .unit), b) ∧
    elaborateLocalFunctionApplication? names (context .unit b) (call []) = none ∧
    elaborateLocalFunctionApplication? names (context (.product .unit .unit) b) (call [unit, unit]) = none :=
  ⟨(unitCall b).complete, (pairCall b).complete, rfl, rfl⟩

theorem zero_arguments_cannot_acquire_an_implicit_unit (b : Core.Ty) :
    ¬ ∃ type, LocalFunctionApplicationHasType names (context .unit b) (call []) type :=
  elaborateLocalFunctionApplication?_eq_none_iff.mp rfl

theorem old_pure_children_do_not_recursively_adopt_applications (a b : Core.Ty) :
    elaborateLocalFunctionApplication? names (context a b) ⟨badSpan, .group (source ranges [] [])⟩ = none ∧
    elaborateLocalFunctionApplication? names (context a b) (call [source ranges [] []]) = none ∧
    elaborateLocalFunctionApplication? names (context a b)
      ⟨badSpan, .call (source ranges [] []) ⟨badSpan, [unit]⟩⟩ = none := by
  simp [elaborateLocalFunctionApplication?, call, source, groups, elaborateLocalExpression?, resolveLocalExpression?]

theorem exact_application_is_outside_the_old_pure_and_body_profiles
    (a b : Core.Ty) (r : Ranges) (fs xs : List Syntax.SourceSpan) :
    elaborateLocalExpression? names (context a b) (source r fs xs) = none ∧
    elaborateReturnBody? names (context a b) ⟨r.root, [⟨r.arguments, .returnStmt (some (source r fs xs))⟩]⟩ = none ∧
    ¬ Core.Expr.LocalFragment core := ⟨by simp [source, elaborateLocalExpression?, resolveLocalExpression?],
      by simp [elaborateReturnBody?, source, elaborateLocalExpression?, resolveLocalExpression?],
      by intro fragment; cases fragment⟩

private def conditional (left right : Syntax.Expr) : Syntax.Expr :=
  ⟨badSpan, .conditional (ref badSpan badSpan "c") badSpan left badSpan right⟩
private def fn : Syntax.Expr := ref badSpan badSpan "f"
private def arg : Syntax.Expr := ref badSpan badSpan "x"
private def missing : Syntax.Expr := ref badSpan badSpan "missing"
private theorem conditionalCall (a b : Core.Ty) : LocalFunctionApplicationElaborates names (context a b)
    ⟨badSpan, .call (conditional fn fn) ⟨badSpan, [conditional arg arg]⟩⟩
    (.apply (.ifE (.var 3) (.var 1) (.var 1)) (.ifE (.var 3) (.var 0) (.var 0))) b :=
  .call (.conditional (.identifier (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
      (.identifier .head) (.identifier .head))
    (.ifE (.var (.tail (by change aid ≠ cid; decide) (.tail (by change fid ≠ cid; decide) (.tail (by change gid ≠ cid; decide) .head))))
      (.var (.tail (by change aid ≠ fid; decide) .head)) (.var (.tail (by change aid ≠ fid; decide) .head)))
    (.ifE (.var (.tail (by change aid ≠ cid; decide) (.tail (by change fid ≠ cid; decide) (.tail (by change gid ≠ cid; decide) .head))))
      (.var (.tail (by change aid ≠ fid; decide) .head)) (.var (.tail (by change aid ≠ fid; decide) .head)))
    (.conditional (.identifier (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
      (.identifier (.tail (by decide) (.tail (by decide) .head))) (.identifier (.tail (by decide) (.tail (by decide) .head))))
    (.ifE (.var (.tail (by change aid ≠ cid; decide) (.tail (by change fid ≠ cid; decide) (.tail (by change gid ≠ cid; decide) .head)))) (.var .head) (.var .head))
    (.ifE (.var (.tail (by change aid ≠ cid; decide) (.tail (by change fid ≠ cid; decide) (.tail (by change gid ≠ cid; decide) .head)))) (.var .head) (.var .head))
theorem both_conditional_children_are_checked_in_the_original_scope (a b : Core.Ty) :
    elaborateLocalFunctionApplication? names (context a b)
      ⟨badSpan, .call (conditional fn fn) ⟨badSpan, [conditional arg arg]⟩⟩ =
      some (.apply (.ifE (.var 3) (.var 1) (.var 1)) (.ifE (.var 3) (.var 0) (.var 0)), b) ∧
    elaborateLocalFunctionApplication? names (context a b) (call [conditional arg missing]) = none ∧
    elaborateLocalFunctionApplication? names (context a b)
      ⟨badSpan, .call (conditional fn missing) ⟨badSpan, [arg]⟩⟩ = none := by
  refine ⟨(conditionalCall a b).complete, ?_, ?_⟩ <;>
    simp [elaborateLocalFunctionApplication?, call, conditional, fn, arg, missing, ref, elaborateLocalExpression?,
      resolveLocalExpression?, LocalNameTable.lookup?, names]

theorem nonfunction_wrong_argument_and_mixed_conditional_types_do_not_coerce :
    elaborateLocalFunctionApplication? names [(fid, .bool), (aid, .unit)] (source ranges [] []) = none ∧
    elaborateLocalFunctionApplication? names (context .word .bool) (call [unit]) = none ∧
    elaborateLocalFunctionApplication? names (context .word .bool) (call [conditional arg unit]) = none ∧
    elaborateLocalFunctionApplication? names (context .word .bool)
      ⟨badSpan, .call (conditional fn arg) ⟨badSpan, [arg]⟩⟩ = none := by
  simp only [elaborateLocalFunctionApplication?, source, groups, call, conditional, fn, arg, unit, ref,
    elaborateLocalExpression?, resolveLocalExpression?, names, LocalNameTable.lookup?]
  exact ⟨rfl, rfl, rfl, rfl⟩

private def identity (type : Core.Ty) : Core.Value := .closure type type (.var 0) []
private theorem identityPath (type : Core.Ty) (value : Core.Value) (store : Core.Store) (k : List Core.Frame) :
    Core.Steps 6 ⟨.eval core [value, identity type], k, store⟩ ⟨.ret value, k, store⟩ :=
  .cons .enterApply (.cons (.var rfl) (.cons .beginArgument (.cons (.var rfl)
    (.cons .invokeClosure (.cons (.var rfl) .refl)))))
theorem actual_identity_paths_keep_their_continuation_without_claiming_source_evaluation
    (type : Core.Ty) (value : Core.Value) (store : Core.Store) (k : List Core.Frame) :
    Core.Steps 6 ⟨.eval core [value, identity type], k, store⟩ ⟨.ret value, k, store⟩ ∧
    Core.runStateful 6 (Core.State.initial core [value, identity type] store) = .done value store ∧
    Core.runStateful 3 (Core.State.initial core [value, identity type] store) =
      .outOfFuel ⟨.eval (.var 0) [value, identity type], [.applyClosure type type (.var 0) []], store⟩ :=
  ⟨identityPath type value store k, rfl, rfl⟩

private def reader : Core.Value := .closure (.cell .word) .word (.loadCell (.var 0)) []
private def readerEnvironment (location : Core.Location) : Core.Environment :=
  [.cellRef .word location, reader, reader, .bool false, .word .zero]
theorem structurally_typed_actual_values_do_not_prove_cells_allocated (location : Core.Location) :
    elaborateLocalFunctionApplication? names (context (.cell .word) .word) (source ranges [] []) = some (core, .word) ∧
    Core.EnvironmentHasTypes (readerEnvironment location) (Resolved.LocalScope.values (context (.cell .word) .word)) ∧
    Core.runStateful 7 (Core.State.initial core (readerEnvironment location) []) =
      .fault (.invalidCellLocation location) ⟨.ret (.cellRef .word location), [.loadCellApply], []⟩ :=
  ⟨(exactCall _ _ ranges [] []).complete,
    .cons .cellRef (.cons (.closure .nil (.loadCell (.var rfl) .word))
      (.cons (.closure .nil (.loadCell (.var rfl) .word)) (.cons .bool (.cons .word .nil)))), rfl⟩

end Tests.FrontendLocalFunctionApplication
