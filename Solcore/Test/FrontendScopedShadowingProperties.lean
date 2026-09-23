import Solcore.Frontend.Computation
import Solcore.Frontend.RecursiveComputationReturnTree
import Solcore.Frontend.RecursiveLocalComputation
import Solcore.Frontend.LocalComputation
import Solcore.Frontend.LocalFunctionApplication

/-! Arbitrary repeated spellings retain old initializer scope and exact rows.
These symbolic spans are original fields, not a claim of parser validity. -/

set_option autoImplicit false
namespace Tests.FrontendScopedShadowing
open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"Shadowing", by decide⟩], by decide⟩⟩, 73⟩
private def id (index : Nat) : Resolved.LocalId := ⟨owner, index⟩
private def foreign : Resolved.LocalId := ⟨{owner with declarationIndex := 74}, 900⟩
private def inputs (a b : Core.Ty) : LocalTypeInputs := ⟨
  [⟨"x", id 7, a⟩, ⟨"next", id 2, b⟩, ⟨"x", foreign, .bool⟩],
  by change [id 7, id 2, foreign].Nodup; decide⟩
private def ref (span : Syntax.SourceSpan) (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def annotation (span : Syntax.SourceSpan) : Syntax.TypeExpr :=
  ⟨span, .named ⟨span, ⟨⟨⟨span, "Payload"⟩, []⟩⟩⟩ none⟩
private def types (type : Core.Ty) : TypeNameTable := [(["Payload"], type), (["Payload"], .unit)]
private def statements (span : Syntax.SourceSpan) (annotated : Bool) : List String → String → List Syntax.Statement
  | [], previous => [⟨span, .returnStmt (some (ref span previous))⟩]
  | name :: rest, previous =>
      ⟨span, .letDecl ⟨span, name⟩ (if annotated then some (annotation span) else none)
        (some (ref span previous))⟩ :: statements span annotated rest name
private def core : Nat → Core.Expr
  | 0 => .var 0
  | count + 1 => .letE (.var 0) (core count)

private theorem elaboration (span : Syntax.SourceSpan) (annotated : Bool) (names : List String)
    (previous : String) (type : Core.Ty) (initial : LocalTypeInputs)
    (child : RecursiveLocalComputationElaborates initial.names initial.context (ref span previous) (.var 0) type) :
    RecursiveComputationReturnTreeElaborates (types type) owner initial
      ⟨span, statements span annotated names previous⟩ (core names.length) type := by
  induction names generalizing previous initial with
  | nil => exact .expression child
  | cons name rest ih =>
      have tail := ih name (initial.bindFresh owner name type)
        (.pure (.identifier .head) (.var .head) (.var .head))
      cases annotated with
      | false => exact .inferred child tail
      | true => exact .binding (.named .head) child tail

theorem arbitrary_repeated_names_have_independent_exact_typing
    (span : Syntax.SourceSpan) (annotated : Bool) (names : List String) (type other : Core.Ty) :
    RecursiveComputationReturnTreeElaborates (types type) owner (inputs type other)
      ⟨span, statements span annotated names "x"⟩ (core names.length) type ∧
    RecursiveComputationReturnTreeHasType (types type) owner (inputs type other)
      ⟨span, statements span annotated names "x"⟩ type ∧
    elaborateRecursiveComputationReturnTree? (types type) owner (inputs type other)
      ⟨span, statements span annotated names "x"⟩ = some (core names.length, type) ∧
    Core.HasType [type, other, .bool] (core names.length) type := by
  have exact := elaboration span annotated names "x" type (inputs type other)
    (.pure (.identifier .head) (.var .head) (.var .head))
  exact ⟨exact, (computationReturnTreeHasType_iff_elaborates
    recursiveLocalComputationHasType_iff_elaborates).mpr ⟨_, exact⟩,
    (elaborateComputationReturnTree?_iff elaborateRecursiveLocalComputation?_iff).mpr exact,
    ComputationReturnTreeElaborates.core_hasType RecursiveLocalComputationElaborates.core_hasType exact⟩

private theorem raw (span : Syntax.SourceSpan) (annotated : Bool) (names : List String)
    (previous : String) (table : LocalNameTable) (environment : Resolved.Environment)
    (store : Core.Store) (value : Core.Value)
    (child : RecursiveLocalComputationEvaluatesWithCost table environment store (ref span previous) value store 1) :
    RecursiveComputationReturnTreeEvaluatesWithCost owner table environment store
      ⟨span, statements span annotated names previous⟩ value store (3 * names.length + 1) := by
  induction names generalizing previous table environment with
  | nil => exact .expression child
  | cons name rest ih =>
      let fresh := Resolved.freshLocalId owner (table.map Prod.snd)
      have tail := ih name ((name, fresh) :: table) ((fresh, value) :: environment)
        (.pure (.identifier .head .head))
      have count : 3 * (name :: rest).length + 1 = 1 + (3 * rest.length + 1) + 2 := by
        simp only [List.length_cons]; omega
      rw [count]
      cases annotated with
      | false => exact .inferred child tail
      | true => exact .binding child tail

private theorem path (count : Nat) (value : Core.Value) (retained : Core.Environment)
    (store : Core.Store) (continuation : List Core.Frame) :
    Core.Steps (3 * count + 1) ⟨.eval (core count) (value :: retained), continuation, store⟩
      ⟨.ret value, continuation, store⟩ := by
  induction count generalizing retained continuation with
  | zero => exact .cons (.var rfl) .refl
  | succ count ih =>
      have costs : 3 * (count + 1) + 1 = 1 + (3 * count + 1) + 2 := by omega
      rw [costs]
      exact CostStepComposition.letE (.cons (.var rfl) .refl) (ih (value :: retained) continuation)

theorem arbitrary_repeated_names_preserve_actual_values_stores_and_exact_cost
    (span : Syntax.SourceSpan) (annotated : Bool) (names : List String)
    (value next captured : Core.Value) (store : Core.Store) (continuation : List Core.Frame) :
    RecursiveComputationReturnTreeEvaluatesWithCost owner (inputs .word .word).names
      [(id 7, value), (id 2, next), (foreign, captured)] store
      ⟨span, statements span annotated names "x"⟩ value store (3 * names.length + 1) ∧
    Core.Steps (3 * names.length + 1)
      ⟨.eval (core names.length) [value, next, captured], continuation, store⟩
      ⟨.ret value, continuation, store⟩ :=
  ⟨raw span annotated names "x" _ _ store value (.pure (.identifier .head .head)),
    path names.length value [next, captured] store continuation⟩

private theorem changedType (span : Syntax.SourceSpan) (annotated : Bool) (old next : Core.Ty) :
    RecursiveComputationReturnTreeElaborates (types next) owner (inputs old next)
      ⟨span, statements span annotated ["x"] "next"⟩ (.letE (.var 1) (.var 0)) next := by
  have child : RecursiveLocalComputationElaborates (inputs old next).names (inputs old next).context
      (ref span "next") (.var 1) next :=
    .pure (.identifier (.tail (by change "x" ≠ "next"; decide) .head))
      (.var (.tail (by change id 7 ≠ id 2; decide) .head))
      (.var (.tail (by change id 7 ≠ id 2; decide) .head))
  have tail : RecursiveComputationReturnTreeElaborates (types next) owner
      ((inputs old next).bindFresh owner "x" next) ⟨span, statements span annotated [] "x"⟩ (.var 0) next :=
    .expression (.pure (.identifier .head) (.var .head) (.var .head))
  cases annotated with
  | false => exact .inferred child tail
  | true => exact .binding (.named .head) child tail

theorem a_new_type_shadows_the_name_without_overwriting_old_rows
    (span : Syntax.SourceSpan) (annotated : Bool) (old next : Core.Ty) :
    elaborateRecursiveComputationReturnTree? (types next) owner (inputs old next)
      ⟨span, statements span annotated ["x"] "next"⟩ = some (.letE (.var 1) (.var 0), next) ∧
    ((inputs old next).bindFresh owner "x" next).names =
      [("x", id 8), ("x", id 7), ("next", id 2), ("x", foreign)] ∧
    ((inputs old next).bindFresh owner "x" next).context =
      [(id 8, next), (id 7, old), (id 2, next), (foreign, .bool)] :=
  ⟨(elaborateComputationReturnTree?_iff elaborateRecursiveLocalComputation?_iff).mpr
    (changedType span annotated old next), rfl, rfl⟩

theorem original_initializer_and_shadowed_tail_select_different_rows
    (span : Syntax.SourceSpan) (old next : Core.Ty) :
    elaborateRecursiveLocalComputation? (inputs old next).names (inputs old next).context
      (ref span "x") = some (.var 0, old) ∧
    elaborateRecursiveLocalComputation? ((inputs old next).bindFresh owner "x" next).names
      ((inputs old next).bindFresh owner "x" next).context (ref span "x") = some (.var 0, next) ∧
    (inputs old next).names.lookup? "x" = some (id 7) ∧
    ((inputs old next).bindFresh owner "x" next).names.lookup? "x" = some (id 8) ∧
    ((inputs old next).bindFresh owner "x" next).context.lookup? (id 7) = some old ∧
    Resolved.freshLocalId owner (inputs old next).ids = id 8 ∧
    ((inputs old next).bindFresh owner "x" next).context.values = [next, old, next, .bool] :=
  ⟨elaborateRecursiveLocalComputation?_iff.mpr (.pure (.identifier .head) (.var .head) (.var .head)),
    elaborateRecursiveLocalComputation?_iff.mpr (.pure (.identifier .head) (.var .head) (.var .head)),
    rfl, rfl, rfl, rfl, rfl⟩

end Tests.FrontendScopedShadowing
