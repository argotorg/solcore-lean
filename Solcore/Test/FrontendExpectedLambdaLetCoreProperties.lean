import Solcore.Frontend.Expected
import Solcore.Frontend.RecursiveComputationReturnTree
import Solcore.Frontend.RecursiveLocalComputation
import Solcore.Frontend.LocalFunctionApplication
import Solcore.Core.FuelResumptionProperties

/-! An original lambda-let calls the old captured function, while the tail calls
the newly bound closure. Paths below are Core consumers with actual values and
stores, not raw source evaluation or a runtime-typing guarantee. -/
set_option autoImplicit false
namespace Tests.ExpectedLambdaLetCore
open Solcore Solcore.Frontend
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"LambdaLetCore",by decide⟩],by decide⟩⟩,151⟩
private def span : Syntax.SourceSpan := ⟨⟨.main,"lambda-let-core.sol"⟩,0,73⟩
private def types (a b : Core.Ty) : TypeNameTable := [(["F"],.function a b)]
private def annotation : Syntax.TypeExpr := ⟨span,.named ⟨span,⟨⟨⟨span,"F"⟩,[]⟩⟩⟩ none⟩
private def ref (name : String) : Syntax.Expr := ⟨span,.identifier ⟨span,name⟩⟩
private def call (name : String) : Syntax.Expr := ⟨span,.call (ref "f") ⟨span,[ref name]⟩⟩
private def returned (e : Syntax.Expr) : Syntax.Block := ⟨span,[⟨span,.returnStmt (some e)⟩]⟩
private def lambda : Syntax.Expr :=
  ⟨span,.lambda span ⟨span,[⟨span,.inferred ⟨span,"x"⟩⟩]⟩ none (returned (call "x"))⟩
private def source (tail : Syntax.Expr) : Syntax.Block :=
  ⟨span,⟨span,.letDecl ⟨span,"f"⟩ (some annotation) (some lambda)⟩ :: (returned tail).value⟩
private def outer (a b : Core.Ty) : LocalTypeInputs :=
  ⟨[{name:="f",id:=⟨owner,3⟩,type:=.function a b},{name:="arg",id:=⟨owner,7⟩,type:=a}],
    by change ([⟨owner,3⟩,⟨owner,7⟩] : List Resolved.LocalId).Nodup; decide⟩
private def inner (a b : Core.Ty) := (outer a b).bindFresh owner "x" a
private def tailScope (a b : Core.Ty) := (outer a b).bindFresh owner "f" (.function a b)
private def lambdaBody : Core.Expr := .apply (.var 1) (.var 0)
private def core (a b : Core.Ty) (tail : Core.Expr) : Core.Expr := .letE (.lambda a b lambdaBody) tail
private theorem fresh_old_f : (Resolved.freshLocalId owner (outer .word .word).ids) ≠ ⟨owner,3⟩ := by decide
private theorem fresh_arg : (Resolved.freshLocalId owner (outer .word .word).ids) ≠ ⟨owner,7⟩ := by decide
private theorem old_f_arg : (⟨owner,3⟩ : Resolved.LocalId) ≠ ⟨owner,7⟩ := by decide
private theorem header (a b : Core.Ty) :
    ExpectedUnaryLambdaHeaderDeclares (types a b) owner (outer a b) lambda (.function a b)
      ⟨inner a b,returned (call "x"),a,b⟩ := .lambda .inferred .omitted
private theorem initializerTyped (a b : Core.Ty) (wa : Core.Ty.WellFormed [] a) (wb : Core.Ty.WellFormed [] b) :
    ExpectedComputationLambdaHasType RecursiveLocalComputationHasType (types a b) owner
      (outer a b) lambda (.function a b) :=
  .lambda (header a b) wa wb (.expression (.application
    (.pure (.identifier (.tail (by change "x" ≠ "f"; decide) .head) (.tail fresh_old_f .head)))
    (.pure (.identifier .head .head))))
private theorem initializerElab (a b : Core.Ty) (wa : Core.Ty.WellFormed [] a) (wb : Core.Ty.WellFormed [] b) :
    ExpectedComputationLambdaElaborates RecursiveLocalComputationElaborates (types a b) owner
      (outer a b) lambda (.lambda a b lambdaBody) (.function a b) :=
  .lambda (header a b) wa wb (.expression (.application
    (.pure (.identifier (.tail (by change "x" ≠ "f"; decide) .head))
      (.var (.tail fresh_old_f .head)) (.var (.tail fresh_old_f .head)))
    (.pure (.identifier .head) (.var .head) (.var .head))))
private theorem tailTyped (a b : Core.Ty) :
    RecursiveComputationReturnTreeHasType (types a b) owner (tailScope a b) (returned (call "arg")) b :=
  .expression (.application (.pure (.identifier .head .head))
    (.pure (.identifier (.tail (by change "f" ≠ "arg"; decide) (.tail (by change "f" ≠ "arg"; decide) .head))
      (.tail fresh_arg (.tail old_f_arg .head)))))
private theorem tailElab (a b : Core.Ty) :
    RecursiveComputationReturnTreeElaborates (types a b) owner (tailScope a b)
      (returned (call "arg")) (.apply (.var 0) (.var 2)) b :=
  .expression (.application (.pure (.identifier .head) (.var .head) (.var .head))
    (.pure (.identifier (.tail (by change "f" ≠ "arg"; decide) (.tail (by change "f" ≠ "arg"; decide) .head)))
      (.var (.tail fresh_arg (.tail old_f_arg .head))) (.var (.tail fresh_arg (.tail old_f_arg .head)))))

theorem original_source_typing_precedes_the_literal_core_and_checker
    (a b : Core.Ty) (wa : Core.Ty.WellFormed [] a) (wb : Core.Ty.WellFormed [] b) :
    ExpectedLambdaLetBodyHasType RecursiveLocalComputationHasType (types a b) owner (outer a b) (source (call "arg")) b ∧
    ExpectedLambdaLetBodyElaborates RecursiveLocalComputationElaborates (types a b) owner (outer a b)
      (source (call "arg")) (core a b (.apply (.var 0) (.var 2))) b ∧
    elaborateExpectedLambdaLetBody? elaborateRecursiveLocalComputation? (types a b) owner (outer a b)
      (source (call "arg"))=some (core a b (.apply (.var 0) (.var 2)),b) ∧
    Core.HasType (outer a b).context.values (core a b (.apply (.var 0) (.var 2))) b := by
  have sourceTyping : ExpectedLambdaLetBodyHasType RecursiveLocalComputationHasType (types a b) owner (outer a b)
      (source (call "arg")) b := .binding (.named .head) (initializerTyped a b wa wb) (tailTyped a b)
  have elaboration : ExpectedLambdaLetBodyElaborates RecursiveLocalComputationElaborates (types a b) owner (outer a b)
      (source (call "arg")) (core a b (.apply (.var 0) (.var 2))) b :=
    .binding (.named .head) (initializerElab a b wa wb) (tailElab a b)
  exact ⟨sourceTyping,elaboration,(elaborateExpectedLambdaLetBody?_iff elaborateRecursiveLocalComputation?_iff).mpr elaboration,
    elaboration.core_hasType RecursiveLocalComputationElaborates.core_hasType⟩

theorem returning_the_new_closure_is_also_an_independently_typed_original_tail
    (a b : Core.Ty) (wa : Core.Ty.WellFormed [] a) (wb : Core.Ty.WellFormed [] b) :
    ExpectedLambdaLetBodyHasType RecursiveLocalComputationHasType (types a b) owner (outer a b)
      (source (ref "f")) (.function a b) ∧
    ExpectedLambdaLetBodyElaborates RecursiveLocalComputationElaborates (types a b) owner (outer a b)
      (source (ref "f")) (core a b (.var 0)) (.function a b) := by
  exact ⟨.binding (.named .head) (initializerTyped a b wa wb) (.expression (.pure (.identifier .head .head))),
    .binding (.named .head) (initializerElab a b wa wb) (.expression (.pure (.identifier .head) (.var .head) (.var .head)))⟩

theorem the_reused_fresh_number_has_two_distinct_original_scopes (a b : Core.Ty) :
    (inner a b).bindings=
      {name:="x",id:=⟨owner,8⟩,type:=a} :: (outer a b).bindings ∧
    (tailScope a b).bindings=
      {name:="f",id:=⟨owner,8⟩,type:=.function a b} :: (outer a b).bindings ∧
    LocalNameTable.Lookup (inner a b).names "f" ⟨owner,3⟩ ∧
    LocalNameTable.Lookup (tailScope a b).names "f" ⟨owner,8⟩ := by
  exact ⟨rfl,rfl,.tail (by change "x" ≠ "f"; decide) .head,.head⟩

private def oldClosure (a b : Core.Ty) (body : Core.Expr) (captured : Core.Environment) : Core.Value := .closure a b body captured
private def newClosure (a b : Core.Ty) (environment : Core.Environment) : Core.Value := .closure a b lambdaBody environment
private theorem bodyPath (a b : Core.Ty) (body : Core.Expr) (argument value : Core.Value)
    (captured suffix : Core.Environment) (initial final : Core.Store) (cost : Nat)
    (actual : Core.Steps cost (.initial body (argument::captured) initial) (.final value final)) (k : List Core.Frame) :
    Core.Steps (cost+5) ⟨.eval lambdaBody (argument::oldClosure a b body captured::argument::suffix),k,initial⟩
      ⟨.ret value,k,final⟩ := by
  have count : cost+5=1+1+cost+3 := by omega
  rw [count]
  exact CostStepComposition.apply (parameterType:=a) (resultType:=b)
    (.cons (.var rfl) .refl) (.cons (.var rfl) .refl) actual
private theorem tailPath (a b : Core.Ty) (body : Core.Expr) (argument value : Core.Value)
    (captured suffix : Core.Environment) (initial final : Core.Store) (cost : Nat)
    (actual : Core.Steps cost (.initial body (argument::captured) initial) (.final value final)) (k : List Core.Frame) :
    Core.Steps (cost+10)
      ⟨.eval (.apply (.var 0) (.var 2))
        (newClosure a b (oldClosure a b body captured::argument::suffix)::oldClosure a b body captured::argument::suffix),k,initial⟩
      ⟨.ret value,k,final⟩ := by
  have count : cost+10=1+1+(cost+5)+3 := by omega
  rw [count]
  exact CostStepComposition.apply (.cons (.var rfl) .refl) (.cons (.var rfl) .refl)
    (bodyPath a b body argument value captured suffix initial final cost actual [])

theorem core_original_let_invokes_the_old_actual_callee_without_self_binding
    (a b : Core.Ty) (body : Core.Expr) (argument value : Core.Value)
    (captured suffix : Core.Environment) (initial final : Core.Store) (cost : Nat)
    (actual : Core.Steps cost (.initial body (argument::captured) initial) (.final value final)) :
    ∀ k,Core.Steps (cost+13)
      ⟨.eval (core a b (.apply (.var 0) (.var 2))) (oldClosure a b body captured::argument::suffix),k,initial⟩
      ⟨.ret value,k,final⟩ := by
  intro k
  have count : cost+13=1+(cost+10)+2 := by omega
  rw [count]
  exact CostStepComposition.letE (.cons .lambda .refl)
    (tailPath a b body argument value captured suffix initial final cost actual k)

theorem core_returning_the_closure_keeps_every_actual_capture_and_leaves_the_store
    (a b : Core.Ty) (environment : Core.Environment) (store : Core.Store) (k : List Core.Frame) :
    Core.Steps 4 ⟨.eval (core a b (.var 0)) environment,k,store⟩
      ⟨.ret (newClosure a b environment),k,store⟩ :=
  CostStepComposition.letE (.cons .lambda .refl) (.cons (.var rfl) .refl)

theorem core_fuel_and_genuine_resumption_keep_actual_capture_and_store_effects
    (a b : Core.Ty) (body : Core.Expr) (argument value : Core.Value)
    (captured suffix : Core.Environment) (initial final : Core.Store) (cost spent : Nat)
    (actual : Core.Steps cost (.initial body (argument::captured) initial) (.final value final))
    (cp : Core.State) (exhausted : Core.runStateful spent
      (.initial (core a b (.apply (.var 0) (.var 2))) (oldClosure a b body captured::argument::suffix) initial)=.outOfFuel cp) :
    spent<cost+13 ∧ Core.Steps (cost+13-spent) cp (.final value final) ∧
    ∀ extra,Core.runStateful extra cp=Core.runStateful (spent+extra)
      (.initial (core a b (.apply (.var 0) (.var 2))) (oldClosure a b body captured::argument::suffix) initial) := by
  have path := core_original_let_invokes_the_old_actual_callee_without_self_binding a b body argument value
    captured suffix initial final cost actual []
  exact ⟨(path.residual_of_outOfFuel exhausted).1,(path.residual_of_outOfFuel exhausted).2,Core.runStateful_resume exhausted⟩

/-- Captured references use the invocation store, not a snapshot stored at closure creation. -/
theorem core_captured_reference_writes_the_current_store
    (argument : Core.Word) (oldValue : Core.Value) (location : Nat)
    (captured suffix : Core.Environment) (initial final : Core.Store)
    (found : initial.read? location=some oldValue)
    (written : initial.write? location (.word argument)=some final) (k : List Core.Frame) :
    Core.Steps 18
      ⟨.eval (core .word .unit (.apply (.var 0) (.var 2)))
        (oldClosure .word .unit (.storeCell (.var 1) (.var 0)) (.cellRef .word location::captured)::
          .word argument::suffix),k,initial⟩ ⟨.ret .unit,k,final⟩ := by
  have actual : Core.Steps 5
      (.initial (.storeCell (.var 1) (.var 0)) (.word argument::.cellRef .word location::captured) initial)
      (.final .unit final) :=
    .cons .enterStoreCell (.cons (.var rfl) (.cons (.beginStoreCellValue found)
      (.cons (.var rfl) (.cons (.applyStoreCell written) .refl))))
  exact core_original_let_invokes_the_old_actual_callee_without_self_binding .word .unit _ _ _
    _ suffix initial final 5 actual k

theorem core_callee_allocation_retains_the_actual_old_store_and_appends_the_argument
    (argument : Core.Word) (captured suffix : Core.Environment) (initial : Core.Store) (k : List Core.Frame) :
    Core.Steps 16
      ⟨.eval (core .word (.cell .word) (.apply (.var 0) (.var 2)))
        (oldClosure .word (.cell .word) (.newCell .word (.var 0)) captured::.word argument::suffix),k,initial⟩
      ⟨.ret (.cellRef .word initial.length),k,initial++[.word argument]⟩ := by
  have actual : Core.Steps 3 (.initial (.newCell .word (.var 0)) (.word argument::captured) initial)
      (.final (.cellRef .word initial.length) (initial++[.word argument])) :=
    .cons .enterNewCell (.cons (.var rfl) (.cons .applyNewCell .refl))
  exact core_original_let_invokes_the_old_actual_callee_without_self_binding .word (.cell .word) _ _ _
    captured suffix initial _ 3 actual k

end Tests.ExpectedLambdaLetCore
