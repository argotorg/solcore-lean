import Solcore.Frontend.ExpectedComputationLambda
import Solcore.Frontend.RecursiveComputationReturnTree
import Solcore.Frontend.RecursiveLocalComputationProperties
import Solcore.Frontend.LocalFunctionApplicationStepComposition
import Solcore.Frontend.WordLessCostStepComposition
import Solcore.Core.FuelResumptionProperties

/-! Independent original lambdas retain arbitrary outer rows and repeated
typed/inferred shadowing. The final paths are consumers of Core only: creating
a closure captures the complete actual environment, but does not run its body.
No source-lambda evaluation, runtime typing or general store invariance is claimed. -/
set_option autoImplicit false
namespace Tests.FrontendExpectedComputationLambda
open Solcore Solcore.Frontend
private def named (s : Syntax.SourceSpan) (name : String) : Syntax.TypeExpr :=
  ⟨s,.named ⟨s,⟨⟨⟨s,name⟩,[]⟩⟩⟩ none⟩
private def types (a b : Core.Ty) : TypeNameTable := [(["A"],a),(["B"],b)]
private def ref (s : Syntax.SourceSpan) (name : String) : Syntax.Expr := ⟨s,.identifier ⟨s,name⟩⟩
private def statements (s : Syntax.SourceSpan) : Nat → List Syntax.Statement
  | 0 => [⟨s,.returnStmt (some ⟨s,.call (ref s "f") ⟨s,[ref s "x"]⟩⟩)⟩]
  | n+1 => ⟨s,.letDecl ⟨s,"x"⟩ (some (named s "A")) (some (ref s "x"))⟩::
      ⟨s,.letDecl ⟨s,"x"⟩ none (some (ref s "x"))⟩::statements s n
private def source (s : Syntax.SourceSpan) (n : Nat) (annotated : Bool := false) : Syntax.Expr :=
  ⟨s,.lambda s ⟨s,[⟨s,if annotated then .typed none ⟨s,"x"⟩ (named s "A") else .inferred ⟨s,"x"⟩⟩]⟩
    (if annotated then some (named s "B") else none) ⟨s,statements s n⟩⟩
private def outer (o : Resolved.DeclarationId) (i : LocalTypeInputs) (a b : Core.Ty) :=
  i.bindFresh o "f" (.function a b)
private def scope (o : Resolved.DeclarationId) (i : LocalTypeInputs) (a b : Core.Ty) : Nat → LocalTypeInputs
  | 0 => (outer o i a b).bindFresh o "x" a
  | m+1 => (scope o i a b m).bindFresh o "x" a
private def code : Nat → Nat → Core.Expr
  | 0,m => .apply (.var (m+1)) (.var 0)
  | n+1,m => .letE (.var 0) (.letE (.var 0) (code n (m+2)))
private def header (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (i : LocalTypeInputs)
    (a b : Core.Ty) (n : Nat) : DeclaredUnaryLambdaHeader := ⟨scope o i a b 0,⟨s,statements s n⟩,a,b⟩
private theorem declared (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (i : LocalTypeInputs)
    (a b : Core.Ty) (n : Nat) (annotated : Bool) :
    ExpectedUnaryLambdaHeaderDeclares (types a b) o (outer o i a b) (source s n annotated)
      (.function a b) (header s o i a b n) := by
  cases annotated
  · exact .lambda .inferred .omitted
  · exact .lambda (.typed (.named .head))
      (.annotated (.named (.tail (by change (["A"] : List String) ≠ ["B"]; decide) .head)))
private theorem functionFacts (o : Resolved.DeclarationId) (i : LocalTypeInputs) (a b : Core.Ty) (m : Nat) :
    LocalNameTable.Lookup (scope o i a b m).names "f" (Resolved.freshLocalId o i.ids) ∧
    Resolved.LocalScope.IndexOf (scope o i a b m).context.ids (Resolved.freshLocalId o i.ids) (m+1) ∧
    Resolved.LocalScope.Lookup (scope o i a b m).context (Resolved.freshLocalId o i.ids) (.function a b) := by
  induction m with
  | zero =>
      have different := Resolved.freshLocalId_cons_fresh_ne o i.ids
      exact ⟨.tail (by change "x" ≠ "f"; decide) .head,.tail different .head,.tail different .head⟩
  | succ m ih =>
      have different : Resolved.freshLocalId o (scope o i a b m).ids ≠ Resolved.freshLocalId o i.ids := by
        intro same
        have member : Resolved.freshLocalId o i.ids ∈ (scope o i a b m).names.map Prod.snd :=
          List.mem_map.mpr ⟨("f",Resolved.freshLocalId o i.ids),ih.1.mem,rfl⟩
        rw [LocalTypeInputs.names_ids] at member
        exact Resolved.freshLocalId_not_mem o _ (same ▸ member)
      exact ⟨.tail (by change "x" ≠ "f"; decide) ih.1,.tail different ih.2.1,.tail different ih.2.2⟩
private theorem argument (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (i : LocalTypeInputs) (a b : Core.Ty) (m : Nat) :
    RecursiveLocalComputationElaborates (scope o i a b m).names (scope o i a b m).context (ref s "x") (.var 0) a := by
  cases m <;> exact .pure (.identifier .head) (.var .head) (.var .head)
private theorem bodyElab (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (i : LocalTypeInputs)
    (a b : Core.Ty) (n m : Nat) :
    RecursiveComputationReturnTreeElaborates (types a b) o (scope o i a b m) ⟨s,statements s n⟩ (code n m) b := by
  induction n generalizing m with
  | zero => exact .expression (.application
      (.pure (.identifier (functionFacts o i a b m).1) (.var (functionFacts o i a b m).2.1) (.var (functionFacts o i a b m).2.2))
      (argument s o i a b m))
  | succ n ih =>
      exact .binding (.named .head) (argument s o i a b m)
        (.inferred (argument s o i a b (m+1)) (ih (m+2)))
private theorem elaborated (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (i : LocalTypeInputs)
    (a b : Core.Ty) (n : Nat) (annotated : Bool)
    (wa : Core.Ty.WellFormed [] a) (wb : Core.Ty.WellFormed [] b) :
    ExpectedComputationLambdaElaborates RecursiveLocalComputationElaborates (types a b) o
      (outer o i a b) (source s n annotated) (.lambda a b (code n 0)) (.function a b) :=
  .lambda (declared s o i a b n annotated) wa wb (bodyElab s o i a b n 0)

theorem arbitrary_well_formed_components_and_outer_rows_need_no_actual_inhabitants
    (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (i : LocalTypeInputs) (a b : Core.Ty) (n : Nat)
    (wa : Core.Ty.WellFormed [] a) (wb : Core.Ty.WellFormed [] b) :
    RecursiveComputationReturnTreeElaborates (types a b) o (scope o i a b 0) ⟨s,statements s n⟩ (code n 0) b ∧
      ExpectedComputationLambdaElaborates RecursiveLocalComputationElaborates (types a b) o
        (outer o i a b) (source s n) (.lambda a b (code n 0)) (.function a b) ∧
      elaborateExpectedComputationLambda? elaborateRecursiveLocalComputation? (types a b) o
        (outer o i a b) (source s n) (.function a b)=some (.lambda a b (code n 0)) ∧
      Core.HasType (outer o i a b).context.values (.lambda a b (code n 0)) (.function a b) := by
  have original := elaborated s o i a b n false wa wb
  exact ⟨bodyElab s o i a b n 0,original,
    (elaborateExpectedComputationLambda?_iff elaborateRecursiveLocalComputation?_iff).mpr original,
    original.core_hasType RecursiveLocalComputationElaborates.core_hasType⟩
theorem annotated_and_inferred_originals_have_the_same_literal_lambda
    (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (i : LocalTypeInputs) (a b : Core.Ty) (n : Nat)
    (wa : Core.Ty.WellFormed [] a) (wb : Core.Ty.WellFormed [] b) :
    ExpectedComputationLambdaElaborates RecursiveLocalComputationElaborates (types a b) o
      (outer o i a b) (source s n true) (.lambda a b (code n 0)) (.function a b) ∧
      elaborateExpectedComputationLambda? elaborateRecursiveLocalComputation? (types a b) o
        (outer o i a b) (source s n true) (.function a b)=
      elaborateExpectedComputationLambda? elaborateRecursiveLocalComputation? (types a b) o
        (outer o i a b) (source s n false) (.function a b) := by
  have typed := elaborated s o i a b n true wa wb
  exact ⟨typed,((elaborateExpectedComputationLambda?_iff elaborateRecursiveLocalComputation?_iff).mpr typed).trans
    ((elaborateExpectedComputationLambda?_iff elaborateRecursiveLocalComputation?_iff).mpr
      (elaborated s o i a b n false wa wb)).symm⟩
theorem provenance_keeps_the_original_body_and_exact_inner_scope
    (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (i : LocalTypeInputs) (a b : Core.Ty) (n : Nat)
    (core : Core.Expr) (e : ExpectedComputationLambdaElaborates RecursiveLocalComputationElaborates
      (types a b) o (outer o i a b) (source s n) core (.function a b)) :
    ∃ bodyCore, RecursiveComputationReturnTreeElaborates (types a b) o (scope o i a b 0)
      ⟨s,statements s n⟩ bodyCore b ∧ core=.lambda a b bodyCore := by
  obtain ⟨h,c,hd,_,_,body,shape⟩ := e.provenance
  have same := hd.result_unique (declared s o i a b n false)
  subst h
  exact ⟨c,body,shape⟩
theorem fresh_shadowing_retains_every_outer_row_and_the_captured_function_position
    (o : Resolved.DeclarationId) (i : LocalTypeInputs) (a b : Core.Ty) (m : Nat) :
    (scope o i a b 0).bindings.tail=(outer o i a b).bindings ∧
      (outer o i a b).bindings.tail=i.bindings ∧
      Resolved.LocalScope.IndexOf (scope o i a b m).context.ids (Resolved.freshLocalId o i.ids) (m+1) ∧
      LocalNameTable.Lookup (scope o i a b m).names "x" (Resolved.freshLocalId o
        (if m=0 then (outer o i a b).ids else (scope o i a b (m-1)).ids)) := by
  refine ⟨rfl,rfl,(functionFacts o i a b m).2.1,?_⟩
  cases m <;> simp only [scope,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,ite_false,Nat.add_sub_cancel,ite_true] <;> exact .head
theorem a_body_return_disagreement_is_not_repaired_by_an_omitted_annotation
    (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (i : LocalTypeInputs) (a b c : Core.Ty) (n : Nat) (different : b≠c) :
    declareExpectedUnaryLambdaHeader? (types a b) o (outer o i a b) (source s n) (.function a c)=
      some ⟨scope o i a b 0,⟨s,statements s n⟩,a,c⟩ ∧
      elaborateExpectedComputationLambda? elaborateRecursiveLocalComputation? (types a b) o
        (outer o i a b) (source s n) (.function a c)=none ∧
      ¬∃ core,ExpectedComputationLambdaElaborates RecursiveLocalComputationElaborates (types a b) o
        (outer o i a b) (source s n) core (.function a c) := by
  have hd : ExpectedUnaryLambdaHeaderDeclares (types a b) o (outer o i a b) (source s n) (.function a c)
      ⟨scope o i a b 0,⟨s,statements s n⟩,a,c⟩ := .lambda .inferred .omitted
  have absent : ¬∃ core,ExpectedComputationLambdaElaborates RecursiveLocalComputationElaborates (types a b) o
      (outer o i a b) (source s n) core (.function a c) := by
    rintro ⟨core,e⟩
    obtain ⟨h,bc,decl,_,_,body,_⟩ := e.provenance
    have same := decl.result_unique hd
    subst h
    have first := (elaborateComputationReturnTree?_iff elaborateRecursiveLocalComputation?_iff).mpr (bodyElab s o i a b n 0)
    have second := (elaborateComputationReturnTree?_iff elaborateRecursiveLocalComputation?_iff).mpr body
    exact different (congrArg Prod.snd (Option.some.inj (first.symm.trans second)))
  exact ⟨declareExpectedUnaryLambdaHeader?_iff.mpr hd,
    (elaborateExpectedComputationLambda?_eq_none_iff elaborateRecursiveLocalComputation?_iff).mpr absent,absent⟩

private def callee (a b : Core.Ty) (body : Core.Expr) (captured : Core.Environment) : Core.Value := .closure a b body captured
private theorem manual (a b : Core.Ty) (body : Core.Expr) (argument value : Core.Value)
    (captured suffix : Core.Environment) (initial final : Core.Store) (n m cost : Nat)
    (actual : Core.Steps cost (.initial body (argument::captured) initial) (.final value final)) (k : List Core.Frame) :
    Core.Steps (6*n+cost+5)
      ⟨.eval (code n m) (List.replicate (m+1) argument++callee a b body captured::suffix),k,initial⟩ ⟨.ret value,k,final⟩ := by
  induction n generalizing m k with
  | zero =>
      have count : 6*0+cost+5=1+1+cost+3 := by omega
      rw [count]
      exact CostStepComposition.apply (parameterType:=a) (resultType:=b)
        (.cons (.var (by simp [callee])) .refl) (.cons (.var (by simp [List.replicate_succ])) .refl) actual
  | succ n ih =>
      have count : 6*(n+1)+cost+5=1+(1+(6*n+cost+5)+2)+2 := by omega
      rw [count]
      simpa [code,List.replicate_succ] using CostStepComposition.letE (.cons (.var rfl) .refl)
        (CostStepComposition.letE (.cons (.var rfl) .refl) (ih (m+2) k))
theorem core_creation_captures_all_actual_values_and_does_not_run_the_body
    (a b : Core.Ty) (n : Nat) (environment : Core.Environment) (store : Core.Store) (k : List Core.Frame) :
    Core.Steps 1 ⟨.eval (.lambda a b (code n 0)) environment,k,store⟩
      ⟨.ret (.closure a b (code n 0) environment),k,store⟩ := .cons .lambda .refl
private def produced (a b : Core.Ty) (n : Nat) (body : Core.Expr) (captured suffix : Core.Environment) : Core.Value :=
  .closure a b (code n 0) (callee a b body captured::suffix)
private theorem applied (a b : Core.Ty) (n : Nat) (body : Core.Expr) (argument value : Core.Value)
    (captured suffix : Core.Environment) (initial final : Core.Store) (cost : Nat)
    (actual : Core.Steps cost (.initial body (argument::captured) initial) (.final value final)) (k : List Core.Frame) :
    Core.Steps (6*n+cost+10) ⟨.eval (.apply (.var 0) (.var 1)) [produced a b n body captured suffix,argument],k,initial⟩
      ⟨.ret value,k,final⟩ := by
  have count : 6*n+cost+10=1+1+(6*n+cost+5)+3 := by omega
  rw [count]
  exact CostStepComposition.apply (.cons (.var rfl) .refl) (.cons (.var rfl) .refl)
    (manual a b body argument value captured suffix initial final n 0 cost actual [])
theorem core_application_alone_runs_the_captured_callee_and_its_actual_effects
    (a b : Core.Ty) (n : Nat) (body : Core.Expr) (argument value : Core.Value)
    (captured suffix : Core.Environment) (initial final : Core.Store) (cost : Nat)
    (actual : Core.Steps cost (.initial body (argument::captured) initial) (.final value final)) :
    ∀ k,Core.Steps (6*n+cost+10)
      ⟨.eval (.apply (.var 0) (.var 1)) [produced a b n body captured suffix,argument],k,initial⟩ ⟨.ret value,k,final⟩ :=
  applied a b n body argument value captured suffix initial final cost actual
theorem core_application_fuel_and_full_resumption_keep_actual_captures_and_stores
    (a b : Core.Ty) (n : Nat) (body : Core.Expr) (argument value : Core.Value)
    (captured suffix : Core.Environment) (initial final : Core.Store) (cost spent : Nat)
    (actual : Core.Steps cost (.initial body (argument::captured) initial) (.final value final))
    (cp : Core.State) (exhausted : Core.runStateful spent
      (.initial (.apply (.var 0) (.var 1)) [produced a b n body captured suffix,argument] initial)=.outOfFuel cp) :
    spent<6*n+cost+10 ∧ Core.Steps (6*n+cost+10-spent) cp (.final value final) ∧
      ∀ extra,Core.runStateful extra cp=Core.runStateful (spent+extra)
        (.initial (.apply (.var 0) (.var 1)) [produced a b n body captured suffix,argument] initial) := by
  have path := applied a b n body argument value captured suffix initial final cost actual []
  exact ⟨(path.residual_of_outOfFuel exhausted).1,(path.residual_of_outOfFuel exhausted).2,Core.runStateful_resume exhausted⟩

end Tests.FrontendExpectedComputationLambda
