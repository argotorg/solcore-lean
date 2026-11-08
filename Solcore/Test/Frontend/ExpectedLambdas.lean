import Solcore.Frontend.Fragments.Internal.Expected
import Solcore.Frontend.Fragments.Internal.RecursiveComputation
import Solcore.Frontend.Fragments.Internal.Computation
import Solcore.Frontend.Fragments.Internal.LocalFunctionApplication
import Solcore.Core.Fuel
import Solcore.Frontend.Fragments.Internal.LocalExpressions
import Solcore.Frontend.Fragments.Internal.ClosedSource
import Solcore.Frontend.Fragments.Internal.SourceValues
import Solcore.Core.Typing
import Solcore.Core.Eval
import Solcore.Resolved.Eval
import Solcore.Syntax.Parser.Internal.TermBasics
import Solcore.Core.Correspondence

/-!
# Expected lambda tests

Expected lambdas: headers, computation and data lambdas, typing, argument application and let spines.
-/

section
-- leanmerge: from Solcore.Test.FrontendExpectedComputationLambdaBoundaryProperties
/-! Well-formed lambda components, an exact child checker and child Core typing
are distinct premises. Original header/body evidence and arbitrary unused outer
types cannot silently replace them; no runtime or source evaluation is asserted. -/
set_option autoImplicit false
namespace Tests.ExpectedComputationLambdaBoundaries
open Solcore Solcore.Frontend
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"ExpectedLambdaBoundaries",by decide⟩],by decide⟩⟩,149⟩
private def span : Syntax.SourceSpan := ⟨⟨.main,"expected-lambda-boundaries.sol"⟩,0,47⟩
private def ref (name : String) : Syntax.Expr := ⟨span,.identifier ⟨span,name⟩⟩
private def returned (name : String) : Syntax.Block := ⟨span,[⟨span,.returnStmt (some (ref name))⟩]⟩
private def bare : Syntax.Block := ⟨span,[⟨span,.returnStmt none⟩]⟩
private def source (body : Syntax.Block) : Syntax.Expr :=
  ⟨span,.lambda span ⟨span,[⟨span,.inferred ⟨span,"x"⟩⟩]⟩ none body⟩
private def header (outer : LocalTypeInputs) (body : Syntax.Block) (a b : Core.Ty) : DeclaredUnaryLambdaHeader :=
  ⟨outer.bindFresh owner "x" a,body,a,b⟩
private theorem declares (outer : LocalTypeInputs) (body : Syntax.Block) (a b : Core.Ty) :
    ExpectedUnaryLambdaHeaderDeclares [] owner outer (source body) (.function a b) (header outer body a b) :=
  .lambda .inferred .omitted
private def saved (a : Core.Ty) : LocalTypeInputs := LocalTypeInputs.empty.bindFresh owner "saved" a
private theorem nominal_not_well_formed (nominal : Core.DataTypeId) :
    ¬ Core.Ty.WellFormed [] (.namedData nominal) := by
  intro formed; cases formed with | namedData found => cases found
private theorem own_body (outer : LocalTypeInputs) (a : Core.Ty) :
    RecursiveComputationReturnTreeElaborates [] owner (outer.bindFresh owner "x" a) (returned "x") (.var 0) a :=
  .expression (.pure (.identifier .head) (.var .head) (.var .head))
private theorem captured_body (a b : Core.Ty) :
    RecursiveComputationReturnTreeElaborates [] owner ((saved b).bindFresh owner "x" a) (returned "saved") (.var 1) b :=
  .expression (.pure (.identifier (.tail (by change "x" ≠ "saved"; decide) .head))
    (.var (.tail (by change (⟨owner,1⟩ : Resolved.LocalId) ≠ ⟨owner,0⟩; decide) .head))
    (.var (.tail (by change (⟨owner,1⟩ : Resolved.LocalId) ≠ ⟨owner,0⟩; decide) .head)))

private inductive Mislabels (_ : LocalNameTable) (_ : Resolved.Context) (_ : Syntax.Expr) : Core.Expr → Core.Ty → Prop where
  | wrong : Mislabels _ _ _ .unit .word
private def mischeck (_ : LocalNameTable) (_ : Resolved.Context) (_ : Syntax.Expr) : Option (Core.Expr × Core.Ty) := some (.unit,.word)
private theorem miscorrect {table : LocalNameTable} {context : Resolved.Context} {src : Syntax.Expr} {core : Core.Expr} {type : Core.Ty} :
    mischeck table context src=some (core,type) ↔ Mislabels table context src core type := by
  constructor
  · intro accepted
    cases Option.some.inj accepted
    exact .wrong
  · intro evidence; cases evidence; rfl
private theorem no_mislabel_typing :
    ¬ Core.HasType [] (.lambda .word .word .unit) (.function .word .word) := by
  intro typed
  cases typed with | lambda _ _ body => cases body
private theorem no_child_typing_law :
    ¬ (∀ {table context src core type}, Mislabels table context src core type → Core.HasType context.values core type) := by
  intro law
  have falseType := law (table:=[]) (context:=[]) (src:=ref "x") Mislabels.wrong
  cases falseType

/-- A valid original header and a Unit body do not establish the domain guard. -/
theorem a_header_and_typed_body_do_not_make_an_unregistered_domain_well_formed
    (nominal : Core.DataTypeId) :
    ExpectedUnaryLambdaHeaderDeclares [] owner .empty (source bare) (.function (.namedData nominal) .unit)
      (header .empty bare (.namedData nominal) .unit) ∧
    RecursiveComputationReturnTreeElaborates [] owner (LocalTypeInputs.empty.bindFresh owner "x" (.namedData nominal)) bare .unit .unit ∧
    elaborateExpectedComputationLambda? elaborateRecursiveLocalComputation? [] owner .empty
      (source bare) (.function (.namedData nominal) .unit)=none ∧
    (¬ ∃ core, ExpectedComputationLambdaElaborates RecursiveLocalComputationElaborates [] owner .empty
      (source bare) core (.function (.namedData nominal) .unit)) ∧
    ¬ Core.HasType [] (.lambda (.namedData nominal) .unit .unit) (.function (.namedData nominal) .unit) := by
  have rejected : elaborateExpectedComputationLambda? elaborateRecursiveLocalComputation? [] owner .empty
      (source bare) (.function (.namedData nominal) .unit)=none := by
    simp [elaborateExpectedComputationLambda?,declareExpectedUnaryLambdaHeader?_iff.mpr (declares .empty bare (.namedData nominal) .unit),
      header,Core.Ty.isWellFormed]
  refine ⟨declares .empty bare _ _,.bare,rejected,
    (elaborateExpectedComputationLambda?_eq_none_iff elaborateRecursiveLocalComputation?_iff).mp rejected,?_⟩
  intro typed
  cases typed with | lambda domain _ _ => exact nominal_not_well_formed nominal domain

/-- A typed captured variable cannot replace the separate codomain guard. -/
theorem a_typed_captured_return_does_not_make_an_unregistered_codomain_well_formed
    (nominal : Core.DataTypeId) :
    let outer := saved (.namedData nominal)
    ExpectedUnaryLambdaHeaderDeclares [] owner outer (source (returned "saved")) (.function .word (.namedData nominal))
      (header outer (returned "saved") .word (.namedData nominal)) ∧
    RecursiveComputationReturnTreeElaborates [] owner (outer.bindFresh owner "x" .word)
      (returned "saved") (.var 1) (.namedData nominal) ∧
    elaborateExpectedComputationLambda? elaborateRecursiveLocalComputation? [] owner outer
      (source (returned "saved")) (.function .word (.namedData nominal))=none ∧
    (¬ ∃ core, ExpectedComputationLambdaElaborates RecursiveLocalComputationElaborates [] owner outer
      (source (returned "saved")) core (.function .word (.namedData nominal))) ∧
    ¬ Core.HasType outer.context.values (.lambda .word (.namedData nominal) (.var 1)) (.function .word (.namedData nominal)) := by
  dsimp only
  have rejected : elaborateExpectedComputationLambda? elaborateRecursiveLocalComputation? [] owner (saved (.namedData nominal))
      (source (returned "saved")) (.function .word (.namedData nominal))=none := by
    simp [elaborateExpectedComputationLambda?,declareExpectedUnaryLambdaHeader?_iff.mpr (declares (saved (.namedData nominal))
      (returned "saved") .word (.namedData nominal)),header,Core.Ty.isWellFormed]
  refine ⟨declares _ _ _ _,captured_body _ _,rejected,
    (elaborateExpectedComputationLambda?_eq_none_iff elaborateRecursiveLocalComputation?_iff).mp rejected,?_⟩
  intro typed
  cases typed with | lambda _ codomain _ => exact nominal_not_well_formed nominal codomain

theorem an_unused_outer_nominal_type_is_not_a_new_blanket_well_formedness_guard
    (nominal : Core.DataTypeId) :
    let outer := saved (.namedData nominal)
    ExpectedComputationLambdaElaborates RecursiveLocalComputationElaborates [] owner outer
      (source (returned "x")) (.lambda .word .word (.var 0)) (.function .word .word) ∧
    elaborateExpectedComputationLambda? elaborateRecursiveLocalComputation? [] owner outer
      (source (returned "x")) (.function .word .word)=some (.lambda .word .word (.var 0)) ∧
    Core.HasType outer.context.values (.lambda .word .word (.var 0)) (.function .word .word) ∧
    ¬ Core.Ty.WellFormed [] (.namedData nominal) := by
  have evidence : ExpectedComputationLambdaElaborates RecursiveLocalComputationElaborates [] owner (saved (.namedData nominal))
      (source (returned "x")) (.lambda .word .word (.var 0)) (.function .word .word) :=
    .lambda (declares _ _ _ _) .word .word (own_body _ _)
  exact ⟨evidence,(elaborateExpectedComputationLambda?_iff elaborateRecursiveLocalComputation?_iff).mpr evidence,
    evidence.core_hasType RecursiveLocalComputationElaborates.core_hasType,nominal_not_well_formed nominal⟩

theorem an_exact_checker_for_a_dishonest_child_is_not_a_core_typing_law :
    (∀ {table context src core type}, mischeck table context src=some (core,type) ↔ Mislabels table context src core type) ∧
    ExpectedComputationLambdaElaborates Mislabels [] owner .empty
      (source (returned "x")) (.lambda .word .word .unit) (.function .word .word) ∧
    elaborateExpectedComputationLambda? mischeck [] owner .empty
      (source (returned "x")) (.function .word .word)=some (.lambda .word .word .unit) ∧
    (¬ Core.HasType [] (.lambda .word .word .unit) (.function .word .word)) ∧
    ¬ (∀ {table context src core type}, Mislabels table context src core type → Core.HasType context.values core type) := by
  have evidence : ExpectedComputationLambdaElaborates Mislabels [] owner .empty
      (source (returned "x")) (.lambda .word .word .unit) (.function .word .word) :=
    .lambda (declares _ _ _ _) .word .word (.expression .wrong)
  exact ⟨miscorrect,evidence,(elaborateExpectedComputationLambda?_iff miscorrect).mpr evidence,
    no_mislabel_typing,no_child_typing_law⟩

private def reject (_ : LocalNameTable) (_ : Resolved.Context) (_ : Syntax.Expr) : Option (Core.Expr × Core.Ty) := none
theorem independent_lambda_typing_does_not_prove_an_arbitrary_checker_accepts :
    ExpectedComputationLambdaElaborates RecursiveLocalComputationElaborates [] owner .empty
      (source (returned "x")) (.lambda .word .word (.var 0)) (.function .word .word) ∧
    Core.HasType [] (.lambda .word .word (.var 0)) (.function .word .word) ∧
    elaborateExpectedComputationLambda? reject [] owner .empty (source (returned "x")) (.function .word .word)=none := by
  have evidence : ExpectedComputationLambdaElaborates RecursiveLocalComputationElaborates [] owner .empty
      (source (returned "x")) (.lambda .word .word (.var 0)) (.function .word .word) :=
    .lambda (declares _ _ _ _) .word .word (own_body _ _)
  refine ⟨evidence,evidence.core_hasType RecursiveLocalComputationElaborates.core_hasType,?_⟩
  simp only [elaborateExpectedComputationLambda?,declareExpectedUnaryLambdaHeader?_iff.mpr (declares .empty (returned "x") .word .word),
    bind,Option.bind_some]
  simp [header,Core.Ty.isWellFormed,returned,elaborateComputationReturnTree?,reject]
end Tests.ExpectedComputationLambdaBoundaries
end

section
-- leanmerge: from Solcore.Test.FrontendExpectedComputationLambdaProperties
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
end

section
-- leanmerge: from Solcore.Test.FrontendExpectedComputationLambdaTypingProperties
/-! True recursive source typing constructs the original mixed lambda before
any Core witness or checker result is requested. Arbitrary outer rows, expected
components and shadow depth need no runtime inhabitants or execution premises. -/
set_option autoImplicit false
namespace Tests.FrontendExpectedComputationLambdaTyping
open Solcore Solcore.Frontend
private structure Scenario where
  span : Syntax.SourceSpan
  owner : Resolved.DeclarationId
  initial : LocalTypeInputs
  a : Core.Ty
  b : Core.Ty
  depth : Nat
  hasDefault : Bool
  annotated : Bool
  domain : Core.Ty.WellFormed [] a
  codomain : Core.Ty.WellFormed [] b
private def types (p : Scenario) : TypeNameTable := [(["A"],p.a),(["B"],p.b)]
private def named (p : Scenario) (name : String) : Syntax.TypeExpr :=
  ⟨p.span,.named ⟨p.span,⟨⟨⟨p.span,name⟩,[]⟩⟩⟩ none⟩
private def ref (p : Scenario) (name : String) : Syntax.Expr := ⟨p.span,.identifier ⟨p.span,name⟩⟩
private def call (p : Scenario) : Syntax.Expr := ⟨p.span,.call (ref p "f") ⟨p.span,[ref p "x"]⟩⟩
private def outer (p : Scenario) := p.initial.bindFresh p.owner "f" (.function p.a p.b)
private def scope (p : Scenario) : Nat → LocalTypeInputs
  | 0 => (outer p).bindFresh p.owner "x" p.a
  | m+1 => (scope p m).bindFresh p.owner "x" p.a
private def zero (p : Scenario) : Syntax.Expr := ⟨p.span,.literal ⟨p.span,.decimal "0"⟩⟩
private theorem zeroMeaning (p : Scenario) : WordLiteralDenotes ⟨p.span,.decimal "0"⟩ (Core.Word.ofNatModulo 0) :=
  .decimal (by decide) (.cons (.decimal (digit := 0) (by decide) rfl) .nil)
private theorem oneMeaning (p : Scenario) : WordLiteralDenotes ⟨p.span,.decimal "1"⟩ (Core.Word.ofNatModulo 1) :=
  .decimal (by decide) (.cons (.decimal (digit := 1) (by decide) rfl) .nil)
private def condition (p : Scenario) : Syntax.Expr := ⟨p.span,.binary (zero p) ⟨p.span,.equal⟩ (zero p)⟩
private def returned (p : Scenario) : Syntax.Block := ⟨p.span,[⟨p.span,.returnStmt (some (call p))⟩]⟩
private def literalArm (p : Scenario) : Syntax.MatchCase :=
  ⟨p.span,⟨⟨p.span,.literal ⟨p.span,.decimal "1"⟩⟩,returned p⟩⟩
private def wildcardArm (p : Scenario) : Syntax.MatchCase :=
  ⟨p.span,⟨⟨p.span,.group ⟨p.span,.wildcard p.span⟩⟩,returned p⟩⟩
private def fallback (p : Scenario) : Option Syntax.Block := if p.hasDefault then some (returned p) else none
private def matched (p : Scenario) : Syntax.Block :=
  ⟨p.span,[⟨p.span,.matchWith ⟨p.span,⟨zero p,[]⟩⟩
    ⟨p.span,⟨[literalArm p,wildcardArm p],fallback p⟩⟩⟩]⟩
private def barrier (p : Scenario) : Syntax.Block := ⟨p.span,[⟨p.span,.block (matched p).value⟩]⟩
private def statements (p : Scenario) : Nat → List Syntax.Statement
  | 0 => [⟨p.span,.expression (call p) true⟩,
      ⟨p.span,.ifThen (condition p) (barrier p) (some (returned p))⟩]
  | n+1 => ⟨p.span,.letDecl ⟨p.span,"x"⟩ (some (named p "A")) (some (ref p "x"))⟩::
      ⟨p.span,.letDecl ⟨p.span,"x"⟩ none (some (ref p "x"))⟩::statements p n
private def source (p : Scenario) : Syntax.Expr :=
  ⟨p.span,.lambda p.span ⟨p.span,[⟨p.span,if p.annotated then
    .typed none ⟨p.span,"x"⟩ (named p "A") else .inferred ⟨p.span,"x"⟩⟩]⟩
    (if p.annotated then some (named p "B") else none) ⟨p.span,statements p p.depth⟩⟩
private theorem header (p : Scenario) : ExpectedUnaryLambdaHeaderDeclares (types p) p.owner (outer p)
    (source p) (.function p.a p.b) ⟨scope p 0,⟨p.span,statements p p.depth⟩,p.a,p.b⟩ := by
  cases annotated : p.annotated
  · simp only [source,annotated,Bool.false_eq_true,ite_false]
    exact .lambda .inferred .omitted
  · simp only [source,annotated,ite_true]
    exact .lambda (.typed (.named .head))
      (.annotated (.named (.tail (by change (["A"] : List String) ≠ ["B"]; decide) .head)))
private theorem functionFacts (p : Scenario) (m : Nat) :
    LocalNameTable.Lookup (scope p m).names "f" (Resolved.freshLocalId p.owner p.initial.ids) ∧
    Resolved.LocalScope.Lookup (scope p m).context (Resolved.freshLocalId p.owner p.initial.ids) (.function p.a p.b) := by
  induction m with
  | zero =>
      exact ⟨.tail (by change "x" ≠ "f"; decide) .head,
        .tail (Resolved.freshLocalId_cons_fresh_ne p.owner p.initial.ids) .head⟩
  | succ m ih =>
      have different : Resolved.freshLocalId p.owner (scope p m).ids ≠ Resolved.freshLocalId p.owner p.initial.ids := by
        intro same
        have member : Resolved.freshLocalId p.owner p.initial.ids ∈ (scope p m).names.map Prod.snd :=
          List.mem_map.mpr ⟨("f",Resolved.freshLocalId p.owner p.initial.ids),ih.1.mem,rfl⟩
        rw [LocalTypeInputs.names_ids] at member
        exact Resolved.freshLocalId_not_mem p.owner _ (same ▸ member)
      exact ⟨.tail (by change "x" ≠ "f"; decide) ih.1,.tail different ih.2⟩
private theorem argumentTyped (p : Scenario) (m : Nat) :
    RecursiveLocalComputationHasType (scope p m).names (scope p m).context (ref p "x") p.a := by
  cases m <;> exact .pure (.identifier .head .head)
private theorem callTyped (p : Scenario) (m : Nat) :
    RecursiveLocalComputationHasType (scope p m).names (scope p m).context (call p) p.b :=
  .application (.pure (.identifier (functionFacts p m).1 (functionFacts p m).2)) (argumentTyped p m)
private theorem guardTyped (p : Scenario) (m : Nat) :
    RecursiveLocalComputationHasType (scope p m).names (scope p m).context (condition p) .bool :=
  .pure (.equal (.wordLiteral (zeroMeaning p)) (.wordLiteral (zeroMeaning p)))
private theorem literalPattern (p : Scenario) :
    WordMatchPatternClassifies (literalArm p).value.pattern (some (Core.Word.ofNatModulo 1)) :=
  .literal ⟨_,rfl,oneMeaning p⟩
private theorem wildcardPattern (p : Scenario) : WordMatchPatternClassifies (wildcardArm p).value.pattern none :=
  .group (.wildcard rfl)
private theorem matchTyped (p : Scenario) (m : Nat) :
    RecursiveComputationReturnTreeHasType (types p) p.owner (scope p m) (matched p) p.b := by
  refine .wordMatch (.pure (.wordLiteral (zeroMeaning p))) ?_ (.inl rfl) ?_ ?_ ?_
  · intro arm member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨_,literalPattern p⟩
    · have same := List.mem_singleton.mp member; subst arm; exact ⟨_,wildcardPattern p⟩
  · exact .inr ⟨wildcardArm p,by simp,wildcardPattern p⟩
  · intro arm member
    rcases List.mem_cons.mp member with rfl | member
    · exact .expression (callTyped p m)
    · have same := List.mem_singleton.mp member; subst arm; exact .expression (callTyped p m)
  · intro body member
    cases present : p.hasDefault <;> simp only [fallback,present,Bool.false_eq_true,ite_false,ite_true,
      Option.toList_none,List.not_mem_nil,Option.toList_some,List.mem_singleton] at member
    subst body
    exact .expression (callTyped p m)
private theorem protection (p : Scenario) (m : Nat) :
    ComputationNamesProtected ((scope p m).names.map Prod.fst) (barrier p) :=
  computationBlockPreservesNames_iff.mp (by simp only [barrier,computationBlockPreservesNames])
private theorem bodyTyped (p : Scenario) (n m : Nat) :
    RecursiveComputationReturnTreeHasType (types p) p.owner (scope p m) ⟨p.span,statements p n⟩ p.b := by
  induction n generalizing m with
  | zero =>
      exact .discard (callTyped p m) (.conditional (guardTyped p m) (protection p m)
        (.block (matchTyped p m)) (.expression (callTyped p m)))
  | succ n ih =>
      exact .binding (.named .head) (argumentTyped p m) (.inferred (argumentTyped p (m+1)) (ih (m+2)))
private theorem original (p : Scenario) : ExpectedComputationLambdaHasType RecursiveLocalComputationHasType
    (types p) p.owner (outer p) (source p) (.function p.a p.b) :=
  .lambda (header p) p.domain p.codomain (bodyTyped p p.depth 0)

theorem original_mixed_body_is_typed_without_a_core_expression_or_checker_result (p : Scenario) :
    RecursiveComputationReturnTreeHasType (types p) p.owner (scope p 0) ⟨p.span,statements p p.depth⟩ p.b :=
  bodyTyped p p.depth 0
theorem source_only_typing_precedes_both_correspondence_laws (p : Scenario) :
    ExpectedComputationLambdaHasType RecursiveLocalComputationHasType (types p) p.owner (outer p)
      (source p) (.function p.a p.b) := original p
theorem independent_elaboration_exists_after_source_typing (p : Scenario) :
    ∃ core,ExpectedComputationLambdaElaborates RecursiveLocalComputationElaborates
      (types p) p.owner (outer p) (source p) core (.function p.a p.b) :=
  (expectedComputationLambdaHasType_iff_elaborates recursiveLocalComputationHasType_iff_elaborates).mp (original p)
theorem successful_check_exists_after_source_typing (p : Scenario) :
    ∃ core,elaborateExpectedComputationLambda? elaborateRecursiveLocalComputation?
      (types p) p.owner (outer p) (source p) (.function p.a p.b)=some core :=
  (expectedComputationLambdaHasType_iff_checked recursiveLocalComputationHasType_iff_elaborates
    elaborateRecursiveLocalComputation?_iff).mp (original p)
theorem both_witness_kinds_recover_the_same_source_only_judgment
    (table : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs) (source : Syntax.Expr) (expected : Core.Ty) :
    ((∃ core,ExpectedComputationLambdaElaborates RecursiveLocalComputationElaborates table owner inputs source core expected) →
      ExpectedComputationLambdaHasType RecursiveLocalComputationHasType table owner inputs source expected) ∧
    ((∃ core,elaborateExpectedComputationLambda? elaborateRecursiveLocalComputation? table owner inputs source expected=some core) →
      ExpectedComputationLambdaHasType RecursiveLocalComputationHasType table owner inputs source expected) :=
  ⟨(expectedComputationLambdaHasType_iff_elaborates recursiveLocalComputationHasType_iff_elaborates).mpr,
    (expectedComputationLambdaHasType_iff_checked recursiveLocalComputationHasType_iff_elaborates
      elaborateRecursiveLocalComputation?_iff).mpr⟩
theorem annotations_and_original_optional_defaults_preserve_source_typing (p : Scenario) (annotation fallback : Bool) :
    let changed := {p with annotated:=annotation,hasDefault:=fallback}
    ExpectedComputationLambdaHasType RecursiveLocalComputationHasType (types changed) changed.owner
      (outer changed) (source changed) (.function changed.a changed.b) := original _
theorem every_original_match_arm_and_optional_default_is_independently_typed (p : Scenario) (m : Nat) :
    (∀ arm ∈ [literalArm p,wildcardArm p],RecursiveComputationReturnTreeHasType (types p) p.owner
      (scope p m) arm.value.body p.b) ∧
    (∀ body ∈ (fallback p).toList,RecursiveComputationReturnTreeHasType (types p) p.owner (scope p m) body p.b) := by
  constructor
  · intro arm member
    rcases List.mem_cons.mp member with rfl | member
    · exact .expression (callTyped p m)
    · have same := List.mem_singleton.mp member; subst arm; exact .expression (callTyped p m)
  · intro body member
    cases present : p.hasDefault <;> simp only [fallback,present,Bool.false_eq_true,ite_false,ite_true,
      Option.toList_none,List.not_mem_nil,Option.toList_some,List.mem_singleton] at member
    subst body
    exact .expression (callTyped p m)
theorem fresh_shadowing_keeps_arbitrary_outer_rows_and_the_original_captured_name (p : Scenario) (m : Nat) :
    (scope p 0).bindings.tail=(outer p).bindings ∧ (outer p).bindings.tail=p.initial.bindings ∧
      LocalNameTable.Lookup (scope p m).names "f" (Resolved.freshLocalId p.owner p.initial.ids) ∧
      Resolved.LocalScope.Lookup (scope p m).context (Resolved.freshLocalId p.owner p.initial.ids) (.function p.a p.b) :=
  ⟨rfl,rfl,(functionFacts p m).1,(functionFacts p m).2⟩
theorem checker_absence_is_exactly_absence_of_recursive_source_typing
    (table : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs) (source : Syntax.Expr) (expected : Core.Ty) :
    elaborateExpectedComputationLambda? elaborateRecursiveLocalComputation? table owner inputs source expected=none ↔
      ¬ExpectedComputationLambdaHasType RecursiveLocalComputationHasType table owner inputs source expected := by
  have bridge : ExpectedComputationLambdaHasType RecursiveLocalComputationHasType table owner inputs source expected ↔
      ∃ core,elaborateExpectedComputationLambda? elaborateRecursiveLocalComputation? table owner inputs source expected=some core :=
    expectedComputationLambdaHasType_iff_checked recursiveLocalComputationHasType_iff_elaborates elaborateRecursiveLocalComputation?_iff
  constructor
  · intro rejected typed
    obtain ⟨core,accepted⟩ := bridge.mp typed
    rw [rejected] at accepted
    cases accepted
  · intro absent
    cases accepted : elaborateExpectedComputationLambda? elaborateRecursiveLocalComputation? table owner inputs source expected with
    | none => rfl
    | some core => exact False.elim (absent (bridge.mpr ⟨core,accepted⟩))

theorem an_accepted_header_does_not_hide_the_original_body_return_disagreement
    (p : Scenario) (otherReturn : Core.Ty) (different : p.b≠otherReturn) :
    let q := {p with annotated:=false}
    declareExpectedUnaryLambdaHeader? (types q) q.owner (outer q) (source q) (.function q.a otherReturn)=
      some ⟨scope q 0,⟨q.span,statements q q.depth⟩,q.a,otherReturn⟩ ∧
      ¬ExpectedComputationLambdaHasType RecursiveLocalComputationHasType (types q) q.owner (outer q)
        (source q) (.function q.a otherReturn) ∧
      elaborateExpectedComputationLambda? elaborateRecursiveLocalComputation? (types q) q.owner (outer q)
        (source q) (.function q.a otherReturn)=none := by
  dsimp only
  let q := {p with annotated:=false}
  have hd : ExpectedUnaryLambdaHeaderDeclares (types q) q.owner (outer q) (source q) (.function q.a otherReturn)
      ⟨scope q 0,⟨q.span,statements q q.depth⟩,q.a,otherReturn⟩ := .lambda .inferred .omitted
  have absent : ¬ExpectedComputationLambdaHasType RecursiveLocalComputationHasType (types q) q.owner (outer q)
      (source q) (.function q.a otherReturn) := by
    intro typing
    cases typing with
    | lambda actualHeader _ _ wrongBody =>
        have same := actualHeader.result_unique hd
        cases same
        obtain ⟨firstCore,first⟩ := (computationReturnTreeHasType_iff_elaborates
          recursiveLocalComputationHasType_iff_elaborates).mp (bodyTyped q q.depth 0)
        obtain ⟨secondCore,second⟩ := (computationReturnTreeHasType_iff_elaborates
          recursiveLocalComputationHasType_iff_elaborates).mp wrongBody
        have firstChecked := (elaborateComputationReturnTree?_iff elaborateRecursiveLocalComputation?_iff).mpr first
        have secondChecked := (elaborateComputationReturnTree?_iff elaborateRecursiveLocalComputation?_iff).mpr second
        exact different (congrArg Prod.snd (Option.some.inj (firstChecked.symm.trans secondChecked)))
  exact ⟨declareExpectedUnaryLambdaHeader?_iff.mpr hd,absent,
    (checker_absence_is_exactly_absence_of_recursive_source_typing _ _ _ _ _).mpr absent⟩

end Tests.FrontendExpectedComputationLambdaTyping
end

section
-- leanmerge: from Solcore.Test.FrontendExpectedDataLambdaAdmissionBoundaryProperties
/- Raw source calls can bypass unvisited syntax and produce non-Core intermediates. -/
set_option autoImplicit false
namespace Tests.ExpectedDataLambdaAdmissionBoundaries
open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"LambdaAdmission", by decide⟩], by decide⟩⟩, 295⟩
private def name (s : Syntax.SourceSpan) : Syntax.Identifier := ⟨s, "p"⟩
private def ref (s : Syntax.SourceSpan) (text : String) : Syntax.Expr :=
  ⟨s, .identifier ⟨s, text⟩⟩
private def unit (s : Syntax.SourceSpan) : Syntax.Expr := ⟨s, .tuple ⟨s, []⟩⟩
private def output (s : Syntax.SourceSpan) (e : Syntax.Expr) : Syntax.Block :=
  ⟨s, [⟨s, .returnStmt (some e)⟩]⟩
private def bare (s : Syntax.SourceSpan) : Syntax.Block := ⟨s, [⟨s, .returnStmt none⟩]⟩
private def lambda (s : Syntax.SourceSpan) (b : Syntax.Block) : Syntax.Expr :=
  ⟨s, .lambda s ⟨s, [⟨s, .inferred (name s)⟩]⟩ none b⟩
private def call (s : Syntax.SourceSpan) (f a : Syntax.Expr) : Syntax.Expr :=
  ⟨s, .call f ⟨s, [a]⟩⟩
private def branching (s : Syntax.SourceSpan) : Syntax.Block :=
  ⟨s, [⟨s, .ifThen (ref s "p") (bare s) (some (output s (ref s "missing")))⟩]⟩
private def matching (s : Syntax.SourceSpan) : Syntax.Block :=
  ⟨s, [⟨s, .matchWith ⟨s, ⟨ref s "p", []⟩⟩
    ⟨s, ⟨[⟨s, ⟨⟨s, .wildcard s⟩, bare s⟩⟩,
      ⟨s, ⟨⟨s, .literal ⟨s, .string "bad"⟩⟩, bare s⟩⟩], none⟩⟩⟩]⟩
private def hiddenArgument (s : Syntax.SourceSpan) : Syntax.Expr :=
  ⟨s, .conditional (ref s "flag") s (unit s) s (ref s "missing")⟩
private def inputs : LocalTypeInputs := LocalTypeInputs.empty.bindFresh owner "flag" .bool
private def environment : List (Resolved.LocalId × RuntimeValue) :=
  [(Resolved.freshLocalId owner [], .bool true)]
private def argumentName (s : Syntax.SourceSpan) : Syntax.Expr := ref s "flag"

variable (s : Syntax.SourceSpan) (store : List RuntimeValue)

/-- The selected original branch succeeds while the checker rejects an unselected missing name. -/
theorem unselected_body_is_still_checked :
    ClosedSourceDataBody (branching s) ∧
    ClosedSourceExpressionEvaluates owner inputs.names environment store
      (call s (lambda s (branching s)) (argumentName s)) .unit store ∧
    elaborateExpectedComputationLambda? elaborateLocalExpression? [] owner inputs
      (lambda s (branching s)) (.function .bool .unit) = none := by
  have raw : ClosedSourceExpressionEvaluates owner inputs.names environment store
      (call s (lambda s (branching s)) (argumentName s)) .unit store :=
    .call .inferred (.creation .inferred) (.reference .head .head)
      (.ifTrue (.reference .head .head) .bare)
  exact ⟨.conditional .reference .bare (.expression .reference), raw, by cbv⟩

/-- A first wildcard bypasses a malformed written pattern at runtime, not in the checker. -/
theorem unselected_pattern_is_still_checked :
    ClosedSourceDataBody (matching s) ∧
    ClosedSourceExpressionEvaluates owner [] [] store
      (call s (lambda s (matching s)) (unit s)) .unit store ∧
    elaborateExpectedComputationLambda? elaborateLocalExpression? [] owner .empty
      (lambda s (matching s)) (.function .unit .unit) = none := by
  have raw : ClosedSourceExpressionEvaluates owner [] [] store
      (call s (lambda s (matching s)) (unit s)) .unit store :=
    .call .inferred (.creation .inferred) .unit
      (.wordMatch (.reference .head .head) (.wildcard (.wildcard rfl)) .bare)
  refine ⟨?_, raw, by cbv⟩
  refine .wordMatch .reference ?_ ?_
  · intro arm member
    rcases List.mem_cons.mp member with rfl | member
    · exact .bare
    · rcases List.mem_cons.mp member with rfl | member
      · exact .bare
      · cases member
  · intro body member; cases member

/-- An admitted argument can run its selected branch despite lacking whole original resolution. -/
theorem unselected_argument_name_blocks_application_admission :
    ClosedSourceDataExpression (hiddenArgument s) ∧
    ClosedSourceDataBody (bare s) ∧
    ClosedSourceExpressionEvaluates owner inputs.names environment store
      (call s (lambda s (bare s)) (hiddenArgument s)) .unit store ∧
    elaborateExpectedComputationLambda? elaborateLocalExpression? [] owner inputs
      (lambda s (bare s)) (.function .unit .unit) = some (.lambda .unit .unit .unit) ∧
    resolveLocalExpression? inputs.names (hiddenArgument s) = none := by
  have raw : ClosedSourceExpressionEvaluates owner inputs.names environment store
      (call s (lambda s (bare s)) (hiddenArgument s)) .unit store :=
    .call .inferred (.creation .inferred) (.conditionalTrue (.reference .head .head) .unit) .bare
  exact ⟨.conditional .reference .unit .reference, .bare, raw, by cbv, by cbv⟩

private def created (s : Syntax.SourceSpan) := lambda s (bare s)
private def returning (s : Syntax.SourceSpan) := output s (created s)
private def discarding (s : Syntax.SourceSpan) : Syntax.Block :=
  ⟨s, [⟨s, .expression (created s) true⟩, ⟨s, .returnStmt none⟩]⟩
private def innerNames (s : Syntax.SourceSpan) : LocalNameTable :=
  [((name s).value, Resolved.freshLocalId owner [])]
private def innerCaptured : List (Resolved.LocalId × RuntimeValue) :=
  [(Resolved.freshLocalId owner [], .unit)]

/-- Creation preserves the entire original unchecked body and captures without evaluating it. -/
theorem creation_does_not_admit_a_nongated_body :
    ClosedSourceExpressionEvaluates owner [] [] store (lambda s (returning s))
      (.sourceClosure (lambda s (returning s)) owner [] []) store ∧
    (¬ ClosedSourceDataBody (returning s)) ∧
    elaborateExpectedComputationLambda? elaborateLocalExpression? [] owner .empty
      (lambda s (returning s)) (.function .unit .unit) = none := by
  have raw : ClosedSourceExpressionEvaluates owner [] [] store (lambda s (returning s))
      (.sourceClosure (lambda s (returning s)) owner [] []) store := .creation .inferred
  refine ⟨raw, ?_, by cbv⟩
  intro gate
  cases gate with
  | expression child => cases child

/-- The original returned closure is not the embedding of any Core value. -/
theorem returned_source_closure_is_not_a_core_result :
    ClosedSourceExpressionEvaluates owner [] [] store
      (call s (lambda s (returning s)) (unit s))
      (.sourceClosure (created s) owner (innerNames s) innerCaptured) store ∧
    (¬ ∃ value, RuntimeValue.sourceClosure (created s) owner (innerNames s) innerCaptured =
      RuntimeValue.ofCore value) := by
  have raw : ClosedSourceExpressionEvaluates owner [] [] store
      (call s (lambda s (returning s)) (unit s))
      (.sourceClosure (created s) owner (innerNames s) innerCaptured) store :=
    .call .inferred (.creation .inferred) .unit (.expression (.creation .inferred))
  refine ⟨raw, ?_⟩
  rintro ⟨value, same⟩
  have contradiction := congrArg RuntimeValue.toCore? same
  simp only [RuntimeValue.toCore?, RuntimeValue.toCore?_ofCore, reduceCtorEq] at contradiction

/-- A Core-image final Unit cannot justify dropping a discarded source-only closure. -/
theorem discarded_source_closure_prevents_body_admission :
    ClosedSourceExpressionEvaluates owner [] [] store
      (call s (lambda s (discarding s)) (unit s)) .unit store ∧
    (¬ ClosedSourceDataBody (discarding s)) ∧
    elaborateExpectedComputationLambda? elaborateLocalExpression? [] owner .empty
      (lambda s (discarding s)) (.function .unit .unit) = none := by
  have raw : ClosedSourceExpressionEvaluates owner [] [] store
      (call s (lambda s (discarding s)) (unit s)) .unit store :=
    .call .inferred (.creation .inferred) .unit (.discard (.creation .inferred) .bare)
  refine ⟨raw, ?_, by cbv⟩
  intro gate
  cases gate with
  | discard child _ => cases child

end Tests.ExpectedDataLambdaAdmissionBoundaries
end

section
-- leanmerge: from Solcore.Test.FrontendExpectedDataLambdaBoundaryProperties
/- Checked lambda bodies do not type their actual arguments or enlarge the closed gate. -/
set_option autoImplicit false
namespace Tests.ExpectedDataLambdaBoundaries
open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"LambdaBoundary", by decide⟩], by decide⟩⟩, 295⟩
private def name (s : Syntax.SourceSpan) : Syntax.Identifier := ⟨s, "p"⟩
private def ref (s : Syntax.SourceSpan) : Syntax.Expr := ⟨s, .identifier (name s)⟩
private def unit (s : Syntax.SourceSpan) : Syntax.Expr := ⟨s, .tuple ⟨s, []⟩⟩
private def output (s : Syntax.SourceSpan) (e : Syntax.Expr) : Syntax.Block :=
  ⟨s, [⟨s, .returnStmt (some e)⟩]⟩
private def lambda (s : Syntax.SourceSpan) (b : Syntax.Block) : Syntax.Expr :=
  ⟨s, .lambda s ⟨s, [⟨s, .inferred (name s)⟩]⟩ none b⟩
private def identity (s : Syntax.SourceSpan) := lambda s (output s (ref s))
private def call (s : Syntax.SourceSpan) (f a : Syntax.Expr) : Syntax.Expr :=
  ⟨s, .call f ⟨s, [a]⟩⟩
private def neg (s : Syntax.SourceSpan) (e : Syntax.Expr) : Syntax.Expr :=
  ⟨s, .unary ⟨s, .logicalNot⟩ e⟩

private theorem identity_checked (s : Syntax.SourceSpan) (inputs : LocalTypeInputs)
    (type : Core.Ty) (wf : type.WellFormed []) :
    elaborateExpectedComputationLambda? elaborateLocalExpression? [] owner inputs
      (identity s) (.function type type) = some (.lambda type type (.var 0)) :=
  (elaborateExpectedComputationLambda?_iff (fun {_ _ _ _ _} => Iff.rfl)).mpr
    (.lambda (.lambda .inferred .omitted) wf wf
      (.expression (elaborateLocalExpression?_complete (.identifier .head) (.var .head) (.var .head))))

variable (s : Syntax.SourceSpan) (store : Core.Store)

/-- Word identity still returns actual Unit; this operational bridge is not whole-call typing. -/
theorem checked_word_identity_accepts_actual_unit :
    elaborateExpectedComputationLambda? elaborateLocalExpression? [] owner .empty
      (identity s) (.function .word .word) = some (.lambda .word .word (.var 0)) ∧
    Core.infer? [] (.apply (.lambda .word .word (.var 0)) .unit) = none ∧
    ClosedSourceExpressionEvaluates owner [] [] (store.map RuntimeValue.ofCore)
      (call s (identity s) (unit s)) .unit (store.map RuntimeValue.ofCore) ∧
    Core.Evaluates [] store (.apply (.lambda .word .word (.var 0)) .unit) .unit store ∧
    (∀ actual final, ClosedSourceExpressionEvaluates owner [] [] (store.map RuntimeValue.ofCore)
      (call s (identity s) (unit s)) actual final ↔
        actual = .unit ∧ final = store.map RuntimeValue.ofCore) := by
  have original : ClosedSourceExpressionEvaluates owner [] [] (store.map RuntimeValue.ofCore)
      (call s (identity s) (unit s)) .unit (store.map RuntimeValue.ofCore) :=
    .call .inferred (.creation .inferred) .unit (.expression (.reference .head .head))
  have core : Core.Evaluates [] store (.apply (.lambda .word .word (.var 0)) .unit) .unit store :=
    .apply .lambda .unit (.var rfl)
  have checked := identity_checked s .empty .word .word
  refine ⟨checked, by decide, original, core, ?_⟩
  intro actual final
  have image := closedSourceExpectedDataLambda_application_core_iff
    (owner := owner) (initialStore := store) (callSpan := s) (argumentsSpan := s)
    (argument := unit s) (environment := []) (actualValue := actual) (actualFinal := final)
    .inferred (.expression .reference) checked rfl .unit .unit .unit
  constructor
  · intro evaluated
    obtain ⟨result, finalStore, same, sameFinal, evaluatedCore⟩ := image.mp evaluated
    obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic evaluatedCore core
    exact ⟨by simpa only [RuntimeValue.ofCore] using same, sameFinal⟩
  · rintro ⟨rfl, rfl⟩
    exact image.mpr ⟨.unit, store, by simp only [RuntimeValue.ofCore], rfl, core⟩

/-- The original unary body checks and evaluates successfully and is admitted by the data gate. -/
theorem checked_unary_body_is_outside_closed_gate :
    let b := output s (neg s (ref s))
    let f := lambda s b
    elaborateExpectedComputationLambda? elaborateLocalExpression? [] owner .empty
      f (.function .bool .bool) = some (.lambda .bool .bool (.unary .boolNot (.var 0))) ∧
    (ClosedSourceDataBody b) ∧
    (∀ (choice : Bool) (initial : List RuntimeValue),
      ClosedSourceBodyEvaluates owner [("p", Resolved.freshLocalId owner [])]
        [(Resolved.freshLocalId owner [], .bool choice)] initial b
        (.bool (!choice)) initial) ∧
    Core.Evaluates [] store
      (.apply (.lambda .bool .bool (.unary .boolNot (.var 0))) (.bool true)) (.bool false) store := by
  have checked : elaborateExpectedComputationLambda? elaborateLocalExpression? [] owner .empty
      (lambda s (output s (neg s (ref s)))) (.function .bool .bool) =
        some (.lambda .bool .bool (.unary .boolNot (.var 0))) :=
    (elaborateExpectedComputationLambda?_iff (fun {_ _ _ _ _} => Iff.rfl)).mpr
      (.lambda (.lambda .inferred .omitted) .bool .bool
        (.expression (elaborateLocalExpression?_complete (.logicalNot (.identifier .head))
          (.unary (.var .head)) (.unary (.var .head)))))
  refine ⟨checked, ?_, ?_, .apply .lambda .bool (.unary (.var rfl) rfl)⟩
  · exact .expression (.logicalNot .reference)
  · intro choice initial
    exact .expression (.logicalNot (.reference .head .head))

/-- An original unary argument checks, lowers and evaluates and is admitted by the data gate. -/
theorem checked_unary_argument_is_outside_closed_gate :
    let inputs := LocalTypeInputs.empty.bindFresh owner "p" .bool
    let id := Resolved.freshLocalId owner []
    elaborateExpectedComputationLambda? elaborateLocalExpression? [] owner inputs
      (identity s) (.function .bool .bool) = some (.lambda .bool .bool (.var 0)) ∧
    elaborateLocalExpression? inputs.names inputs.context (neg s (ref s)) =
      some (.unary .boolNot (.var 0), .bool) ∧
    ResolvesLocalExpression inputs.names (neg s (ref s)) (.unary .boolNot (.var id)) ∧
    Resolved.Lowers [id] (.unary .boolNot (.var id)) (.unary .boolNot (.var 0)) ∧
    (ClosedSourceDataExpression (neg s (ref s))) ∧
    (∀ (choice : Bool) (initial : List RuntimeValue),
      ClosedSourceExpressionEvaluates owner inputs.names [(id, .bool choice)]
        initial (neg s (ref s)) (.bool (!choice)) initial) ∧
    Core.Evaluates [.bool true] store
      (.apply (.lambda .bool .bool (.var 0)) (.unary .boolNot (.var 0))) (.bool false) store := by
  have resolution : ResolvesLocalExpression
      (LocalTypeInputs.empty.bindFresh owner "p" .bool).names (neg s (ref s))
      (.unary .boolNot (.var (Resolved.freshLocalId owner []))) := .logicalNot (.identifier .head)
  have lowering : Resolved.Lowers [Resolved.freshLocalId owner []]
      (.unary .boolNot (.var (Resolved.freshLocalId owner []))) (.unary .boolNot (.var 0)) :=
    .unary (.var .head)
  have typed : Resolved.HasType (LocalTypeInputs.empty.bindFresh owner "p" .bool).context
      (.unary .boolNot (.var (Resolved.freshLocalId owner []))) .bool := .unary (.var .head)
  refine ⟨identity_checked s _ .bool .bool, elaborateLocalExpression?_complete resolution lowering typed,
    resolution, lowering, ?_, ?_, .apply .lambda (.unary (.var rfl) rfl) (.var rfl)⟩
  · exact .logicalNot .reference
  · intro choice initial
    exact .logicalNot (.reference .head .head)

/-- Marked and multiple parameters supply neither the shape premise nor expected checking. -/
theorem marked_and_multiple_parameters_are_not_admitted (type : Core.Ty) :
    let p : Syntax.LambdaParameter := ⟨s, .inferred (name s)⟩
    let marked : Syntax.Expr := ⟨s, .lambda s
      ⟨s, [⟨s, .typed (some s) (name s) ⟨s, .tuple []⟩⟩]⟩ none (output s (unit s))⟩
    let multiple : Syntax.Expr := ⟨s, .lambda s ⟨s, [p, p]⟩ none (output s (unit s))⟩
    (¬ ∃ name body, SourceUnaryLambdaShape marked name body) ∧
    (¬ ∃ name body, SourceUnaryLambdaShape multiple name body) ∧
    elaborateExpectedComputationLambda? elaborateLocalExpression? [] owner .empty
      marked (.function type type) = none ∧
    elaborateExpectedComputationLambda? elaborateLocalExpression? [] owner .empty
      multiple (.function type type) = none := by
  refine ⟨?_, ?_, rfl, rfl⟩
  · rintro ⟨name, body, shape⟩; cases shape
  · rintro ⟨name, body, shape⟩; cases shape

end Tests.ExpectedDataLambdaBoundaries
end

section
-- leanmerge: from Solcore.Test.FrontendExpectedDataLambdaImageProperties
/- Arbitrarily nested original identity bodies retain spans, captures and raw payloads. -/
set_option autoImplicit false
namespace Tests.ExpectedDataLambdaImages
open Solcore Solcore.Frontend

private def statements (spans : Nat → Syntax.SourceSpan) (name : Syntax.Identifier) :
    Nat → List Syntax.Statement
  | 0 => [⟨spans 4, .returnStmt (some ⟨spans 5, .identifier name⟩)⟩]
  | n + 1 => [⟨spans (n + 10), .block (statements spans name n)⟩]

private def body (spans : Nat → Syntax.SourceSpan) (name : Syntax.Identifier)
    (depth : Nat) : Syntax.Block := ⟨spans 3, statements spans name depth⟩

private def source (spans : Nat → Syntax.SourceSpan) (name : Syntax.Identifier)
    (depth : Nat) : Syntax.Expr :=
  ⟨spans 0, .lambda (spans 1) ⟨spans 2, [⟨spans 6, .inferred name⟩]⟩
    none (body spans name depth)⟩

private theorem original_body (spans : Nat → Syntax.SourceSpan) (name : Syntax.Identifier)
    (depth : Nat) (blockSpan : Syntax.SourceSpan) (owner : Resolved.DeclarationId)
    (names : LocalNameTable) (captured : List (Resolved.LocalId × RuntimeValue))
    (store : List RuntimeValue) (id : Resolved.LocalId) (value : RuntimeValue) :
    ClosedSourceDataBody ⟨blockSpan, statements spans name depth⟩ ∧
    ClosedSourceBodyEvaluates owner ((name.value, id) :: names) ((id, value) :: captured)
      store ⟨blockSpan, statements spans name depth⟩ value store := by
  induction depth generalizing blockSpan with
  | zero => exact ⟨.expression .reference, .expression (.reference .head .head)⟩
  | succ n ih =>
      have child := ih (spans (n + 10))
      exact ⟨.block child.1, .block child.2⟩

private theorem body_checked (spans : Nat → Syntax.SourceSpan) (name : Syntax.Identifier)
    (depth : Nat) (blockSpan : Syntax.SourceSpan) (types : TypeNameTable)
    (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs) (type : Core.Ty) :
    ComputationReturnTreeElaborates
      (fun table context child core ty => elaborateLocalExpression? table context child = some (core, ty))
      types owner (inputs.bindFresh owner name.value type)
      ⟨blockSpan, statements spans name depth⟩ (.var 0) type := by
  induction depth generalizing blockSpan with
  | zero =>
      apply ComputationReturnTreeElaborates.expression
      exact elaborateLocalExpression?_complete (.identifier .head) (.var .head) (.var .head)
  | succ n ih => exact .block (ih (spans (n + 10)))

private theorem checked (spans : Nat → Syntax.SourceSpan) (name : Syntax.Identifier)
    (depth : Nat) (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (inputs : LocalTypeInputs) (type : Core.Ty) (wf : type.WellFormed []) :
    elaborateExpectedComputationLambda? elaborateLocalExpression? types owner inputs
      (source spans name depth) (.function type type) = some (.lambda type type (.var 0)) :=
  (elaborateExpectedComputationLambda?_iff (fun {_ _ _ _ _} => Iff.rfl)).mpr
    (.lambda (.lambda .inferred .omitted) wf wf
      (body_checked spans name depth (spans 3) types owner inputs type))

private theorem mapped_lookup {environment : Resolved.Environment} {id : Resolved.LocalId}
    {value : Core.Value} (found : Resolved.LocalScope.Lookup environment id value) :
    Resolved.LocalScope.Lookup (environment.map (fun row => (row.1, RuntimeValue.ofCore row.2)))
      id (RuntimeValue.ofCore value) := by
  induction found with
  | head => exact .head
  | tail different _ ih => exact .tail different ih

section Family
variable (spans : Nat → Syntax.SourceSpan) (name : Syntax.Identifier) (depth : Nat)
  (types : TypeNameTable) (savedOwner : Resolved.DeclarationId) (inputs : LocalTypeInputs)
  (environment : Resolved.Environment) (store : Core.Store) (value : Core.Value)
  (type : Core.Ty) (wf : type.WellFormed [])
  (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids inputs.context)

local notation "original" => source spans name depth
local notation "captures" => List.map (fun row => (Prod.fst row, RuntimeValue.ofCore (Prod.snd row))) environment
local notation "heap" => store.map RuntimeValue.ofCore

include wf in
/-- Source and Core identity endpoints are constructed without a correspondence law. -/
theorem independent_body_and_checker :
    ClosedSourceDataBody (body spans name depth) ∧
    elaborateExpectedComputationLambda? elaborateLocalExpression? types savedOwner inputs
      original (.function type type) = some (.lambda type type (.var 0)) ∧
    Core.Evaluates (value :: Resolved.LocalScope.values environment) store (.var 0) value store := by
  exact ⟨(original_body spans name depth (spans 3) savedOwner inputs.names captures heap
    (Resolved.freshLocalId savedOwner inputs.ids) (RuntimeValue.ofCore value)).1,
    checked spans name depth types savedOwner inputs type wf, .var rfl⟩

section Invocation
variable (callerOwner : Resolved.DeclarationId) (callerNames : LocalNameTable)
  (callerCaptured : List (Resolved.LocalId × RuntimeValue))
  (calleeName argumentName : Syntax.Identifier) (calleeId argumentId : Resolved.LocalId)
  (calleeNamed : LocalNameTable.Lookup callerNames calleeName.value calleeId)
  (calleeFound : Resolved.LocalScope.Lookup callerCaptured calleeId
    (.sourceClosure (source spans name depth) savedOwner inputs.names
      (environment.map (fun row => (row.1, RuntimeValue.ofCore row.2)))))
  (argumentNamed : LocalNameTable.Lookup callerNames argumentName.value argumentId)
  (argumentFound : Resolved.LocalScope.Lookup callerCaptured argumentId (RuntimeValue.ofCore value))

include calleeNamed calleeFound argumentNamed argumentFound in
private theorem invocation_source :
    ClosedSourceExpressionEvaluates callerOwner callerNames callerCaptured heap
      ⟨spans 7, .call ⟨spans 8, .identifier calleeName⟩
        ⟨spans 9, [⟨spans 10, .identifier argumentName⟩]⟩⟩ (RuntimeValue.ofCore value) heap :=
  .call .inferred (.reference calleeNamed calleeFound) (.reference argumentNamed argumentFound)
    (original_body spans name depth (spans 3) savedOwner inputs.names captures heap
      (Resolved.freshLocalId savedOwner (inputs.names.map Prod.snd)) (RuntimeValue.ofCore value)).2

include types wf sameIds calleeNamed calleeFound argumentNamed argumentFound in
/-- Arbitrary mixed caller rows invoke the saved identity with its entire store. -/
theorem invocation_original_and_all_actual_images :
    let call : Syntax.Expr := ⟨spans 7, .call ⟨spans 8, .identifier calleeName⟩
      ⟨spans 9, [⟨spans 10, .identifier argumentName⟩]⟩⟩
    ClosedSourceExpressionEvaluates callerOwner callerNames callerCaptured heap call
      (RuntimeValue.ofCore value) heap ∧
    ∀ actual final, ClosedSourceExpressionEvaluates callerOwner callerNames callerCaptured heap
      call actual final ↔ actual = RuntimeValue.ofCore value ∧ final = heap := by
  have originalEvaluation := invocation_source spans name depth savedOwner inputs environment store value
    callerOwner callerNames callerCaptured calleeName argumentName calleeId argumentId
    calleeNamed calleeFound argumentNamed argumentFound
  have paths := independent_body_and_checker spans name depth types savedOwner inputs
    environment store value type wf
  refine ⟨originalEvaluation, ?_⟩
  intro actual final
  have image := closedSourceExpectedDataLambda_invocation_core_iff
    (callerOwner := callerOwner) (bodyStore := store)
    (callSpan := spans 7) (argumentsSpan := spans 9)
    (callee := ⟨spans 8, .identifier calleeName⟩) (argument := ⟨spans 10, .identifier argumentName⟩)
    (actualValue := actual) (actualFinal := final) .inferred paths.1 paths.2.1 sameIds
    (.reference calleeNamed calleeFound) (.reference argumentNamed argumentFound)
  constructor
  · intro evaluated
    obtain ⟨result, finalStore, same, sameFinal, core⟩ := image.mp evaluated
    obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic core paths.2.2
    exact ⟨same, sameFinal⟩
  · rintro ⟨rfl, rfl⟩
    exact image.mpr ⟨value, store, rfl, rfl, paths.2.2⟩

end Invocation

section Application
variable (argumentName : Syntax.Identifier) (argumentId : Resolved.LocalId) (index : Nat)
  (argumentNamed : LocalNameTable.Lookup inputs.names argumentName.value argumentId)
  (argumentFound : Resolved.LocalScope.Lookup environment argumentId value)
  (argumentIndex : Resolved.LocalScope.IndexOf (Resolved.LocalScope.ids environment) argumentId index)

include argumentNamed argumentFound in
private theorem application_source :
    ClosedSourceExpressionEvaluates savedOwner inputs.names captures heap
      ⟨spans 7, .call original ⟨spans 9, [⟨spans 10, .identifier argumentName⟩]⟩⟩
      (RuntimeValue.ofCore value) heap :=
  .call .inferred (.creation .inferred) (.reference argumentNamed (mapped_lookup argumentFound))
    (original_body spans name depth (spans 3) savedOwner inputs.names captures heap
      (Resolved.freshLocalId savedOwner (inputs.names.map Prod.snd)) (RuntimeValue.ofCore value)).2

include argumentFound argumentIndex in
private theorem application_core :
    Core.Evaluates (Resolved.LocalScope.values environment) store
      (.apply (.lambda type type (.var 0)) (.var index)) value store :=
  .apply .lambda (.var ((Resolved.LocalScope.lookup_iff_getElem? argumentIndex).mp argumentFound))
    (.var rfl)

include types wf sameIds argumentNamed argumentFound argumentIndex in
/-- Direct original application preserves an opaque reference payload, with no domain typing premise. -/
theorem application_original_and_all_actual_images :
    let call : Syntax.Expr :=
      ⟨spans 7, .call original ⟨spans 9, [⟨spans 10, .identifier argumentName⟩]⟩⟩
    ClosedSourceExpressionEvaluates savedOwner inputs.names captures heap call
      (RuntimeValue.ofCore value) heap ∧
    ∀ actual final, ClosedSourceExpressionEvaluates savedOwner inputs.names captures heap
      call actual final ↔ actual = RuntimeValue.ofCore value ∧ final = heap := by
  have originalEvaluation := application_source spans name depth savedOwner inputs environment store value
    argumentName argumentId argumentNamed argumentFound
  have independent := application_core environment store value type argumentId index argumentFound argumentIndex
  have paths := independent_body_and_checker spans name depth types savedOwner inputs
    environment store value type wf
  refine ⟨originalEvaluation, ?_⟩
  intro actual final
  have image := closedSourceExpectedDataLambda_application_core_iff
    (callSpan := spans 7) (argumentsSpan := spans 9) (initialStore := store)
    (argument := ⟨spans 10, .identifier argumentName⟩) (actualValue := actual) (actualFinal := final)
    .inferred paths.1 paths.2.1 sameIds .reference (.identifier argumentNamed) (.var argumentIndex)
  constructor
  · intro evaluated
    obtain ⟨result, finalStore, same, sameFinal, core⟩ := image.mp evaluated
    obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic core independent
    exact ⟨same, sameFinal⟩
  · rintro ⟨rfl, rfl⟩
    exact image.mpr ⟨value, store, rfl, rfl, independent⟩

end Application
end Family
end Tests.ExpectedDataLambdaImages
end

section
-- leanmerge: from Solcore.Test.FrontendExpectedLambdaArgumentApplicationProperties
/-! Independent symbolic consumers for expected-type lambda arguments. -/

set_option autoImplicit false

namespace Tests.ADR0317ExpectedLambdaArgumentConsumer

open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"ExpectedLambdaArgument", by decide⟩], by decide⟩⟩, 317⟩
private def foreignOwner : Resolved.DeclarationId := { owner with declarationIndex := 991 }
private def applyId : Resolved.LocalId := ⟨owner, 17⟩
private def opaqueId : Resolved.LocalId := ⟨foreignOwner, 700⟩
private def duplicateId : Resolved.LocalId := ⟨owner, 3⟩
private def flagId : Resolved.LocalId := ⟨foreignOwner, 701⟩

private def functionType : Core.Ty := .function .word .word
private def inputs : LocalTypeInputs := ⟨[
  ⟨"apply", applyId, .function functionType .word⟩,
  ⟨"opaque", opaqueId, .cell .word⟩,
  ⟨"apply", duplicateId, .unit⟩,
  ⟨"flag", flagId, .bool⟩
], by decide⟩
private def types : TypeNameTable := []
private def file : Syntax.SourceId := ⟨.main, "expected-lambda-argument.sol"⟩
private def span (n : Nat) : Syntax.SourceSpan := ⟨file, n, 1⟩
private def ref (n : Nat) (name : String) : Syntax.Expr :=
  ⟨span n, .identifier ⟨span (n + 1), name⟩⟩
private def body : Syntax.Block :=
  ⟨span 6, [⟨span 7, .returnStmt (some (ref 8 "x"))⟩]⟩
private def argument : Syntax.Expr :=
  ⟨span 3, .lambda (span 4)
    ⟨span 5, [⟨span 5, .inferred ⟨span 5, "x"⟩⟩]⟩ none body⟩
private def source : Syntax.Expr :=
  ⟨span 0, .call (ref 1 "apply") ⟨span 2, [argument]⟩⟩
private def core : Core.Expr :=
  .apply (.var 0) (.lambda .word .word (.var 0))

private theorem calleeElaboration :
    RecursiveLocalComputationElaborates inputs.names inputs.context
      (ref 1 "apply") (.var 0) (.function functionType .word) :=
  .pure (.identifier .head) (.var .head) (.var .head)

private theorem argumentElaboration :
    ExpectedComputationLambdaElaborates RecursiveLocalComputationElaborates
      types owner inputs argument (.lambda .word .word (.var 0)) functionType := by
  apply ExpectedComputationLambdaElaborates.lambda
    (header := ⟨inputs.bindFresh owner "x" .word, body, .word, .word⟩)
  · exact ExpectedUnaryLambdaHeaderDeclares.lambda
      ExpectedLambdaParameterDeclares.inferred ExpectedLambdaReturnDenotes.omitted
  · exact .word
  · exact .word
  · exact ComputationReturnTreeElaborates.expression
      (RecursiveLocalComputationElaborates.pure
        (ResolvesLocalExpression.identifier .head) (Resolved.Lowers.var .head)
        (Resolved.HasType.var .head))

private theorem independent :
    ExpectedLambdaArgumentApplicationElaborates types owner inputs source core .word :=
  .application calleeElaboration argumentElaboration

theorem checked_literal_application_and_static_boundary :
    ExpectedLambdaArgumentApplicationElaborates types owner inputs source core .word ∧
    elaborateExpectedLambdaArgumentApplication? types owner inputs source =
      some (core, .word) ∧
    Core.HasType inputs.context.values core .word ∧
    elaborateRecursiveLocalComputation? inputs.names inputs.context source = none := by
  have checked := elaborateExpectedLambdaArgumentApplication?_iff.mpr independent
  have restored := elaborateExpectedLambdaArgumentApplication?_iff.mp checked
  exact ⟨independent, checked, restored.core_hasType, by
    simp [source, argument, elaborateRecursiveLocalComputation?, elaborateLocalExpression?,
      resolveLocalExpression?]⟩

private def nonFunctionCall : Syntax.Expr :=
  ⟨span 23, .call (ref 24 "flag") ⟨span 25, [argument]⟩⟩
private def ordinaryCall : Syntax.Expr :=
  ⟨span 26, .call (ref 1 "apply") ⟨span 27, [ref 28 "flag"]⟩⟩
private def emptyCall : Syntax.Expr :=
  ⟨span 29, .call (ref 1 "apply") ⟨span 30, []⟩⟩
private def manyCall : Syntax.Expr :=
  ⟨span 31, .call (ref 1 "apply") ⟨span 32, [argument, argument]⟩⟩

private theorem flagElaboration :
    RecursiveLocalComputationElaborates inputs.names inputs.context
      (ref 24 "flag") (.var 3) .bool :=
  .pure
    (.identifier (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
    (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
    (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))

theorem unsupported_shapes_remain_exact_absence :
    elaborateExpectedLambdaArgumentApplication? types owner inputs nonFunctionCall = none ∧
    elaborateExpectedLambdaArgumentApplication? types owner inputs ordinaryCall = none ∧
    elaborateExpectedLambdaArgumentApplication? types owner inputs emptyCall = none ∧
    elaborateExpectedLambdaArgumentApplication? types owner inputs manyCall = none ∧
    elaborateExpectedLambdaArgumentApplication? types owner inputs argument = none := by
  have applyChecked := elaborateRecursiveLocalComputation?_iff.mpr calleeElaboration
  have flagChecked := elaborateRecursiveLocalComputation?_iff.mpr flagElaboration
  refine ⟨?_, ?_, rfl, rfl, rfl⟩
  · simp only [nonFunctionCall, elaborateExpectedLambdaArgumentApplication?, flagChecked,
      bind, Option.bind_some]
  · simp only [ordinaryCall, elaborateExpectedLambdaArgumentApplication?, applyChecked,
      bind, Option.bind_some]
    rfl

private def seven : Core.Word := Core.Word.ofNatModulo 7
private def applyBody : Core.Expr := .apply (.var 0) (.word seven)
private def applyValue : Core.Value :=
  .closure functionType .word applyBody []

theorem independently_executed_core_application_keeps_arbitrary_rows
    (opaqueValue duplicateValue flagValue : Core.Value) (store : Core.Store) :
    let environment := [applyValue, opaqueValue, duplicateValue, flagValue]
    Core.Evaluates environment store core (.word seven) store := by
  intro environment
  exact Core.Evaluates.apply
    (Core.Evaluates.var rfl)
    Core.Evaluates.lambda
    (Core.Evaluates.apply
      (Core.Evaluates.var rfl)
      Core.Evaluates.word
      (Core.Evaluates.var rfl))

end Tests.ADR0317ExpectedLambdaArgumentConsumer
end

section
-- leanmerge: from Solcore.Test.FrontendExpectedLambdaHeaderProperties
/-! Original symbolic headers retain every supplied range and outer row. Header
meaning precedes executable checking and requires no runtime inhabitants. The
separate return-body examples do not elaborate or evaluate a source lambda. -/
set_option autoImplicit false
namespace Tests.FrontendExpectedLambdaHeader
open Solcore Solcore.Frontend
private structure Written where
  sourceSpan : Syntax.SourceSpan
  keyword : Syntax.SourceSpan
  parametersSpan : Syntax.SourceSpan
  parameterSpan : Syntax.SourceSpan
  name : Syntax.Identifier
  body : Syntax.Block
private def source (w : Written) (parameter : Syntax.LambdaParameterValue) (returns : Option Syntax.TypeExpr) : Syntax.Expr :=
  ⟨w.sourceSpan,.lambda w.keyword ⟨w.parametersSpan,[⟨w.parameterSpan,parameter⟩]⟩ returns w.body⟩
private def inferred (w : Written) : Syntax.Expr := source w (.inferred w.name) none
private def result (w : Written) (o : Resolved.DeclarationId) (i : LocalTypeInputs) (a b : Core.Ty) : DeclaredUnaryLambdaHeader :=
  ⟨i.bindFresh o w.name.value a,w.body,a,b⟩
private theorem original (types : TypeNameTable) (w : Written) (o : Resolved.DeclarationId)
    (i : LocalTypeInputs) (a b : Core.Ty) :
    ExpectedUnaryLambdaHeaderDeclares types o i (inferred w) (.function a b) (result w o i a b) :=
  .lambda .inferred .omitted
private def named (span : Syntax.SourceSpan) (name : String) : Syntax.TypeExpr :=
  ⟨span,.named ⟨span,⟨⟨⟨span,name⟩,[]⟩⟩⟩ none⟩

theorem arbitrary_expected_components_need_neither_annotations_nor_runtime_inhabitants
    (types : TypeNameTable) (w : Written) (o : Resolved.DeclarationId) (i : LocalTypeInputs) (a b : Core.Ty) :
    ExpectedUnaryLambdaHeaderDeclares types o i (inferred w) (.function a b) (result w o i a b) ∧
      declareExpectedUnaryLambdaHeader? types o i (inferred w) (.function a b)=some (result w o i a b) ∧
      (result w o i a b).body=w.body ∧ (result w o i a b).returnType=b :=
  ⟨original types w o i a b,declareExpectedUnaryLambdaHeader?_iff.mpr (original types w o i a b),rfl,rfl⟩
theorem explicit_and_inferred_original_headers_have_the_same_exact_inner_record
    (types : TypeNameTable) (w : Written) (o : Resolved.DeclarationId) (i : LocalTypeInputs) (a b : Core.Ty)
    (parameterAnnotation returnAnnotation : Syntax.TypeExpr)
    (pa : StructuralTypeDenotes types parameterAnnotation a) (ra : StructuralTypeDenotes types returnAnnotation b) :
    ExpectedUnaryLambdaHeaderDeclares types o i (source w (.typed none w.name parameterAnnotation) (some returnAnnotation))
      (.function a b) (result w o i a b) ∧
      declareExpectedUnaryLambdaHeader? types o i (source w (.typed none w.name parameterAnnotation) (some returnAnnotation)) (.function a b)=
        declareExpectedUnaryLambdaHeader? types o i (inferred w) (.function a b) := by
  have explicit : ExpectedUnaryLambdaHeaderDeclares types o i
      (source w (.typed none w.name parameterAnnotation) (some returnAnnotation)) (.function a b) (result w o i a b) :=
    .lambda (.typed pa) (.annotated ra)
  exact ⟨explicit,(declareExpectedUnaryLambdaHeader?_iff.mpr explicit).trans
    (declareExpectedUnaryLambdaHeader?_iff.mpr (original types w o i a b)).symm⟩
theorem every_independent_result_is_the_original_body_with_one_fresh_row
    (types : TypeNameTable) (w : Written) (o : Resolved.DeclarationId) (i : LocalTypeInputs) (a b : Core.Ty)
    (out : DeclaredUnaryLambdaHeader)
    (evidence : ExpectedUnaryLambdaHeaderDeclares types o i (inferred w) (.function a b) out) :
    out=result w o i a b ∧ out.body=w.body ∧ out.inputs.bindings=
      {name:=w.name.value,id:=Resolved.freshLocalId o i.ids,type:=a}::i.bindings ∧
      Resolved.freshLocalId o i.ids ∉ i.ids := by
  have same := evidence.result_unique (original types w o i a b)
  rw [same]
  exact ⟨rfl,rfl,rfl,Resolved.freshLocalId_not_mem o i.ids⟩
theorem provenance_contains_original_syntax_and_both_expected_components
    (types : TypeNameTable) (o : Resolved.DeclarationId) (i : LocalTypeInputs)
    (src : Syntax.Expr) (expected : Core.Ty) (out : DeclaredUnaryLambdaHeader)
    (evidence : ExpectedUnaryLambdaHeaderDeclares types o i src expected out) :
    ∃ sourceSpan keyword parametersSpan parameter returns, ∃ name : Syntax.Identifier,
      src=⟨sourceSpan,.lambda keyword ⟨parametersSpan,[parameter]⟩ returns out.body⟩ ∧
      expected=.function out.parameterType out.returnType ∧
      ExpectedLambdaReturnDenotes types returns out.returnType ∧
      out.inputs=i.bindFresh o name.value out.parameterType := by
  obtain ⟨sp,kw,ps,p,ret,name,shape,expected,_,meaning,inputs,_⟩ := evidence.provenance_and_layout
  exact ⟨sp,kw,ps,p,ret,name,shape,expected,meaning,inputs⟩
theorem original_parameter_spelling_shadows_without_deleting_any_outer_binding
    (types : TypeNameTable) (w : Written) (o : Resolved.DeclarationId) (i : LocalTypeInputs) (a b : Core.Ty) :
    ExpectedUnaryLambdaHeaderDeclares types o i (inferred w) (.function a b) (result w o i a b) ∧
      LocalNameTable.Lookup (result w o i a b).inputs.names w.name.value (Resolved.freshLocalId o i.ids) ∧
      Resolved.LocalScope.Lookup (result w o i a b).inputs.context (Resolved.freshLocalId o i.ids) a ∧
      (result w o i a b).inputs.context.values=a::i.context.values ∧
      (result w o i a b).inputs.bindings.tail=i.bindings :=
  ⟨original types w o i a b,.head,.head,rfl,rfl⟩
theorem annotation_meanings_keep_first_match_priority_even_under_same_spelling_shadow
    (w : Written) (o : Resolved.DeclarationId) (i : LocalTypeInputs) (a b hidden : Core.Ty) :
    let table : TypeNameTable := [([w.name.value],a),([w.name.value],hidden)]
    declareExpectedUnaryLambdaHeader? table o i
      (source w (.typed none w.name (named w.name.span w.name.value)) none) (.function a b)=some (result w o i a b) :=
  declareExpectedUnaryLambdaHeader?_iff.mpr (.lambda (.typed (.named .head)) .omitted)
theorem explicit_return_disagreement_has_no_header_derivation
    (types : TypeNameTable) (w : Written) (o : Resolved.DeclarationId) (i : LocalTypeInputs)
    (a actual expected : Core.Ty) (annotation : Syntax.TypeExpr)
    (meaning : StructuralTypeDenotes types annotation actual) (different : actual≠expected) :
    declareExpectedUnaryLambdaHeader? types o i (source w (.inferred w.name) (some annotation)) (.function a expected)=none ∧
      ¬ ∃ out,ExpectedUnaryLambdaHeaderDeclares types o i (source w (.inferred w.name) (some annotation)) (.function a expected) out := by
  have absent : ¬ ∃ out,ExpectedUnaryLambdaHeaderDeclares types o i
      (source w (.inferred w.name) (some annotation)) (.function a expected) out := by
    rintro ⟨out,evidence⟩
    cases evidence with
    | lambda _ returns => cases returns with
      | annotated found => exact different (meaning.type_unique found)
  exact ⟨declareExpectedUnaryLambdaHeader?_eq_none_iff.mpr absent,absent⟩

private def returned (w : Written) : Syntax.Block :=
  ⟨w.body.span,[⟨w.body.span,.returnStmt (some ⟨w.name.span,.identifier w.name⟩)⟩]⟩
private theorem returnedElab (types : TypeNameTable) (w : Written) (o : Resolved.DeclarationId) (i : LocalTypeInputs) (a : Core.Ty) :
    RecursiveComputationReturnTreeElaborates types o (i.bindFresh o w.name.value a) (returned w) (.var 0) a :=
  .expression (.pure (.identifier .head) (.var .head) (.var .head))
theorem a_separate_original_body_proof_can_use_the_declared_parameter_but_is_not_a_lambda_proof
    (types : TypeNameTable) (w : Written) (o : Resolved.DeclarationId) (i : LocalTypeInputs) (a : Core.Ty) :
    let written := {w with body:=returned w}
    let out := result written o i a a
    ExpectedUnaryLambdaHeaderDeclares types o i (inferred written) (.function a a) out ∧
      RecursiveComputationReturnTreeElaborates types o out.inputs out.body (.var 0) a ∧
      elaborateRecursiveComputationReturnTree? types o out.inputs out.body=some (.var 0,a) ∧
      elaborateRecursiveLocalComputation? i.names i.context (inferred written)=none := by
  refine ⟨original types _ o i a a,returnedElab types w o i a,?_,?_⟩
  · exact (elaborateComputationReturnTree?_iff elaborateRecursiveLocalComputation?_iff).mpr (returnedElab types w o i a)
  · simp [inferred,source,elaborateRecursiveLocalComputation?,elaborateLocalExpression?,resolveLocalExpression?]
theorem an_omitted_return_annotation_does_not_check_the_actual_return_body
    (types : TypeNameTable) (w : Written) (o : Resolved.DeclarationId) (i : LocalTypeInputs) (a b : Core.Ty) (different : a≠b) :
    let written := {w with body:=returned w}
    let out := result written o i a b
    declareExpectedUnaryLambdaHeader? types o i (inferred written) (.function a b)=some out ∧
      ¬ ∃ core,RecursiveComputationReturnTreeElaborates types o out.inputs out.body core b := by
  refine ⟨declareExpectedUnaryLambdaHeader?_iff.mpr (original types _ o i a b),?_⟩
  rintro ⟨core,wrong⟩
  have right := (elaborateComputationReturnTree?_iff elaborateRecursiveLocalComputation?_iff).mpr (returnedElab types w o i a)
  have other := (elaborateComputationReturnTree?_iff elaborateRecursiveLocalComputation?_iff).mpr wrong
  change elaborateRecursiveComputationReturnTree? types o (i.bindFresh o w.name.value a) (returned w)=some (core,b) at other
  exact different (congrArg Prod.snd (Option.some.inj (right.symm.trans other)))
theorem an_explicit_error_body_is_retained_and_not_mistaken_for_a_checked_body
    (types : TypeNameTable) (w : Written) (o : Resolved.DeclarationId) (i : LocalTypeInputs) (a b : Core.Ty) :
    let written := {w with body:=⟨w.body.span,[⟨w.body.span,.error⟩]⟩}
    let out := result written o i a b
    declareExpectedUnaryLambdaHeader? types o i (inferred written) (.function a b)=some out ∧
      out.body=written.body ∧ elaborateRecursiveComputationReturnTree? types o out.inputs out.body=none ∧
      elaborateRecursiveLocalComputation? i.names i.context (inferred written)=none := by
  refine ⟨declareExpectedUnaryLambdaHeader?_iff.mpr (original types _ o i a b),rfl,?_,?_⟩
  · simp [result,elaborateRecursiveComputationReturnTree?,elaborateComputationReturnTree?]
  · simp [inferred,source,elaborateRecursiveLocalComputation?,elaborateLocalExpression?,resolveLocalExpression?]

private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"ExpectedLambdaHeader",by decide⟩],by decide⟩⟩,143⟩
private def foreign : Resolved.DeclarationId := {owner with declarationIndex:=144}
private def sparse (name : String) (a : Core.Ty) (high : Nat) : LocalTypeInputs :=
  ⟨[⟨name,⟨owner,7⟩,a⟩,⟨name,⟨foreign,high⟩,.bool⟩,⟨"old",⟨owner,2⟩,.word⟩],by simp [owner,foreign]⟩
theorem sparse_owner_indices_ignore_arbitrarily_large_foreign_rows
    (types : TypeNameTable) (w : Written) (a b oldType : Core.Ty) (high : Nat) :
    let outer := sparse w.name.value oldType high
    let out := result w owner outer a b
    ExpectedUnaryLambdaHeaderDeclares types owner outer (inferred w) (.function a b) out ∧
      out.inputs.ids=[⟨owner,8⟩,⟨owner,7⟩,⟨foreign,high⟩,⟨owner,2⟩] ∧
      out.inputs.bindings.map (fun row => (row.name,row.type))=
        [(w.name.value,a),(w.name.value,oldType),(w.name.value,.bool),("old",.word)] :=
  ⟨original types w owner _ a b,rfl,rfl⟩
end Tests.FrontendExpectedLambdaHeader
end

section
-- leanmerge: from Solcore.Test.FrontendExpectedLambdaLetBodyProperties
/-! Original source typing precedes elaboration and checking. The leading new f
captures the old f in its initializer scope; only the original tail sees new f.
Arbitrary outer rows and well-formed component types need no runtime inhabitants. -/
set_option autoImplicit false
namespace Tests.FrontendExpectedLambdaLetBody
open Solcore Solcore.Frontend
private structure Scenario where
  span : Syntax.SourceSpan
  owner : Resolved.DeclarationId
  outer : LocalTypeInputs
  a : Core.Ty
  b : Core.Ty
  depth : Nat
  typedParameter : Bool
  domain : Core.Ty.WellFormed [] a
  codomain : Core.Ty.WellFormed [] b
private def fn (p : Scenario) : Core.Ty := .function p.a p.b
private def types (p : Scenario) : TypeNameTable := [(["F"],fn p),(["F"],.bool),(["A"],p.a)]
private def named (p : Scenario) (name : String) : Syntax.TypeExpr :=
  ⟨p.span,.named ⟨p.span,⟨⟨⟨p.span,name⟩,[]⟩⟩⟩ none⟩
private def ref (p : Scenario) (name : String) : Syntax.Expr := ⟨p.span,.identifier ⟨p.span,name⟩⟩
private def call (p : Scenario) (argument : String) : Syntax.Expr :=
  ⟨p.span,.call (ref p "f") ⟨p.span,[ref p argument]⟩⟩
private def argumentScope (p : Scenario) := p.outer.bindFresh p.owner "y" p.a
private def initial (p : Scenario) := (argumentScope p).bindFresh p.owner "f" (fn p)
private def oldId (p : Scenario) := Resolved.freshLocalId p.owner (argumentScope p).ids
private def nextId (p : Scenario) := Resolved.freshLocalId p.owner (initial p).ids
private def lambdaInputs (p : Scenario) := (initial p).bindFresh p.owner "x" p.a
private def tailInputs (p : Scenario) : Nat → LocalTypeInputs
  | 0 => (initial p).bindFresh p.owner "f" (fn p)
  | n+1 => (tailInputs p n).bindFresh p.owner "y" p.a
private def lambdaBody (p : Scenario) : Syntax.Block := ⟨p.span,[⟨p.span,.returnStmt (some (call p "x"))⟩]⟩
private def initializer (p : Scenario) : Syntax.Expr :=
  ⟨p.span,.lambda p.span ⟨p.span,[⟨p.span,if p.typedParameter then
    .typed none ⟨p.span,"x"⟩ (named p "A") else .inferred ⟨p.span,"x"⟩⟩]⟩ none (lambdaBody p)⟩
private def tailStatements (p : Scenario) : Nat → List Syntax.Statement
  | 0 => [⟨p.span,.returnStmt (some (call p "y"))⟩]
  | n+1 => ⟨p.span,.letDecl ⟨p.span,"y"⟩ (some (named p "A")) (some (ref p "y"))⟩::
      ⟨p.span,.letDecl ⟨p.span,"y"⟩ none (some (ref p "y"))⟩::tailStatements p n
private def source (p : Scenario) : Syntax.Block :=
  ⟨p.span,⟨p.span,.letDecl ⟨p.span,"f"⟩ (some (named p "F")) (some (initializer p))⟩::tailStatements p p.depth⟩
private theorem aMeaning (p : Scenario) : StructuralTypeDenotes (types p) (named p "A") p.a :=
  .named (.tail (by change (["F"] : List String) ≠ ["A"]; decide)
    (.tail (by change (["F"] : List String) ≠ ["A"]; decide) .head))
private theorem freshNeOld (p : Scenario) : nextId p ≠ oldId p :=
  Resolved.freshLocalId_cons_fresh_ne p.owner (argumentScope p).ids
private theorem lambdaTyped (p : Scenario) :
    ExpectedComputationLambdaHasType RecursiveLocalComputationHasType (types p) p.owner (initial p) (initializer p) (fn p) := by
  have header : ExpectedUnaryLambdaHeaderDeclares (types p) p.owner (initial p) (initializer p) (fn p)
      ⟨lambdaInputs p,lambdaBody p,p.a,p.b⟩ := by
    cases typed : p.typedParameter
    · simp only [initializer,typed,Bool.false_eq_true,ite_false]; exact .lambda .inferred .omitted
    · simp only [initializer,typed,ite_true]; exact .lambda (.typed (aMeaning p)) .omitted
  exact .lambda header p.domain p.codomain (.expression (.application
    (.pure (.identifier (.tail (by change "x" ≠ "f"; decide) .head) (.tail (freshNeOld p) .head)))
    (.pure (.identifier .head .head))))
private theorem tailFunction (p : Scenario) (m : Nat) :
    LocalNameTable.Lookup (tailInputs p m).names "f" (nextId p) ∧
    Resolved.LocalScope.Lookup (tailInputs p m).context (nextId p) (fn p) := by
  induction m with
  | zero => exact ⟨.head,.head⟩
  | succ m ih =>
      have different : Resolved.freshLocalId p.owner (tailInputs p m).ids ≠ nextId p := by
        intro same
        have member : nextId p ∈ (tailInputs p m).names.map Prod.snd :=
          List.mem_map.mpr ⟨("f",nextId p),ih.1.mem,rfl⟩
        rw [LocalTypeInputs.names_ids] at member
        exact Resolved.freshLocalId_not_mem p.owner _ (same ▸ member)
      exact ⟨.tail (by change "y" ≠ "f"; decide) ih.1,.tail different ih.2⟩
private theorem tailArgument (p : Scenario) (m : Nat) :
    RecursiveLocalComputationHasType (tailInputs p m).names (tailInputs p m).context (ref p "y") p.a := by
  cases m with
  | zero =>
      have newNeArgument : nextId p ≠ Resolved.freshLocalId p.owner p.outer.ids := by
        intro same
        apply Resolved.freshLocalId_not_mem p.owner (initial p).ids
        change nextId p ∈ (initial p).ids
        rw [same]
        simp [initial,argumentScope]
      exact .pure (.identifier
        (.tail (by change "f" ≠ "y"; decide) (.tail (by change "f" ≠ "y"; decide) .head))
        (.tail newNeArgument (.tail (Resolved.freshLocalId_cons_fresh_ne p.owner p.outer.ids) .head)))
  | succ m => exact .pure (.identifier .head .head)
private theorem tailTyped (p : Scenario) (n m : Nat) :
    RecursiveComputationReturnTreeHasType (types p) p.owner (tailInputs p m) ⟨p.span,tailStatements p n⟩ p.b := by
  induction n generalizing m with
  | zero => exact .expression (.application
      (.pure (.identifier (tailFunction p m).1 (tailFunction p m).2)) (tailArgument p m))
  | succ n ih =>
      exact .binding (aMeaning p) (tailArgument p m) (.inferred (tailArgument p (m+1)) (ih (m+2)))
private theorem original (p : Scenario) :
    ExpectedLambdaLetBodyHasType RecursiveLocalComputationHasType (types p) p.owner (initial p) (source p) p.b :=
  .binding (.named .head) (lambdaTyped p) (tailTyped p p.depth 0)

theorem original_source_typing_checks_the_initializer_before_the_outer_binding (p : Scenario) :
    ExpectedComputationLambdaHasType RecursiveLocalComputationHasType (types p) p.owner (initial p) (initializer p) (fn p) ∧
      RecursiveComputationReturnTreeHasType (types p) p.owner (tailInputs p 0) ⟨p.span,tailStatements p p.depth⟩ p.b ∧
      ExpectedLambdaLetBodyHasType RecursiveLocalComputationHasType (types p) p.owner (initial p) (source p) p.b :=
  ⟨lambdaTyped p,tailTyped p p.depth 0,original p⟩
theorem an_independent_elaboration_exists_only_after_source_typing (p : Scenario) :
    ∃ core,ExpectedLambdaLetBodyElaborates RecursiveLocalComputationElaborates (types p) p.owner (initial p) (source p) core p.b :=
  (expectedLambdaLetBodyHasType_iff_elaborates recursiveLocalComputationHasType_iff_elaborates).mp (original p)
theorem the_existing_child_checker_matches_the_independent_source_result (p : Scenario) :
    ∃ core,elaborateExpectedLambdaLetBody? elaborateRecursiveLocalComputation? (types p) p.owner (initial p) (source p)=some (core,p.b) ∧
      ExpectedLambdaLetBodyElaborates RecursiveLocalComputationElaborates (types p) p.owner (initial p) (source p) core p.b := by
  obtain ⟨core,checked⟩ := (expectedLambdaLetBodyHasType_iff_checked recursiveLocalComputationHasType_iff_elaborates
    elaborateRecursiveLocalComputation?_iff).mp (original p)
  exact ⟨core,checked,(elaborateExpectedLambdaLetBody?_iff elaborateRecursiveLocalComputation?_iff).mp checked⟩
theorem core_typing_of_independent_elaboration_needs_no_checker_premise
    (table : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs)
    (source : Syntax.Block) (core : Core.Expr) (type : Core.Ty)
    (e : ExpectedLambdaLetBodyElaborates RecursiveLocalComputationElaborates table owner inputs source core type) :
    Core.HasType inputs.context.values core type := e.core_hasType RecursiveLocalComputationElaborates.core_hasType
theorem either_witness_recovers_source_typing_without_runtime_arguments
    (table : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs) (source : Syntax.Block) (type : Core.Ty) :
    ((∃ core,ExpectedLambdaLetBodyElaborates RecursiveLocalComputationElaborates table owner inputs source core type) →
      ExpectedLambdaLetBodyHasType RecursiveLocalComputationHasType table owner inputs source type) ∧
    ((∃ core,elaborateExpectedLambdaLetBody? elaborateRecursiveLocalComputation? table owner inputs source=some (core,type)) →
      ExpectedLambdaLetBodyHasType RecursiveLocalComputationHasType table owner inputs source type) :=
  ⟨(expectedLambdaLetBodyHasType_iff_elaborates recursiveLocalComputationHasType_iff_elaborates).mpr,
    (expectedLambdaLetBodyHasType_iff_checked recursiveLocalComputationHasType_iff_elaborates elaborateRecursiveLocalComputation?_iff).mpr⟩
theorem function_alias_first_match_is_resolved_before_same_name_term_shadowing (p : Scenario) :
    StructuralTypeDenotes (types p) (named p "F") (fn p) ∧
      interpretStructuralType? (types p) (named p "F")=some (fn p) ∧
      (types p).lookup? ["F"]≠some .bool := by
  refine ⟨.named .head,(interpretStructuralType?_iff).mpr (.named .head),?_⟩
  simp [types,TypeNameTable.lookup?,fn]
theorem identical_fresh_numbers_belong_to_disjoint_parameter_and_outer_let_scopes (p : Scenario) :
    (lambdaInputs p).names=("x",nextId p)::(initial p).names ∧
      (tailInputs p 0).names=("f",nextId p)::(initial p).names ∧
      (lambdaInputs p).ids=(tailInputs p 0).ids ∧
      (lambdaInputs p).bindings.tail=(initial p).bindings ∧
      (tailInputs p 0).bindings.tail=(initial p).bindings ∧
      nextId p ∉ (initial p).ids :=
  ⟨rfl,rfl,rfl,rfl,rfl,Resolved.freshLocalId_not_mem p.owner (initial p).ids⟩
theorem initializer_f_is_the_old_row_but_the_tail_f_is_the_new_head (p : Scenario) :
    LocalNameTable.Lookup (lambdaInputs p).names "f" (oldId p) ∧
      Resolved.LocalScope.IndexOf (lambdaInputs p).context.ids (oldId p) 1 ∧
      LocalNameTable.Lookup (tailInputs p 0).names "f" (nextId p) ∧
      Resolved.LocalScope.IndexOf (tailInputs p 0).context.ids (nextId p) 0 ∧
      nextId p ≠ oldId p :=
  ⟨.tail (by change "x" ≠ "f"; decide) .head,.tail (freshNeOld p) .head,.head,.head,freshNeOld p⟩
theorem fresh_selection_ignores_an_arbitrarily_high_foreign_owner_row
    (p : Scenario) (foreign : Resolved.LocalId) (different : foreign.owner≠p.owner) :
    Resolved.freshLocalId p.owner (foreign::(initial p).ids)=nextId p :=
  Resolved.freshLocalId_cons_of_ne_owner p.owner (initial p).ids foreign different
theorem provenance_keeps_original_initializer_and_tail_scopes_separate
    (table : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs)
    (source : Syntax.Block) (core : Core.Expr) (type : Core.Ty)
    (e : ExpectedLambdaLetBodyElaborates RecursiveLocalComputationElaborates table owner inputs source core type) :
    ∃ name : Syntax.Identifier, ∃ declaredType initializer rest blockSpan initializerCore tailCore,
      ExpectedComputationLambdaElaborates RecursiveLocalComputationElaborates table owner inputs initializer initializerCore declaredType ∧
      ComputationReturnTreeElaborates RecursiveLocalComputationElaborates table owner
        (inputs.bindFresh owner name.value declaredType) ⟨blockSpan,rest⟩ tailCore type ∧
      core=.letE initializerCore tailCore ∧ (inputs.bindFresh owner name.value declaredType).bindings.tail=inputs.bindings := by
  obtain ⟨bs,_,name,_,init,rest,decl,ic,tc,_,_,initializer,tail,shape,_⟩ := e.provenance
  exact ⟨name,decl,init,rest,bs,ic,tc,initializer,tail,shape,rfl⟩
theorem omitting_the_outer_let_annotation_remains_outside_this_adapter (p : Scenario) :
    let inferred : Syntax.Block := ⟨p.span,⟨p.span,.letDecl ⟨p.span,"f"⟩ none (some (initializer p))⟩::tailStatements p p.depth⟩
    elaborateExpectedLambdaLetBody? elaborateRecursiveLocalComputation? (types p) p.owner (initial p) inferred=none ∧
      (¬∃ core type,ExpectedLambdaLetBodyElaborates RecursiveLocalComputationElaborates (types p) p.owner (initial p) inferred core type) ∧
      (¬∃ type,ExpectedLambdaLetBodyHasType RecursiveLocalComputationHasType (types p) p.owner (initial p) inferred type) := by
  dsimp only
  refine ⟨rfl,?_,?_⟩
  · exact (elaborateExpectedLambdaLetBody?_eq_none_iff elaborateRecursiveLocalComputation?_iff).mp rfl
  · rintro ⟨type,typed⟩; cases typed

end Tests.FrontendExpectedLambdaLetBody
end

section
-- leanmerge: from Solcore.Test.FrontendExpectedLambdaLetCoreProperties
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
end

section
-- leanmerge: from Solcore.Test.FrontendExpectedLambdaLetSpineBoundaryProperties
/-! Artificial exact children distinguish maximal source dispatch from semantic
fallback. Their deliberately mislabeled Core outputs carry no Core-typing claim. -/
set_option autoImplicit false
namespace Tests.ExpectedLambdaLetSpineBoundaries
open Solcore Solcore.Frontend
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"SpineBoundaries",by decide⟩],by decide⟩⟩,152⟩
private def span : Syntax.SourceSpan := ⟨⟨.main,"spine-boundaries.sol"⟩,0,91⟩
private def fn : Core.Ty := .function .word .word
private def higher : Core.Ty := .function fn fn
private def types : TypeNameTable := [(["F"],fn),(["H"],higher)]
private def annotation (name : String) : Syntax.TypeExpr :=
  ⟨span,.named ⟨span,⟨⟨⟨span,name⟩,[]⟩⟩⟩ none⟩
private def ref (name : String) : Syntax.Expr := ⟨span,.identifier ⟨span,name⟩⟩
private def returned : Syntax.Statement := ⟨span,.returnStmt (some (ref "g"))⟩
private def badLambda : Syntax.Expr := ⟨span,.lambda span ⟨span,[]⟩ none ⟨span,[⟨span,.returnStmt none⟩]⟩⟩
private def goodLambda : Syntax.Expr :=
  ⟨span,.lambda span ⟨span,[⟨span,.inferred ⟨span,"x"⟩⟩]⟩ none ⟨span,[⟨span,.returnStmt (some (ref "x"))⟩]⟩⟩
private def head (init : Syntax.Expr) : Syntax.Statement :=
  ⟨span,.letDecl ⟨span,"g"⟩ (some (annotation "F")) (some init)⟩
private def badBlock : Syntax.Block := ⟨span,[head badLambda,returned]⟩
private def groupedBlock : Syntax.Block := ⟨span,[head ⟨span,.group badLambda⟩,returned]⟩
private def ordinaryBlock : Syntax.Block := ⟨span,head (ref "unresolved") :: badBlock.value⟩
private def goodHead : Syntax.Statement :=
  ⟨span,.letDecl ⟨span,"f"⟩ (some (annotation "H")) (some goodLambda)⟩
private def previousAccepted : Syntax.Block := ⟨span,goodHead :: badBlock.value⟩

private inductive Artificial (_ : LocalNameTable) (_ : Resolved.Context) (_ : Syntax.Expr) : Core.Expr → Core.Ty → Prop where
  | invented : Artificial _ _ _ .unit fn
private inductive ArtificialTyped (_ : LocalNameTable) (_ : Resolved.Context) (_ : Syntax.Expr) : Core.Ty → Prop where
  | invented : ArtificialTyped _ _ _ fn
private def check (_ : LocalNameTable) (_ : Resolved.Context) (_ : Syntax.Expr) : Option (Core.Expr × Core.Ty) :=
  some (.unit,fn)
private theorem correct {table : LocalNameTable} {context : Resolved.Context} {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty} :
    check table context source=some (core,type) ↔ Artificial table context source core type := by
  constructor
  · intro accepted; cases Option.some.inj accepted; exact .invented
  · intro e; cases e; rfl
private theorem typing {table : LocalNameTable} {context : Resolved.Context} {source : Syntax.Expr} {type : Core.Ty} :
    ArtificialTyped table context source type ↔ ∃ core,Artificial table context source core type := by
  constructor
  · intro typed; cases typed; exact ⟨.unit,.invented⟩
  · rintro ⟨core,e⟩; cases e; exact .invented
private theorem oldTyped (i : LocalTypeInputs) (init : Syntax.Expr) :
    ComputationReturnTreeHasType ArtificialTyped types owner i ⟨span,[head init,returned]⟩ fn :=
  .binding (.named .head) .invented (.expression .invented)
private theorem oldElab (i : LocalTypeInputs) (init : Syntax.Expr) :
    ComputationReturnTreeElaborates Artificial types owner i ⟨span,[head init,returned]⟩ (.letE .unit .unit) fn :=
  .binding (.named .head) .invented (.expression .invented)
private theorem goodHeader :
    ExpectedUnaryLambdaHeaderDeclares types owner .empty goodLambda higher
      ⟨LocalTypeInputs.empty.bindFresh owner "x" fn,⟨span,[⟨span,.returnStmt (some (ref "x"))⟩]⟩,fn,fn⟩ :=
  .lambda .inferred .omitted
private theorem goodTyped :
    ExpectedComputationLambdaHasType ArtificialTyped types owner .empty goodLambda higher :=
  .lambda goodHeader (.function .word .word) (.function .word .word) (.expression .invented)
private theorem goodElab :
    ExpectedComputationLambdaElaborates Artificial types owner .empty goodLambda (.lambda fn fn .unit) higher :=
  .lambda goodHeader (.function .word .word) (.function .word .word) (.expression .invented)
private theorem higherMeaning : StructuralTypeDenotes types (annotation "H") higher :=
  .named (.tail (by change (["F"] : List String) ≠ ["H"]; decide) .head)

theorem an_exact_optional_child_does_not_supply_core_typing :
    (∀ {table context source core type},check table context source=some (core,type) ↔ Artificial table context source core type) ∧
    ¬(∀ {table context source core type},Artificial table context source core type → Core.HasType context.values core type) := by
  refine ⟨correct,?_⟩
  intro law
  have impossible := law (table:=[]) (context:=[]) (source:=ref "g") Artificial.invented
  cases impossible

theorem the_old_shared_profile_accepts_the_original_zero_parameter_lambda_head :
    ComputationReturnTreeHasType ArtificialTyped types owner .empty badBlock fn ∧
    ComputationReturnTreeElaborates Artificial types owner .empty badBlock (.letE .unit .unit) fn ∧
    elaborateComputationReturnTree? check types owner .empty badBlock=some (.letE .unit .unit,fn) := by
  exact ⟨oldTyped .empty _,oldElab .empty _,(elaborateComputationReturnTree?_iff correct).mpr (oldElab .empty _)⟩

theorem the_previous_one_head_adapter_accepts_an_original_tail_containing_a_second_lambda :
    ExpectedLambdaLetBodyHasType ArtificialTyped types owner .empty previousAccepted fn ∧
    ExpectedLambdaLetBodyElaborates Artificial types owner .empty previousAccepted
      (.letE (.lambda fn fn .unit) (.letE .unit .unit)) fn ∧
    elaborateExpectedLambdaLetBody? check types owner .empty previousAccepted=
      some (.letE (.lambda fn fn .unit) (.letE .unit .unit),fn) := by
  have sourceTyping : ExpectedLambdaLetBodyHasType ArtificialTyped types owner .empty previousAccepted fn :=
    .binding higherMeaning goodTyped (oldTyped _ _)
  have e : ExpectedLambdaLetBodyElaborates Artificial types owner .empty previousAccepted
      (.letE (.lambda fn fn .unit) (.letE .unit .unit)) fn := .binding higherMeaning goodElab (oldElab _ _)
  exact ⟨sourceTyping,e,(elaborateExpectedLambdaLetBody?_iff correct).mpr e⟩

private theorem badRejected (i : LocalTypeInputs) :
    elaborateExpectedLambdaLetSpine? check types owner i badBlock=none := by
  unfold elaborateExpectedLambdaLetSpine?
  have gate : isExpectedLambdaLetHead badBlock=true := rfl
  rw [gate]
  simp only [reduceCtorEq,ite_false,badBlock,head]
  have declared : interpretStructuralType? types (annotation "F")=some fn :=
    (interpretStructuralType?_iff).mpr (.named .head)
  rw [declared]
  have noHeader : declareExpectedUnaryLambdaHeader? types owner i badLambda fn=none := rfl
  simp only [bind,Option.bind_some,elaborateExpectedComputationLambda?,noHeader,Option.bind_none]

theorem true_original_head_failure_never_falls_back_to_the_old_shared_success :
    isExpectedLambdaLetHead badBlock=true ∧
    elaborateComputationReturnTree? check types owner .empty badBlock=some (.letE .unit .unit,fn) ∧
    elaborateExpectedLambdaLetSpine? check types owner .empty badBlock=none ∧
    (¬∃ core type,ExpectedLambdaLetSpineElaborates Artificial types owner .empty badBlock core type) ∧
    (¬∃ type,ExpectedLambdaLetSpineHasType ArtificialTyped types owner .empty badBlock type) := by
  have noElab := (elaborateExpectedLambdaLetSpine?_eq_none_iff correct).mp (badRejected .empty)
  refine ⟨rfl,(elaborateComputationReturnTree?_iff correct).mpr (oldElab .empty _),badRejected .empty,noElab,?_⟩
  rintro ⟨type,typed⟩
  obtain ⟨core,e⟩ := (expectedLambdaLetSpineHasType_iff_elaborates typing).mp typed
  exact noElab ⟨core,type,e⟩

theorem a_grouped_lambda_is_an_unchanged_terminal_for_the_same_artificial_child :
    isExpectedLambdaLetHead groupedBlock=false ∧
    ExpectedLambdaLetSpineHasType ArtificialTyped types owner .empty groupedBlock fn ∧
    elaborateExpectedLambdaLetSpine? check types owner .empty groupedBlock=some (.letE .unit .unit,fn) :=
  ⟨rfl,.terminal rfl (oldTyped .empty _),
    (elaborateExpectedLambdaLetSpine?_iff correct).mpr (.terminal rfl (oldElab .empty _))⟩

theorem an_ordinary_head_delegates_the_whole_tail_without_restarting_expected_dispatch :
    isExpectedLambdaLetHead ordinaryBlock=false ∧ isExpectedLambdaLetHead badBlock=true ∧
    ExpectedLambdaLetSpineHasType ArtificialTyped types owner .empty ordinaryBlock fn ∧
    elaborateExpectedLambdaLetSpine? check types owner .empty ordinaryBlock=some (.letE .unit (.letE .unit .unit),fn) :=
  ⟨rfl,rfl,.terminal rfl (.binding (.named .head) .invented (oldTyped _ _)),
    (elaborateExpectedLambdaLetSpine?_iff correct).mpr
      (.terminal rfl (.binding (.named .head) .invented (oldElab _ _)))⟩

theorem previous_one_head_acceptance_does_not_embed_without_a_terminal_tail_boundary :
    ExpectedLambdaLetBodyHasType ArtificialTyped types owner .empty previousAccepted fn ∧
    elaborateExpectedLambdaLetBody? check types owner .empty previousAccepted=
      some (.letE (.lambda fn fn .unit) (.letE .unit .unit),fn) ∧
    elaborateExpectedLambdaLetSpine? check types owner .empty previousAccepted=none ∧
    (¬∃ core type,ExpectedLambdaLetSpineElaborates Artificial types owner .empty previousAccepted core type) := by
  have rejected : elaborateExpectedLambdaLetSpine? check types owner .empty previousAccepted=none := by
    unfold elaborateExpectedLambdaLetSpine?
    have gate : isExpectedLambdaLetHead previousAccepted=true := rfl
    rw [gate]
    simp only [reduceCtorEq,ite_false,previousAccepted,goodHead]
    rw [(interpretStructuralType?_iff).mpr higherMeaning]
    simp only [bind,Option.bind_some,(elaborateExpectedComputationLambda?_iff correct).mpr goodElab]
    have absent : elaborateExpectedLambdaLetSpine? check types owner
        (LocalTypeInputs.empty.bindFresh owner "f" higher) ⟨span,badBlock.value⟩=none := badRejected _
    rw [absent]
    rfl
  exact ⟨the_previous_one_head_adapter_accepts_an_original_tail_containing_a_second_lambda.1,
    the_previous_one_head_adapter_accepts_an_original_tail_containing_a_second_lambda.2.2,rejected,
    (elaborateExpectedLambdaLetSpine?_eq_none_iff correct).mp rejected⟩

end Tests.ExpectedLambdaLetSpineBoundaries
end

section
-- leanmerge: from Solcore.Test.FrontendExpectedLambdaLetSpineProperties
/-! Source-only typing is constructed before literal Core or checker evidence.
Each repeated f initializer sees the preceding f, never itself. Runtime paths
below concern only generated Core and keep every actual capture; no source evaluation is asserted. -/
set_option autoImplicit false
namespace Tests.FrontendExpectedLambdaLetSpine
open Solcore Solcore.Frontend
private structure Scenario where
  span : Syntax.SourceSpan
  owner : Resolved.DeclarationId
  outer : LocalTypeInputs
  a : Core.Ty
  b : Core.Ty
  domain : Core.Ty.WellFormed [] a
  codomain : Core.Ty.WellFormed [] b
private def fn (p : Scenario) : Core.Ty := .function p.a p.b
private def types (p : Scenario) : TypeNameTable := [(["F"],fn p),(["F"],.bool)]
private def annotation (p : Scenario) : Syntax.TypeExpr :=
  ⟨p.span,.named ⟨p.span,⟨⟨⟨p.span,"F"⟩,[]⟩⟩⟩ none⟩
private def ref (p : Scenario) (name : String) : Syntax.Expr := ⟨p.span,.identifier ⟨p.span,name⟩⟩
private def lambdaBody (p : Scenario) : Syntax.Block :=
  ⟨p.span,[⟨p.span,.returnStmt (some ⟨p.span,.call (ref p "f") ⟨p.span,[ref p "x"]⟩⟩)⟩]⟩
private def initializer (p : Scenario) : Syntax.Expr :=
  ⟨p.span,.lambda p.span ⟨p.span,[⟨p.span,.inferred ⟨p.span,"x"⟩⟩]⟩ none (lambdaBody p)⟩
private def rows (p : Scenario) : Nat → LocalTypeInputs
  | 0 => p.outer.bindFresh p.owner "f" (fn p)
  | n+1 => (rows p n).bindFresh p.owner "f" (fn p)
private def visible (p : Scenario) : Nat → Resolved.LocalId
  | 0 => Resolved.freshLocalId p.owner p.outer.ids
  | n+1 => Resolved.freshLocalId p.owner (rows p n).ids
private def ordinary (p : Scenario) : Nat → List Syntax.Statement
  | 0 => [⟨p.span,.returnStmt (some (ref p "f"))⟩]
  | m+1 => ⟨p.span,.letDecl ⟨p.span,"f"⟩ (some (annotation p)) (some (ref p "f"))⟩::
      ⟨p.span,.letDecl ⟨p.span,"f"⟩ none (some (ref p "f"))⟩::ordinary p m
private def statements (p : Scenario) : Nat → Nat → List Syntax.Statement
  | 0,m => ordinary p m
  | n+1,m => ⟨p.span,.letDecl ⟨p.span,"f"⟩ (some (annotation p)) (some (initializer p))⟩::statements p n m
private def source (p : Scenario) (n m : Nat) : Syntax.Block := ⟨p.span,statements p n m⟩
private theorem rowFacts (p : Scenario) (j : Nat) :
    LocalNameTable.Lookup (rows p j).names "f" (visible p j) ∧
    Resolved.LocalScope.Lookup (rows p j).context (visible p j) (fn p) ∧
    Resolved.LocalScope.IndexOf (rows p j).context.ids (visible p j) 0 := by
  cases j <;> exact ⟨.head,.head,.head⟩
private theorem different (p : Scenario) (j : Nat) :
    Resolved.freshLocalId p.owner (rows p j).ids ≠ visible p j := by
  cases j <;> exact Resolved.freshLocalId_cons_fresh_ne _ _
private theorem header (p : Scenario) (j : Nat) :
    ExpectedUnaryLambdaHeaderDeclares (types p) p.owner (rows p j) (initializer p) (fn p)
      ⟨(rows p j).bindFresh p.owner "x" p.a,lambdaBody p,p.a,p.b⟩ := .lambda .inferred .omitted
private theorem lambdaTyped (p : Scenario) (j : Nat) :
    ExpectedComputationLambdaHasType RecursiveLocalComputationHasType (types p) p.owner
      (rows p j) (initializer p) (fn p) :=
  .lambda (header p j) p.domain p.codomain (.expression (.application
    (.pure (.identifier (.tail (by change "x" ≠ "f"; decide) (rowFacts p j).1)
      (.tail (different p j) (rowFacts p j).2.1))) (.pure (.identifier .head .head))))
private theorem ordinaryTyped (p : Scenario) (m j : Nat) :
    RecursiveComputationReturnTreeHasType (types p) p.owner (rows p j) ⟨p.span,ordinary p m⟩ (fn p) := by
  induction m generalizing j with
  | zero => exact .expression (.pure (.identifier (rowFacts p j).1 (rowFacts p j).2.1))
  | succ m ih =>
      exact .binding (.named .head) (.pure (.identifier (rowFacts p j).1 (rowFacts p j).2.1))
        (.inferred (.pure (.identifier .head .head)) (ih (j+2)))
private theorem terminalFalse (p : Scenario) (m : Nat) : isExpectedLambdaLetHead (source p 0 m)=false := by
  cases m <;> rfl
private theorem original (p : Scenario) (n m j : Nat) :
    ExpectedLambdaLetSpineHasType RecursiveLocalComputationHasType (types p) p.owner (rows p j) (source p n m) (fn p) := by
  induction n generalizing j with
  | zero => exact .terminal (terminalFalse p m) (ordinaryTyped p m j)
  | succ n ih => exact .binding rfl (.named .head) (lambdaTyped p j) (ih (j+1))

theorem arbitrary_consecutive_heads_and_ordinary_tail_have_original_source_typing (p : Scenario) (n m : Nat) :
    ExpectedLambdaLetSpineHasType RecursiveLocalComputationHasType (types p) p.owner (rows p 0) (source p n m) (fn p) :=
  original p n m 0
theorem both_existence_laws_consume_source_typing_without_actual_inhabitants (p : Scenario) (n m : Nat) :
    (∃ core,ExpectedLambdaLetSpineElaborates RecursiveLocalComputationElaborates (types p) p.owner (rows p 0) (source p n m) core (fn p)) ∧
    (∃ core,elaborateExpectedLambdaLetSpine? elaborateRecursiveLocalComputation? (types p) p.owner (rows p 0) (source p n m)=some (core,fn p)) :=
  ⟨(expectedLambdaLetSpineHasType_iff_elaborates recursiveLocalComputationHasType_iff_elaborates).mp (original p n m 0),
    (expectedLambdaLetSpineHasType_iff_checked recursiveLocalComputationHasType_iff_elaborates elaborateRecursiveLocalComputation?_iff).mp (original p n m 0)⟩
theorem zero_heads_delegate_the_complete_ordinary_tail (p : Scenario) (m : Nat) :
    isExpectedLambdaLetHead (source p 0 m)=false ∧
    elaborateExpectedLambdaLetSpine? elaborateRecursiveLocalComputation? (types p) p.owner (rows p 0) (source p 0 m)=
      elaborateComputationReturnTree? elaborateRecursiveLocalComputation? (types p) p.owner (rows p 0) (source p 0 m) := by
  exact ⟨terminalFalse p m,by unfold elaborateExpectedLambdaLetSpine?; simp only [terminalFalse p m,ite_true]⟩

private def bodyCore : Core.Expr := .apply (.var 1) (.var 0)
private def ordinaryCore : Nat → Core.Expr
  | 0 => .var 0
  | m+1 => .letE (.var 0) (.letE (.var 0) (ordinaryCore m))
private def literalCore (a b : Core.Ty) : Nat → Nat → Core.Expr
  | 0,m => ordinaryCore m
  | n+1,m => .letE (.lambda a b bodyCore) (literalCore a b n m)
private theorem lambdaElab (p : Scenario) (j : Nat) :
    ExpectedComputationLambdaElaborates RecursiveLocalComputationElaborates (types p) p.owner
      (rows p j) (initializer p) (.lambda p.a p.b bodyCore) (fn p) :=
  .lambda (header p j) p.domain p.codomain (.expression (.application
    (.pure (.identifier (.tail (by change "x" ≠ "f"; decide) (rowFacts p j).1))
      (.var (.tail (different p j) (rowFacts p j).2.2)) (.var (.tail (different p j) (rowFacts p j).2.1)))
    (.pure (.identifier .head) (.var .head) (.var .head))))
private theorem ordinaryElab (p : Scenario) (m j : Nat) :
    RecursiveComputationReturnTreeElaborates (types p) p.owner (rows p j) ⟨p.span,ordinary p m⟩ (ordinaryCore m) (fn p) := by
  induction m generalizing j with
  | zero => exact .expression (.pure (.identifier (rowFacts p j).1) (.var (rowFacts p j).2.2) (.var (rowFacts p j).2.1))
  | succ m ih =>
      exact .binding (.named .head)
        (.pure (.identifier (rowFacts p j).1) (.var (rowFacts p j).2.2) (.var (rowFacts p j).2.1))
        (.inferred (.pure (.identifier .head) (.var .head) (.var .head)) (ih (j+2)))
private theorem literalElab (p : Scenario) (n m j : Nat) :
    ExpectedLambdaLetSpineElaborates RecursiveLocalComputationElaborates (types p) p.owner (rows p j)
      (source p n m) (literalCore p.a p.b n m) (fn p) := by
  induction n generalizing j with
  | zero => exact .terminal (terminalFalse p m) (ordinaryElab p m j)
  | succ n ih => exact .binding rfl (.named .head) (lambdaElab p j) (ih (j+1))

theorem literal_nested_core_is_independent_of_the_checker (p : Scenario) (n m : Nat) :
    ExpectedLambdaLetSpineElaborates RecursiveLocalComputationElaborates (types p) p.owner (rows p 0)
      (source p n m) (literalCore p.a p.b n m) (fn p) ∧
    Core.HasType (rows p 0).context.values (literalCore p.a p.b n m) (fn p) ∧
    elaborateExpectedLambdaLetSpine? elaborateRecursiveLocalComputation? (types p) p.owner (rows p 0)
      (source p n m)=some (literalCore p.a p.b n m,fn p) :=
  ⟨literalElab p n m 0,(literalElab p n m 0).core_hasType RecursiveLocalComputationElaborates.core_hasType,
    (elaborateExpectedLambdaLetSpine?_iff elaborateRecursiveLocalComputation?_iff).mpr (literalElab p n m 0)⟩
theorem each_lambda_looks_up_the_previous_f_while_the_next_tail_gets_the_new_f (p : Scenario) (j : Nat) :
    LocalNameTable.Lookup ((rows p j).bindFresh p.owner "x" p.a).names "f" (visible p j) ∧
    Resolved.LocalScope.IndexOf ((rows p j).bindFresh p.owner "x" p.a).context.ids (visible p j) 1 ∧
    LocalNameTable.Lookup (rows p (j+1)).names "f" (visible p (j+1)) ∧ visible p (j+1)≠visible p j :=
  ⟨.tail (by change "x" ≠ "f"; decide) (rowFacts p j).1,
    .tail (different p j) (rowFacts p j).2.2,.head,different p j⟩
theorem separate_scopes_reuse_the_fresh_number_without_leaking_parameter_rows (p : Scenario) (j : Nat) :
    ((rows p j).bindFresh p.owner "x" p.a).ids=(rows p (j+1)).ids ∧
    ((rows p j).bindFresh p.owner "x" p.a).names=("x",visible p (j+1))::(rows p j).names ∧
    (rows p (j+1)).names=("f",visible p (j+1))::(rows p j).names ∧
    (rows p (j+1)).bindings.tail=(rows p j).bindings ∧ visible p (j+1)∉(rows p j).ids :=
  ⟨rfl,rfl,rfl,rfl,Resolved.freshLocalId_not_mem _ _⟩
theorem owner_filtered_fresh_growth_and_alias_first_match (p : Scenario) (j : Nat)
    (foreign : Resolved.LocalId) (differentOwner : foreign.owner≠p.owner) :
    Resolved.freshLocalId p.owner (foreign::(rows p j).ids)=visible p (j+1) ∧
    (visible p (j+2)).binderIndex=(visible p (j+1)).binderIndex+1 ∧
    StructuralTypeDenotes (types p) (annotation p) (fn p) ∧ (types p).lookup? ["F"]=some (fn p) :=
  ⟨Resolved.freshLocalId_cons_of_ne_owner _ _ _ differentOwner,
    Resolved.freshLocalId_cons_fresh_binderIndex _ _,.named .head,rfl⟩
theorem one_layer_provenance_preserves_the_entire_recursive_tail (p : Scenario) (n m : Nat) :
    ∃ blockSpan letSpan name annotation initializer rest declaredType initCore tailCore,
      source p (n+1) m=⟨blockSpan,⟨letSpan,.letDecl name (some annotation) (some initializer)⟩::rest⟩ ∧
      ExpectedComputationLambdaElaborates RecursiveLocalComputationElaborates (types p) p.owner
        (rows p 0) initializer initCore declaredType ∧
      ExpectedLambdaLetSpineElaborates RecursiveLocalComputationElaborates (types p) p.owner
        ((rows p 0).bindFresh p.owner name.value declaredType) ⟨blockSpan,rest⟩ tailCore (fn p) ∧
      literalCore p.a p.b (n+1) m=.letE initCore tailCore := by
  rcases (literalElab p (n+1) m 0).provenance with ⟨impossible,_⟩ | head
  · cases impossible
  · obtain ⟨bs,ls,name,ann,init,rest,decl,ic,tc,_,shape,_,initializer,tail,coreShape,_⟩ := head
    exact ⟨bs,ls,name,ann,init,rest,decl,ic,tc,shape,initializer,tail,coreShape⟩

theorem old_one_head_evidence_embeds_when_its_original_tail_is_terminal
    (ChildElab : LocalNameTable → Resolved.Context → Syntax.Expr → Core.Expr → Core.Ty → Prop)
    (table : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs)
    (source : Syntax.Block) (core : Core.Expr) (type : Core.Ty)
    (old : ExpectedLambdaLetBodyElaborates ChildElab table owner inputs source core type)
    (tailFalse : isExpectedLambdaLetHead ⟨source.span,source.value.tail⟩=false) :
    ExpectedLambdaLetSpineElaborates ChildElab table owner inputs source core type := by
  cases old with
  | binding meaning initializer tail =>
      refine .binding ?_ meaning initializer (.terminal tailFalse tail)
      cases initializer with
      | lambda header _ _ _ => cases header; rfl

private def wrap (a b : Core.Ty) (environment : Core.Environment) : Core.Value := .closure a b bodyCore environment
private def capturedResult (a b : Core.Ty) : Nat → Core.Value → Core.Environment → Core.Value
  | 0,value,_ => value
  | n+1,value,suffix => capturedResult a b n (wrap a b (value::suffix)) (value::suffix)
private theorem capturePath (a b : Core.Ty) (n : Nat) (value : Core.Value)
    (suffix : Core.Environment) (store : Core.Store) (k : List Core.Frame) :
    Core.Steps (3*n+1) ⟨.eval (literalCore a b n 0) (value::suffix),k,store⟩
      ⟨.ret (capturedResult a b n value suffix),k,store⟩ := by
  induction n generalizing value suffix with
  | zero => exact .cons (.var rfl) .refl
  | succ n ih =>
      have count : 3*(n+1)+1=1+(3*n+1)+2 := by omega
      rw [count]
      exact CostStepComposition.letE (.cons .lambda .refl) (ih _ _)

theorem generated_core_captures_all_actual_rows_without_running_any_initializer_body
    (a b : Core.Ty) (n : Nat) (value : Core.Value) (suffix : Core.Environment)
    (store : Core.Store) (k : List Core.Frame) :
    Core.Steps (3*n+1) ⟨.eval (literalCore a b n 0) (value::suffix),k,store⟩
      ⟨.ret (capturedResult a b n value suffix),k,store⟩ := capturePath a b n value suffix store k
theorem actual_saved_core_checkpoints_resume_the_same_nested_capture_chain
    (a b : Core.Ty) (n spent : Nat) (value : Core.Value) (suffix : Core.Environment)
    (store : Core.Store) (cp : Core.State)
    (exhausted : Core.runStateful spent (.initial (literalCore a b n 0) (value::suffix) store)=.outOfFuel cp) :
    spent<3*n+1 ∧ Core.Steps (3*n+1-spent) cp (.final (capturedResult a b n value suffix) store) ∧
    ∀ extra,Core.runStateful extra cp=Core.runStateful (spent+extra) (.initial (literalCore a b n 0) (value::suffix) store) := by
  have path := capturePath a b n value suffix store []
  exact ⟨(path.residual_of_outOfFuel exhausted).1,(path.residual_of_outOfFuel exhausted).2,Core.runStateful_resume exhausted⟩

end Tests.FrontendExpectedLambdaLetSpine
end

section
-- leanmerge: from Solcore.Test.FrontendExpectedLambdaTypingBoundaryProperties
/-! Source typing precedes Core existence. Artificial child models distinguish
existence from determinism and show why each correspondence premise matters.
The concrete identity has multiple supplied expected types, not inferred unique type. -/
set_option autoImplicit false
namespace Tests.ExpectedLambdaTypingBoundaries
open Solcore Solcore.Frontend
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"ExpectedLambdaTyping",by decide⟩],by decide⟩⟩,150⟩
private def span : Syntax.SourceSpan := ⟨⟨.main,"expected-lambda-typing.sol"⟩,0,29⟩
private def ref : Syntax.Expr := ⟨span,.identifier ⟨span,"x"⟩⟩
private def body : Syntax.Block := ⟨span,[⟨span,.returnStmt (some ref)⟩]⟩
private def original : Syntax.Expr := ⟨span,.lambda span ⟨span,[⟨span,.inferred ⟨span,"x"⟩⟩]⟩ none body⟩
private def inner (a : Core.Ty) : LocalTypeInputs := LocalTypeInputs.empty.bindFresh owner "x" a
private def header (a b : Core.Ty) : DeclaredUnaryLambdaHeader := ⟨inner a,body,a,b⟩
private theorem declares (a b : Core.Ty) :
    ExpectedUnaryLambdaHeaderDeclares [] owner .empty original (.function a b) (header a b) :=
  .lambda .inferred .omitted
private theorem identityTyped (a : Core.Ty) (formed : Core.Ty.WellFormed [] a) :
    ExpectedComputationLambdaHasType RecursiveLocalComputationHasType [] owner .empty original (.function a a) :=
  .lambda (declares a a) formed formed (.expression (.pure (.identifier .head .head)))

theorem one_original_inferred_identity_supports_distinct_supplied_expected_types :
    ExpectedComputationLambdaHasType RecursiveLocalComputationHasType [] owner .empty original (.function .word .word) ∧
    ExpectedComputationLambdaHasType RecursiveLocalComputationHasType [] owner .empty original (.function .bool .bool) ∧
    (Core.Ty.function .word .word ≠ .function .bool .bool) ∧
    (∃ core, elaborateExpectedComputationLambda? elaborateRecursiveLocalComputation? [] owner .empty original (.function .word .word)=some core) ∧
    (∃ core, elaborateExpectedComputationLambda? elaborateRecursiveLocalComputation? [] owner .empty original (.function .bool .bool)=some core) :=
  ⟨identityTyped .word .word,identityTyped .bool .bool,by decide,
    (expectedComputationLambdaHasType_iff_checked recursiveLocalComputationHasType_iff_elaborates
      elaborateRecursiveLocalComputation?_iff).mp (identityTyped .word .word),
    (expectedComputationLambdaHasType_iff_checked recursiveLocalComputationHasType_iff_elaborates
      elaborateRecursiveLocalComputation?_iff).mp (identityTyped .bool .bool)⟩

private inductive BitTyped (_ : LocalNameTable) (_ : Resolved.Context) (_ : Syntax.Expr) : Core.Ty → Prop where
  | bit : BitTyped _ _ _ .bool
private inductive EitherBit (_ : LocalNameTable) (_ : Resolved.Context) (_ : Syntax.Expr) : Core.Expr → Core.Ty → Prop where
  | left : EitherBit _ _ _ (.bool false) .bool
  | right : EitherBit _ _ _ (.bool true) .bool
private theorem bitTyping {table : LocalNameTable} {context : Resolved.Context} {src : Syntax.Expr} {type : Core.Ty} :
    BitTyped table context src type ↔ ∃ core, EitherBit table context src core type := by
  constructor
  · intro typed; cases typed; exact ⟨_,.left⟩
  · rintro ⟨core,evidence⟩; cases evidence <;> exact .bit
private theorem sourceBit :
    ExpectedComputationLambdaHasType BitTyped [] owner .empty original (.function .word .bool) :=
  .lambda (declares .word .bool) .word .bool (.expression .bit)

theorem source_typing_existence_does_not_require_a_deterministic_child :
    ExpectedComputationLambdaHasType BitTyped [] owner .empty original (.function .word .bool) ∧
    (∃ core, ExpectedComputationLambdaElaborates EitherBit [] owner .empty original core (.function .word .bool)) ∧
    ExpectedComputationLambdaElaborates EitherBit [] owner .empty original (.lambda .word .bool (.bool false)) (.function .word .bool) ∧
    ExpectedComputationLambdaElaborates EitherBit [] owner .empty original (.lambda .word .bool (.bool true)) (.function .word .bool) ∧
    (Core.Expr.lambda .word .bool (.bool false) ≠ .lambda .word .bool (.bool true)) :=
  ⟨sourceBit,(expectedComputationLambdaHasType_iff_elaborates bitTyping).mp sourceBit,
    .lambda (declares _ _) .word .bool (.expression .left),
    .lambda (declares _ _) .word .bool (.expression .right),by decide⟩

theorem this_nondeterministic_model_has_no_exact_optional_child_checker :
    ¬ ∃ checkChild : LocalNameTable → Resolved.Context → Syntax.Expr → Option (Core.Expr × Core.Ty),
      ∀ {table context src core type}, checkChild table context src=some (core,type) ↔ EitherBit table context src core type := by
  rintro ⟨checkChild,correct⟩
  have left := (correct (table:=[]) (context:=[]) (src:=ref)).mpr EitherBit.left
  have right := (correct (table:=[]) (context:=[]) (src:=ref)).mpr EitherBit.right
  cases Option.some.inj (left.symm.trans right)

private def reject (_ : LocalNameTable) (_ : Resolved.Context) (_ : Syntax.Expr) : Option (Core.Expr × Core.Ty) := none
theorem independent_source_typing_does_not_supply_checker_correspondence :
    ExpectedComputationLambdaHasType BitTyped [] owner .empty original (.function .word .bool) ∧
    (∃ core, ExpectedComputationLambdaElaborates EitherBit [] owner .empty original core (.function .word .bool)) ∧
    elaborateExpectedComputationLambda? reject [] owner .empty original (.function .word .bool)=none := by
  refine ⟨sourceBit,(expectedComputationLambdaHasType_iff_elaborates bitTyping).mp sourceBit,?_⟩
  simp only [elaborateExpectedComputationLambda?,declareExpectedUnaryLambdaHeader?_iff.mpr (declares .word .bool),
    bind,Option.bind_some]
  simp [header,Core.Ty.isWellFormed,body,elaborateComputationReturnTree?,reject]

private def EmptyTyping (_ : LocalNameTable) (_ : Resolved.Context) (_ : Syntax.Expr) (_ : Core.Ty) : Prop := False
private theorem noEmptyTyping :
    ¬ ExpectedComputationLambdaHasType EmptyTyping [] owner .empty original (.function .word .word) := by
  intro typed
  cases typed with
  | lambda hd _ _ bodyTyped =>
      have same := hd.result_unique (declares .word .word)
      cases same
      cases bodyTyped with | expression child => exact child
private theorem identityElab :
    ExpectedComputationLambdaElaborates RecursiveLocalComputationElaborates [] owner .empty original
      (.lambda .word .word (.var 0)) (.function .word .word) :=
  .lambda (declares _ _) .word .word (.expression (.pure (.identifier .head) (.var .head) (.var .head)))

theorem successful_checking_does_not_reflect_an_unrelated_child_typing_relation :
    elaborateExpectedComputationLambda? elaborateRecursiveLocalComputation? [] owner .empty original
      (.function .word .word)=some (.lambda .word .word (.var 0)) ∧
    (¬ ExpectedComputationLambdaHasType EmptyTyping [] owner .empty original (.function .word .word)) ∧
    ¬ (∀ {table context src type}, EmptyTyping table context src type ↔
      ∃ core, RecursiveLocalComputationElaborates table context src core type) := by
  refine ⟨(elaborateExpectedComputationLambda?_iff elaborateRecursiveLocalComputation?_iff).mpr identityElab,noEmptyTyping,?_⟩
  intro wrongBridge
  exact noEmptyTyping ((expectedComputationLambdaHasType_iff_elaborates wrongBridge).mpr ⟨_,identityElab⟩)
end Tests.ExpectedLambdaTypingBoundaries
end

section
-- leanmerge: from Solcore.Test.FrontendParsedExpectedComputationLambdas
/-! Original header/body certificates precede the new standalone checker.
Creation and application are only existing Core consumers, not source evaluation.
Their arbitrary actual captures need not realize the static input types. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedExpectedComputationLambdas
private def check (p : Bool) (label : String) : IO Unit := do unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"ExpectedComputationLambdas",by decide⟩],by decide⟩⟩,147⟩
private def id (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def foreign : Resolved.LocalId := ⟨{owner with declarationIndex:=900},700⟩
private def outer : LocalTypeInputs := ⟨[⟨"x",id 7,.bool⟩,⟨"saved",id 31,.word⟩,
  ⟨"f",foreign,.function .word .word⟩,⟨"g",id 20,.function .word .word⟩],by decide⟩
private def types : TypeNameTable := [(["A"],.word),(["B"],.bool),(["A"],.bool),
  (["C"],.cell (.function .word .word))]
private def file (text : String) : Syntax.SourceFile := ⟨⟨.main,"expected-computation-lambdas.sol"⟩,text⟩
private def parsed (text : String) (diagnostics : Nat := 0) : IO Syntax.Expr := do
  let .ok lexed := Syntax.Lexer.lex (file text) | throw (IO.userError "lexer invariant")
  match Syntax.Parser.expression (Syntax.Parser.State.initial (file text) lexed) with
  | .ok source next =>
      check (lexed.diagnostics.isEmpty && next.atEnd && decide (next.diagnostics.length=diagnostics ∧
        source.span=⟨(file text).id,0,text.utf8ByteSize⟩)) "full original source, ranges and explicit diagnostics"
      return source
  | .reject _ _ => throw (IO.userError "original lambda rejected")
  | .invariant _ => throw (IO.userError "parser invariant")
private structure Meaning (source : Syntax.TypeExpr) where
  type : Core.Ty
  evidence : StructuralTypeDenotes types source type
private def meaning (source : Syntax.TypeExpr) : IO (Meaning source) := do
  match shape : source with
  | ⟨_,.named name none⟩ => match found : types.lookup? (qualifiedTypeNameKey name) with
      | some t => return ⟨t,by rw [shape]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩
      | none => throw (IO.userError "annotation lookup")
  | ⟨_,.tuple []⟩ => return ⟨.unit,by rw [shape]; exact .unit⟩
  | ⟨_,.tuple [child]⟩ => let a ← meaning child; return ⟨a.type,by rw [shape]; exact .single a.evidence⟩
  | ⟨_,.tuple [left,right]⟩ =>
      let a ← meaning left; let b ← meaning right
      return ⟨.product a.type b.type,by rw [shape]; exact .pair a.evidence b.evidence⟩
  | ⟨_,.function _ ⟨_,[a]⟩ (some ⟨span,results⟩)⟩ =>
      let p ← meaning a; let r ← meaning ⟨span,.tuple results⟩
      return ⟨.function p.type r.type,by rw [shape]; exact .functionReturns p.evidence r.evidence⟩
  | _ => throw (IO.userError "independent annotation shape")
termination_by sizeOf source
private def wellFormed : (t : Core.Ty) → Option (PLift (Core.Ty.WellFormed [] t))
  | .unit => some ⟨.unit⟩ | .bool => some ⟨.bool⟩ | .word => some ⟨.word⟩ | .integer => some ⟨.integer⟩
  | .product a b => do let p ← wellFormed a; let r ← wellFormed b; return ⟨.product p.down r.down⟩
  | .function a b => do let p ← wellFormed a; let r ← wellFormed b; return ⟨.function p.down r.down⟩
  | .sum a b => do let p ← wellFormed a; let r ← wellFormed b; return ⟨.sum p.down r.down⟩
  | .cell a => do let p ← wellFormed a; return ⟨.cell p.down⟩
  | .namedData _ => none
private structure Header (source : Syntax.Expr) (a b : Core.Ty) where
  name : String
  body : Syntax.Block
  evidence : ExpectedUnaryLambdaHeaderDeclares types owner outer source (.function a b)
    ⟨outer.bindFresh owner name a,body,a,b⟩
private def header (source : Syntax.Expr) (a b : Core.Ty) : IO (Header source a b) := do
  match shape : source with
  | ⟨span,.lambda keyword ⟨ps,[p]⟩ returns body⟩ =>
      check (span.contains keyword && span.contains ps && ps.contains p.span && span.contains body.span &&
        decide (keyword.endByte≤ps.startByte ∧ ps.endByte≤body.span.startByte)) "original keyword, single parameter and body"
      let ⟨name,evidence⟩ : Σ name, PLift (ExpectedLambdaParameterDeclares types owner outer p a (outer.bindFresh owner name a)) ←
        match parameterShape : p with
        | ⟨_,.inferred name⟩ => pure ⟨name.value,⟨by rw [parameterShape]; exact .inferred⟩⟩
        | ⟨_,.typed none name ann⟩ => do
            let m ← meaning ann
            if same : m.type=a then pure ⟨name.value,⟨by rw [parameterShape]; exact .typed (same ▸ m.evidence)⟩⟩
            else throw (IO.userError "independent parameter mismatch")
        | _ => throw (IO.userError "original parameter profile")
      match present : returns with
      | none => return ⟨name,body,by rw [shape,present]; exact .lambda evidence.down .omitted⟩
      | some ann =>
          let m ← meaning ann
          if same : m.type=b then return ⟨name,body,by rw [shape,present]; exact .lambda evidence.down (.annotated (same ▸ m.evidence))⟩
          else throw (IO.userError "independent return mismatch")
  | _ => throw (IO.userError "original unary header")
private structure Child (inputs : LocalTypeInputs) (source : Syntax.Expr) where
  core : Core.Expr
  type : Core.Ty
  evidence : RecursiveLocalComputationElaborates inputs.names inputs.context source core type
private def child (inputs : LocalTypeInputs) (source : Syntax.Expr) : IO (Child inputs source) := do
  match shape : source with
  | ⟨_,.identifier name⟩ => match named : inputs.names.lookup? name.value with
      | some i => match typed : inputs.context.lookup? i, position : Resolved.LocalScope.index? inputs.context.ids i with
          | some t,some n => return ⟨.var n,t,by
              rw [shape]
              exact .pure (.identifier (LocalNameTable.lookup?_iff.mp named))
                (.var (Resolved.LocalScope.index?_iff.mp position)) (.var (Resolved.LocalScope.lookup?_iff.mp typed))⟩
          | _,_ => throw (IO.userError "original typed row")
      | none => throw (IO.userError "original name")
  | ⟨_,.call fn ⟨_,[arg]⟩⟩ =>
      let f ← child inputs fn; let a ← child inputs arg
      match ft : f.type with
      | .function p r =>
          if same : a.type=p then return ⟨.apply f.core a.core,r,by rw [shape]; exact .application (ft ▸ f.evidence) (same ▸ a.evidence)⟩
          else throw (IO.userError "child argument type")
      | _ => throw (IO.userError "child callee type")
  | _ => throw (IO.userError "independent child profile")
termination_by sizeOf source
private structure Body (inputs : LocalTypeInputs) (source : Syntax.Block) where
  core : Core.Expr
  type : Core.Ty
  evidence : ComputationReturnTreeElaborates RecursiveLocalComputationElaborates types owner inputs source core type
private def body (inputs : LocalTypeInputs) (source : Syntax.Block) : IO (Body inputs source) := do
  match shape : source with
  | ⟨_,[⟨_,.returnStmt none⟩]⟩ => return ⟨.unit,.unit,by rw [shape]; exact .bare⟩
  | ⟨_,[⟨_,.returnStmt (some expr)⟩]⟩ =>
      let c ← child inputs expr; return ⟨c.core,c.type,by rw [shape]; exact .expression c.evidence⟩
  | ⟨span,⟨_,.letDecl name ann (some expr)⟩::rest⟩ =>
      let c ← child inputs expr
      let tail ← body (inputs.bindFresh owner name.value c.type) ⟨span,rest⟩
      match present : ann with
      | none => return ⟨.letE c.core tail.core,tail.type,by rw [shape,present]; exact .inferred c.evidence tail.evidence⟩
      | some sourceType =>
          let m ← meaning sourceType
          if same : m.type=c.type then return ⟨.letE c.core tail.core,tail.type,by rw [shape,present]; exact .binding (same ▸ m.evidence) c.evidence tail.evidence⟩
          else throw (IO.userError "original typed shadow")
  | ⟨span,⟨_,.expression expr true⟩::rest⟩ =>
      let c ← child inputs expr; let tail ← body inputs ⟨span,rest⟩
      return ⟨.letE c.core (tail.core.weakenAt 0),tail.type,by rw [shape]; exact .discard c.evidence tail.evidence⟩
  | _ => throw (IO.userError "independent body profile")
termination_by sizeOf source
private def accepted (text : String) (a b : Core.Ty) (literalBody : Core.Expr) (diagnostics : Nat := 0) : IO Unit := do
  let source ← parsed text diagnostics
  let h ← header source a b
  let inner := outer.bindFresh owner h.name a
  let original ← body inner h.body
  let some pa := wellFormed a | throw (IO.userError "domain WF")
  let some rb := wellFormed b | throw (IO.userError "codomain WF")
  if fixed : original.core=literalBody ∧ original.type=b then
    have independent : ExpectedComputationLambdaElaborates RecursiveLocalComputationElaborates types owner outer source (.lambda a b literalBody) (.function a b) :=
      .lambda h.evidence pa.down rb.down (by simpa only [fixed.1,fixed.2] using original.evidence)
    have typed := independent.core_hasType RecursiveLocalComputationElaborates.core_hasType
    have provenance := independent.provenance
    have complete := (elaborateExpectedComputationLambda?_iff elaborateRecursiveLocalComputation?_iff).mpr independent
    have restored := (elaborateExpectedComputationLambda?_iff elaborateRecursiveLocalComputation?_iff).mp complete
    have _ := typed; have _ := provenance; have _ := restored
    check (decide (elaborateExpectedComputationLambda? elaborateRecursiveLocalComputation? types owner outer source (.function a b)=some (.lambda a b literalBody) ∧
      inner.names=(h.name,id 32)::outer.names ∧ inner.context=(id 32,a)::outer.context)) "literal lambda, unchanged outer rows and fresh inner input"
    check (elaborateRecursiveLocalComputation? outer.names outer.context source).isNone "old recursive checker still excludes the original lambda"
  else throw (IO.userError "independent original body versus fixed expected Core/type")
private def rejectedBody (text : String) (a b : Core.Ty) (diagnostics : Nat := 0) : IO Unit := do
  let source ← parsed text diagnostics; let h ← header source a b
  have _ := declareExpectedUnaryLambdaHeader?_iff.mpr h.evidence
  if rejected : elaborateExpectedComputationLambda? elaborateRecursiveLocalComputation? types owner outer source (.function a b)=none then
    have _ := (elaborateExpectedComputationLambda?_eq_none_iff elaborateRecursiveLocalComputation?_iff).mp rejected
    check (declareExpectedUnaryLambdaHeader? types owner outer source (.function a b)).isSome "header is accepted but body is not"
  else throw (IO.userError "unsupported or mismatched body admitted")
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def allocator : Core.Value := .closure .word .word (.letE (.newCell .word (.var 0)) (.var 1)) [.bool false]
private def writer (l : Nat) : Core.Value := .closure .word .word (.letE (.storeCell (.var 1) (.var 0)) (.loadCell (.var 2))) [.cellRef .word l]
private def literalBody : Core.Expr := .letE (.apply (.var 3) (.var 0)) (.letE (.apply (.var 5) (.var 0)) (.var 4))
private def lambda : Core.Expr := .lambda .word .word literalBody
private theorem creation (a b : Core.Ty) (e : Core.Expr) (env : Core.Environment) (s : Core.Store) (k : List Core.Frame) :
    Core.Steps 1 ⟨.eval (.lambda a b e) env,k,s⟩ ⟨.ret (.closure a b e env),k,s⟩ := .cons .lambda .refl
private structure Path (e : Core.Expr) (env : Core.Environment) (s : Core.Store) where
  value : Core.Value
  final : Core.Store
  cost : Nat
  evidence : ∀ k, Core.Steps cost ⟨.eval e env,k,s⟩ ⟨.ret value,k,final⟩
private def path : (depth : Nat) → (e : Core.Expr) → (env : Core.Environment) → (s : Core.Store) → IO (Path e env s)
  | 0,_,_,_ => throw (IO.userError "manual depth")
  | n+1,e,env,s => do
    match shape : e with
    | .var i => match found : env[i]? with | some v => return ⟨v,s,1,fun _ => by rw [shape]; exact .cons (.var found) .refl⟩ | none => throw (IO.userError "manual row")
    | .word v => return ⟨.word v,s,1,fun _ => by rw [shape]; exact .cons .word .refl⟩
    | .lambda a b inner => return ⟨.closure a b inner env,s,1,fun _ => by rw [shape]; exact creation a b inner env s _⟩
    | .letE a b => let l ← path n a env s; let r ← path n b (l.value::env) l.final; return ⟨r.value,r.final,l.cost+r.cost+2,fun _ => by rw [shape]; exact CostStepComposition.letE (l.evidence _) (r.evidence _)⟩
    | .apply f a =>
        let fn ← path n f env s; let arg ← path n a env fn.final
        match fv : fn.value with
        | .closure _ _ inner captured => let r ← path n inner (arg.value::captured) arg.final; return ⟨r.value,r.final,fn.cost+arg.cost+r.cost+3,fun _ => by rw [shape]; exact CostStepComposition.apply (fv ▸ fn.evidence _) (arg.evidence _) (r.evidence [])⟩
        | _ => throw (IO.userError "manual callable")
    | .newCell .word (.var i) => match found : env[i]? with | some v => return ⟨.cellRef .word s.length,s++[v],3,fun _ => by rw [shape]; exact .cons .enterNewCell (.cons (.var found) (.cons .applyNewCell .refl))⟩ | none => throw (IO.userError "allocation row")
    | .loadCell (.var i) => match ref : env[i]? with
      | some (.cellRef _ l) => match found : s.read? l with
        | some v => return ⟨v,s,3,fun _ => by rw [shape]; exact .cons .enterLoadCell (.cons (.var ref) (.cons (.applyLoadCell found) .refl))⟩ | none => throw (IO.userError "read location")
      | _ => throw (IO.userError "read reference")
    | .storeCell (.var i) (.var j) => match ref : env[i]?, val : env[j]? with
      | some (.cellRef _ l),some v => match found : s.read? l, written : s.write? l v with
        | some _,some final => return ⟨.unit,final,5,fun _ => by rw [shape]; exact .cons .enterStoreCell (.cons (.var ref) (.cons (.beginStoreCellValue found) (.cons (.var val) (.cons (.applyStoreCell written) .refl))))⟩
        | _,_ => throw (IO.userError "write location")
      | _,_ => throw (IO.userError "write reference")
    | _ => throw (IO.userError "manual Core shape")
private def coreEffects (saved : Core.Value) (location : Nat) (expected : Core.Store) : IO Unit := do
  let env := [.bool true,saved,allocator,writer location,.closure .unit .unit (.var 99) [.cellRef .word 700]]
  let store := [w 99]
  let closed := Core.Value.closure .word .word literalBody env
  have made := creation .word .word literalBody env store []
  check (decide (Core.runStateful 0 (Core.State.initial lambda env store)=.outOfFuel (Core.State.initial lambda env store) ∧
    Core.runStateful 1 (Core.State.initial lambda env store)=.done closed store)) "Core creation captures all actual values, even unused invalid captures, without effects"
  have _ := made
  let originalPath ← path 40 literalBody (w 14::env) store
  let application := Core.Expr.apply lambda (.word (Core.Word.ofNatModulo 14))
  let applied ← path 50 application env store
  if fixed : originalPath.cost=31 ∧ applied.cost=36 ∧ originalPath.value=saved ∧ applied.value=saved ∧ originalPath.final=expected ∧ applied.final=expected then
    have exactPath (k) : Core.Steps 36 ⟨.eval application env,k,store⟩ ⟨.ret saved,k,expected⟩ := by simpa only [fixed.2.1,fixed.2.2.2.1,fixed.2.2.2.2.2] using applied.evidence k
    have allFuel (fuel : Nat) := (exactPath []).runStateful_done_iff (fuel:=fuel)
    for fuel in List.range 38 do
      let observed := Core.runStateful fuel (Core.State.initial application env store)
      if fuel<36 then
        match exhausted : Core.runStateful fuel (Core.State.initial application env store) with
        | .outOfFuel cp =>
            for more in [0,1,36] do check (decide (Core.runStateful more cp=Core.runStateful (fuel+more) (Core.State.initial application env store))) "genuine Core checkpoint resumes exactly"
            have _ := Core.runStateful_resume exhausted 36
        | _ => throw (IO.userError "early Core completion or fault")
      else check (decide (observed=.done saved expected)) "existing Core application alone performs allocation/write"
    have _ := allFuel
  else throw (IO.userError "fixed Core effects/cost independent of the source checker")
private def wholeRejected : IO Unit := do
  let text := "function wrap(f:function(A) returns(A),g:function(A) returns(A),saved:A) returns(function(A) returns(A)){return lam(x:A)->A{let x:A=f(x);g(x);return saved;};}"
  let .ok lexed := Syntax.Lexer.lex (file text) | throw (IO.userError "whole lexer")
  match Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial (file text) lexed) with
  | .ok declaration next =>
      check (next.atEnd && lexed.diagnostics.isEmpty && next.diagnostics.isEmpty &&
        decide (declaration.span=⟨(file text).id,0,text.utf8ByteSize⟩)) "original full function"
      let identity : TypedRuntimeArgument :=
        ⟨.function .word .word,.closure .word .word (.var 0) [],.closure .nil (.var rfl)⟩
      let arguments : List TypedRuntimeArgument := [identity,identity,⟨.word,w 41,.word⟩]
      check (decide (interpretRuntimeFunctionHeader? types declaration.value.signature=some (.function .word .word)) &&
        (declareRuntimeParameters? types owner declaration.value.signature.parameters.elements).isSome &&
        (bindRuntimeParameters? types owner declaration.value.signature.parameters.elements arguments).isSome)
        "original named header and all three actual arguments are accepted before the lambda boundary"
      check (compileComputationFunction? elaborateRecursiveLocalComputation? types owner declaration).isNone "old whole function still rejects source lambda"
      check (prepareComputationFunction? elaborateRecursiveLocalComputation? types owner declaration arguments).isNone "no named-function admission was added"
      for fuel in [0,1,100] do
        check (runComputationFunction? elaborateRecursiveLocalComputation? types owner declaration arguments fuel []).isNone "old runner still rejects the original lambda"
  | .reject _ _ => throw (IO.userError "whole parser rejected")
  | .invariant _ => throw (IO.userError "whole parser invariant")
end ParsedExpectedComputationLambdas
open ParsedExpectedComputationLambdas
def frontendParsedExpectedComputationLambdaTests : IO Unit := do
  for text in ["lam(x){return x;}","lam(x:A)->A{return x;}","lam(x,)->A{return x;}"] do accepted text .word .word (.var 0)
  accepted "lam(x:A)->A{return saved;}" .word .word (.var 2)
  accepted "lam(x:A)->A{let x:A=f(x); g(x); return saved;}" .word .word literalBody
  accepted "lam(x){let x=f(x); g(x); return saved;}" .word .word literalBody
  accepted "lam(x:(A,B))->(A,B){return x;}" (.product .word .bool) (.product .word .bool) (.var 0)
  accepted "lam(x:function(A) returns(B))->function(A) returns(B){return x;}" (.function .word .bool) (.function .word .bool) (.var 0)
  accepted "lam(x:C)->A{return saved;}" (.cell (.function .word .word)) .word (.var 2)
  accepted "lam(x:A)->(){return;}" .word .unit .unit
  accepted "lam(comptime){return comptime;}" .word .word (.var 0) 1
  for text in ["lam(x){return x;}","lam(x:A)->B{return x;}","lam(x){return;}","lam(x){return Missing;}",
      "lam(x){let x:B=saved;return x;}","lam(x){return lam(y){return y;};}"] do rejectedBody text .word .bool
  rejectedBody "lam(x){let ;}" .word .word 1
  for saved in [w 41,.bool false] do
    coreEffects saved 0 [w 14,w 14]
    coreEffects saved 1 [w 99,w 14]
  wholeRejected
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedExpectedDataLambdaApplications
/- Original whole-written certificates precede search. The actual grouped call
uses invocation; no direct-call AST or source/Core closure equality is invented. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace Tests.ParsedExpectedDataLambdaApplications
open Solcore Solcore.Frontend
private def check (b : Bool) (s : String) : IO Unit := unless b do throw (IO.userError s)
private def proof {p : Prop} (_ : p) : IO Unit := pure ()
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"ExpectedApplications",by decide⟩],by decide⟩⟩,175⟩
private def sid (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def foreign (n : Nat) : Resolved.LocalId := ⟨{owner with declarationIndex:=901},n⟩
private def inputs : LocalTypeInputs := ⟨[⟨"x",sid 7,.bool⟩,⟨"saved",sid 31,.unit⟩,⟨"c",sid 11,.bool⟩,
  ⟨"d",sid 20,.bool⟩,⟨"arg",sid 9,.unit⟩,⟨"other",foreign 700,.unit⟩,⟨"x",foreign 701,.word⟩],by decide⟩
private def types : TypeNameTable := [(["Unit"],.unit),(["Word"],.word)]
private def up (e : Resolved.Environment) := e.map (fun r => (r.1,RuntimeValue.ofCore r.2))
private def env (a o q : Core.Value) (c d : Bool) : Resolved.Environment :=
  [(sid 7,.bool false),(sid 31,q),(sid 11,.bool c),(sid 20,.bool d),(sid 9,a),(foreign 700,o),(foreign 701,.word (Core.Word.ofNatModulo 99))]
private abbrev Child (n : LocalNameTable) (t : Resolved.Context) (s : Syntax.Expr) (c : Core.Expr) (v : Core.Ty) :=
  ∃ r, ResolvesLocalExpression n s r ∧ Resolved.Lowers t.ids r c ∧ Resolved.HasType t r v
private structure EC (t : LocalTypeInputs) (e : Resolved.Environment) (s : Core.Store) (src : Syntax.Expr) where
  core : Core.Expr
  type : Core.Ty
  value : Core.Value
  cost : Nat
  gate : ClosedSourceDataExpression src
  elaboration : Child t.names t.context src core type
  old : LocalExpressionEvaluatesWithCost t.names e s src value s cost
  closed : ClosedSourceExpressionEvaluates owner t.names (up e) (s.map RuntimeValue.ofCore) src (RuntimeValue.ofCore value) (s.map RuntimeValue.ofCore)
private theorem mapped {e : Resolved.Environment} {i : Resolved.LocalId} {v : Core.Value}
    (h : Resolved.LocalScope.Lookup e i v) : Resolved.LocalScope.Lookup (up e) i (RuntimeValue.ofCore v) := by
  induction h with | head => exact .head | tail different _ ih => exact .tail different ih
private theorem path {t e s src} (h : EC t e s src) (same : e.ids=t.context.ids) (k : List Core.Frame) :
    Core.Steps h.cost ⟨.eval h.core e.values,k,s⟩ ⟨.ret h.value,k,s⟩ := by
  obtain ⟨r,res,low,_⟩ := h.elaboration
  exact h.old.toStepsWithContinuation res (same ▸ low) k
private def expr (t : LocalTypeInputs) (e : Resolved.Environment) (s : Core.Store) (src : Syntax.Expr) : IO (EC t e s src) := do
  match shape : src with
  | ⟨_,.identifier name⟩ =>
    match named : t.names.lookup? name.value with
    | some i => match typed : t.context.lookup? i, found : e.lookup? i, indexed : Resolved.LocalScope.index? t.context.ids i with
      | some ty,some v,some n => return ⟨.var n,ty,v,1,by rw [shape]; exact .reference,
          by rw [shape]; exact ⟨.var i,.identifier (LocalNameTable.lookup?_iff.mp named),.var (Resolved.LocalScope.index?_iff.mp indexed),.var (Resolved.LocalScope.lookup?_iff.mp typed)⟩,
          by rw [shape]; exact .identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found),
          by rw [shape]; exact .reference (LocalNameTable.lookup?_iff.mp named) (mapped (Resolved.LocalScope.lookup?_iff.mp found))⟩
      | _,_,_ => throw (IO.userError "independent original reference row")
    | none => throw (IO.userError "independent original name")
  | ⟨span,.group child⟩ =>
    check (span.startByte+1==child.span.startByte && child.span.endByte+1==span.endByte) "original group margins"
    let h ← expr t e s child
    return ⟨h.core,h.type,h.value,h.cost,by rw [shape]; exact .group h.gate,
      by obtain ⟨r,a,b,c⟩ := h.elaboration; rw [shape]; exact ⟨r,.group a,b,c⟩,
      by rw [shape]; exact .group h.old,by rw [shape]; exact .group h.closed⟩
  | ⟨span,.tuple ⟨ts,[left,right]⟩⟩ =>
    check (span==ts && span.contains left.span && span.contains right.span && left.span.endByte<right.span.startByte) "original pair ranges"
    let l ← expr t e s left; let r ← expr t e s right
    return ⟨.pair l.core r.core,.product l.type r.type,.pair l.value r.value,l.cost+r.cost+3,
      by rw [shape]; exact .pair l.gate r.gate,
      by obtain ⟨a,ar,al,alt⟩ := l.elaboration; obtain ⟨b,br,bl,bt⟩ := r.elaboration; rw [shape]; exact ⟨.pair a b,.pair ar br,.pair al bl,.pair alt bt⟩,
      by rw [shape]; exact .pair l.old r.old,by rw [shape]; simpa only [RuntimeValue.ofCore] using ClosedSourceExpressionEvaluates.pair l.closed r.closed⟩
  | ⟨span,.conditional guard qm yes colon no⟩ =>
    check (span.contains guard.span && span.contains yes.span && span.contains no.span && qm.endByte==qm.startByte+1 && colon.endByte==colon.startByte+1 && guard.span.endByte==qm.startByte && qm.endByte==yes.span.startByte && yes.span.endByte==colon.startByte && colon.endByte==no.span.startByte) "original conditional children and markers"
    let g ← expr t e s guard; let a ← expr t e s yes; let b ← expr t e s no
    if typed : g.type=.bool ∧ a.type=b.type then
      match value : g.value with
      | .bool c => return ⟨.ifE g.core a.core b.core,a.type,if c then a.value else b.value,g.cost+(if c then a.cost else b.cost)+2,
          by rw [shape]; exact .conditional g.gate a.gate b.gate,
          by obtain ⟨r,rr,rl,rt⟩ := g.elaboration; obtain ⟨u,ur,ul,ut⟩ := a.elaboration; obtain ⟨v,vr,vl,vt⟩ := b.elaboration
             rw [shape]; exact ⟨.ifE r u v,.conditional rr ur vr,.ifE rl ul vl,.ifE (typed.1 ▸ rt) ut (typed.2 ▸ vt)⟩,
          by rw [shape]; cases c <;> first | exact .ifTrue (value ▸ g.old) a.old | exact .ifFalse (value ▸ g.old) b.old,
          by rw [shape]; cases c <;> first | exact .conditionalTrue (by simpa only [value,RuntimeValue.ofCore] using g.closed) a.closed | exact .conditionalFalse (by simpa only [value,RuntimeValue.ofCore] using g.closed) b.closed⟩
      | _ => throw (IO.userError "original Bool guard payload")
    else throw (IO.userError "independent original conditional types")
  | _ => throw (IO.userError "bounded original certificate profile")
termination_by sizeOf src
private structure Meaning (src : Syntax.TypeExpr) where
  type : Core.Ty
  evidence : StructuralTypeDenotes types src type
private def meaning (src : Syntax.TypeExpr) : IO (Meaning src) := do
  match shape : src with
  | ⟨_,.named name none⟩ => match found : types.lookup? (qualifiedTypeNameKey name) with
    | some ty => return ⟨ty,by rw [shape]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩
    | none => throw (IO.userError "original annotation meaning")
  | ⟨_,.tuple [a,b]⟩ => let l ← meaning a; let r ← meaning b; return ⟨.product l.type r.type,by rw [shape]; exact .pair l.evidence r.evidence⟩
  | _ => throw (IO.userError "original annotation profile")
termination_by sizeOf src
private structure BC (t : LocalTypeInputs) (e : Resolved.Environment) (s : Core.Store) (src : Syntax.Block) where
  core : Core.Expr
  value : Core.Value
  cost : Nat
  gate : ClosedSourceDataBody src
  elaboration : ComputationReturnTreeElaborates Child types owner t src core (.product .unit .unit)
  old : ComputationReturnTreeEvaluatesWithCost LocalExpressionEvaluatesWithCost owner t.names e s src value s cost
  closed : ClosedSourceBodyEvaluates owner t.names (up e) (s.map RuntimeValue.ofCore) src (RuntimeValue.ofCore value) (s.map RuntimeValue.ofCore)
  path : ∀ k, Core.Steps cost ⟨.eval core e.values,k,s⟩ ⟨.ret value,k,s⟩
private def body (t : LocalTypeInputs) (e : Resolved.Environment) (s : Core.Store) (src : Syntax.Block) (same : e.ids=t.context.ids) : IO (BC t e s src) := do
  match shape : src with
  | ⟨bs,[⟨ls,.letDecl name (some ann) (some init)⟩,⟨rs,.returnStmt (some result)⟩]⟩ =>
    let h ← expr t e s init; let m ← meaning ann
    if typed : m.type=.unit ∧ h.type=.unit then
      let t1 := t.bindFresh owner name.value .unit
      let e1 : Resolved.Environment := (Resolved.freshLocalId owner t.ids,h.value)::e
      have same1 : e1.ids=t1.context.ids := by simpa only [e1,t1,LocalTypeInputs.bindFresh_context,Resolved.LocalScope.ids,List.map_cons] using congrArg (List.cons _) same
      let r ← expr t1 e1 s result
      if rt : r.type=.product .unit .unit then
        return ⟨.letE h.core r.core,r.value,h.cost+r.cost+2,by rw [shape]; exact .binding h.gate (.expression r.gate),
          by rw [shape]; exact .binding (typed.1 ▸ m.evidence) (typed.2 ▸ h.elaboration) (.expression (rt ▸ r.elaboration)),
          by rw [shape]; apply ComputationReturnTreeEvaluatesWithCost.binding h.old
             simpa only [e1,t1,LocalTypeInputs.bindFresh_names,LocalTypeInputs.names_ids] using ComputationReturnTreeEvaluatesWithCost.expression (blockSpan:=bs) (returnSpan:=rs) (owner:=owner) r.old,
          by rw [shape]; apply ClosedSourceBodyEvaluates.binding h.closed
             simpa only [e1,t1,LocalTypeInputs.bindFresh_names,LocalTypeInputs.names_ids,up,List.map_cons] using ClosedSourceBodyEvaluates.expression (blockSpan:=bs) (returnSpan:=rs) r.closed,
          fun k => CostStepComposition.letE (path h same _) (by simpa only [e1,Resolved.LocalScope.values,List.map_cons] using path r same1 k)⟩
      else throw (IO.userError "independent pair result type")
    else throw (IO.userError "independent Unit local shadow")
  | _ => throw (IO.userError "original typed shadow and conditional return")
private structure Header (src : Syntax.Expr) where
  name : Syntax.Identifier
  body : Syntax.Block
  shape : SourceUnaryLambdaShape src name body
  declaration : ExpectedUnaryLambdaHeaderDeclares types owner inputs src (.function .unit (.product .unit .unit))
    ⟨inputs.bindFresh owner name.value .unit,body,.unit,.product .unit .unit⟩
private def header (src : Syntax.Expr) : IO (Header src) := do
  match shape : src with
  | ⟨span,.lambda keyword ⟨pspan,[p]⟩ returns b⟩ =>
    check (span.contains keyword && span.contains pspan && pspan.contains p.span && span.contains b.span && returns.toList.all (fun a => span.contains a.span) && b.value.all (fun st => b.span.contains st.span)) "original lambda/header/body ranges"
    let ⟨n,param,raw⟩ : Σ n, PLift (ExpectedLambdaParameterDeclares types owner inputs p .unit (inputs.bindFresh owner n.value .unit)) × PLift (SourceUnaryLambdaShape src n b) ←
      match ps : p with
      | ⟨_,.inferred n⟩ => pure ⟨n,⟨by rw [ps]; exact .inferred⟩,⟨by rw [shape,ps]; exact .inferred⟩⟩
      | ⟨_,.typed none n ann⟩ => do
        let m ← meaning ann
        if h : m.type=.unit then pure ⟨n,⟨by rw [ps]; exact .typed (h ▸ m.evidence)⟩,⟨by rw [shape,ps]; exact .typed⟩⟩
        else throw (IO.userError "original parameter Unit")
      | _ => throw (IO.userError "original unmarked unary parameter")
    match present : returns with
    | none => return ⟨n,b,raw.down,by rw [shape,present]; exact .lambda param.down .omitted⟩
    | some ann =>
      let m ← meaning ann
      if h : m.type=.product .unit .unit then return ⟨n,b,raw.down,by rw [shape,present]; exact .lambda param.down (.annotated (h ▸ m.evidence))⟩
      else throw (IO.userError "original expected pair annotation")
  | _ => throw (IO.userError "original direct lambda child")
private def parsed (text : String) : IO Syntax.Expr := do
  let f : Syntax.SourceFile := ⟨⟨.main,"expected-data-applications.sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex f | throw (IO.userError "lexer")
  match Syntax.Parser.expression (Syntax.Parser.State.initial f lexed) with
  | .ok src next =>
    check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && src.span==Syntax.SourceSpan.fullFile f) "original source, complete EOF and diagnostics"
    return src
  | _ => throw (IO.userError "original expression parser")
private def mainText := "(lam(x:Unit)->(Unit,Unit){let x:Unit=(x);return c?(x,saved):(saved,x);})(d?arg:other)"
private def inferredText := "(lam(x){let x:Unit=(x);return c?(x,saved):(saved,x);})(d?arg:other)"
private def literalBody : Core.Expr := .letE (.var 0) (.ifE (.var 4) (.pair (.var 0) (.var 3)) (.pair (.var 3) (.var 0)))
private def exercise (text : String) (a o q : Core.Value) (c d : Bool) (s : Core.Store) : IO Unit := do
  let src ← parsed text; let e := env a o q c d
  match original : src with
  | ⟨cs,.call ⟨gs,.group fs⟩ ⟨args,[arg]⟩⟩ =>
    let h ← header fs; let ac ← expr inputs e s arg
    let inner := inputs.bindFresh owner h.name.value .unit
    let ie : Resolved.Environment := (Resolved.freshLocalId owner inputs.ids,ac.value)::e
    have same : e.ids=inputs.context.ids := rfl
    have same1 : ie.ids=inner.context.ids := by simpa only [ie,inner,LocalTypeInputs.bindFresh_context,Resolved.LocalScope.ids,List.map_cons] using congrArg (List.cons _) same
    let bc ← body inner ie s h.body same1
    have originalExpected : ExpectedComputationLambdaElaborates Child types owner inputs fs (.lambda .unit (.product .unit .unit) bc.core) (.function .unit (.product .unit .unit)) :=
      .lambda h.declaration .unit (.product .unit .unit) bc.elaboration
    have callee : ClosedSourceExpressionEvaluates owner inputs.names (up e) (s.map RuntimeValue.ofCore) ⟨gs,.group fs⟩ (.sourceClosure fs owner inputs.names (up e)) (s.map RuntimeValue.ofCore) := .group (.creation h.shape)
    have closed : ClosedSourceExpressionEvaluates owner inputs.names (up e) (s.map RuntimeValue.ofCore) src (RuntimeValue.ofCore bc.value) (s.map RuntimeValue.ofCore) := by
      rw [original]; apply ClosedSourceExpressionEvaluates.call h.shape callee ac.closed
      simpa only [ie,inner,LocalTypeInputs.bindFresh_names,LocalTypeInputs.names_ids,up,List.map_cons] using bc.closed
    have beta (k) : Core.Steps bc.cost ⟨.eval bc.core (ac.value::e.values),k,s⟩ ⟨.ret bc.value,k,s⟩ := by simpa only [ie,Resolved.LocalScope.values,List.map_cons] using bc.path k
    let core := Core.Expr.apply (.lambda .unit (.product .unit .unit) bc.core) ac.core
    have full (k) : Core.Steps (1+ac.cost+bc.cost+3) ⟨.eval core e.values,k,s⟩ ⟨.ret bc.value,k,s⟩ := CostStepComposition.apply (.cons .lambda .refl) (path ac same _) (beta [])
    proof closed; proof (Core.steps_from_initial_sound (full [])); proof originalExpected
    check (decide (bc.core=literalBody ∧ ac.core=.ifE (.var 3) (.var 4) (.var 5) ∧ ac.cost=4 ∧ bc.cost=11 ∧ h.name.value="x" ∧ Resolved.freshLocalId owner inputs.ids=sid 32 ∧ Resolved.freshLocalId owner inner.ids=sid 33)) "independent literal Core/cost and fresh shadow rows"
    check (decide (ac.value=(if d then a else o) ∧ bc.value=(if c then .pair ac.value q else .pair q ac.value))) "independent full opaque argument and pair endpoint"
    check (cs.startByte==0 && gs.startByte==0 && fs.span.startByte==1 && fs.span.endByte+1==gs.endByte && args.startByte==gs.endByte && args.endByte==cs.endByte) "actual grouped callee retained in whole original call"
    have independentChecked := (elaborateExpectedComputationLambda?_iff elaborateLocalExpression?_iff).mpr originalExpected
    proof independentChecked
    check (decide (elaborateExpectedComputationLambda? elaborateLocalExpression? types owner inputs fs (.function .unit (.product .unit .unit))=some (.lambda .unit (.product .unit .unit) bc.core))) "actual expected checker agrees with independent original"
    check (elaborateComputationReturnTree? elaborateLocalExpression? types owner inner h.body==some (bc.core,.product .unit .unit)) "actual original shared body checker"
    check ((elaborateExpectedComputationLambda? elaborateLocalExpression? types owner inputs ⟨gs,.group fs⟩ (.function .unit (.product .unit .unit))).isNone && (elaborateLocalExpression? inputs.names inputs.context src).isNone) "grouped callee and whole call are not old checked expressions"
    check (decide (evaluateLocalExpressionWithCost? inputs.names e arg=some (ac.value,ac.cost))) "actual old argument value/cost"
    match resolved : resolveLocalExpression? inputs.names arg with
    | some r => check (r.lower? e.ids==some ac.core) "actual original argument resolution and lowering"; proof (resolveLocalExpression?_sound resolved)
    | none => throw (IO.userError "actual original argument resolution")
    for depth in [0,1,2,3,4,5,6,9] do
      match run : evaluateClosedSourceExpression? depth owner inputs.names (up e) (s.map RuntimeValue.ofCore) src with
      | none => check (depth<6) "actual original depth below 6"
      | some (mv,ms) => proof ((evaluateClosedSourceExpression?_sound run).deterministic closed); check (depth≥6) "actual depth 6, separate Core cost 19"
    match made : evaluateClosedSourceExpression? 2 owner inputs.names (up e) (s.map RuntimeValue.ofCore) ⟨gs,.group fs⟩ with
    | none => throw (IO.userError "actual grouped creation depth 2")
    | some (actualFn,calleeStore) =>
      have fnEq := (evaluateClosedSourceExpression?_sound made).deterministic callee
      match argRun : evaluateClosedSourceExpression? 2 owner inputs.names (up e) calleeStore arg with
      | none => throw (IO.userError "actual argument after actual callee store")
      | some (actualArg,argumentStore) =>
        have argEq := (evaluateClosedSourceExpression?_sound (fnEq.2 ▸ argRun)).deterministic ac.closed
        have fnEval : ClosedSourceExpressionEvaluates owner inputs.names (up e) (s.map RuntimeValue.ofCore) ⟨gs,.group fs⟩ (.sourceClosure fs owner inputs.names (up e)) calleeStore := by simpa only [fnEq.1] using evaluateClosedSourceExpression?_sound made
        have argEval : ClosedSourceExpressionEvaluates owner inputs.names (up e) calleeStore arg (RuntimeValue.ofCore ac.value) (s.map RuntimeValue.ofCore) := by simpa only [argEq.1,argEq.2] using evaluateClosedSourceExpression?_sound argRun
        have image {v st} := closedSourceExpectedDataLambda_invocation_core_iff h.shape bc.gate independentChecked same fnEval argEval (callSpan:=cs) (argumentsSpan:=args) (actualValue:=v) (actualFinal:=st)
        match actualRun : evaluateClosedSourceExpression? 6 owner inputs.names (up e) (s.map RuntimeValue.ofCore) src, coreRun : Core.runStateful 19 (.initial core e.values s) with
        | some (mv,ms),.done cv final =>
          have actual := evaluateClosedSourceExpression?_sound actualRun
          have actualCore := Core.runStateful_evaluation_sound coreRun
          have forward := (image (v:=mv) (st:=ms)).mp (by simpa only [original] using actual)
          have equal : mv=RuntimeValue.ofCore cv ∧ ms=final.map RuntimeValue.ofCore := by
            obtain ⟨v,st,hv,hs,ev⟩ := forward
            have both := Core.evaluation_deterministic (Core.Evaluates.apply (parameterType:=.unit) (resultType:=.product .unit .unit) Core.Evaluates.lambda (Core.steps_from_initial_sound (path ac same [])) ev) actualCore
            simpa only [both.1,both.2] using And.intro hv hs
          have actualBeta : Core.Evaluates (ac.value::e.values) s bc.core cv final := by
            change Core.Evaluates e.values s (.apply (.lambda .unit (.product .unit .unit) bc.core) ac.core) cv final at actualCore
            cases actualCore with
            | apply f a b =>
              cases f
              obtain ⟨ha,hs⟩ := Core.evaluation_deterministic a (Core.steps_from_initial_sound (path ac same []))
              cases ha; cases hs; exact b
          proof ((image (v:=mv) (st:=ms)).mpr ⟨cv,final,equal.1,equal.2,actualBeta⟩)
          proof ((image (v:=RuntimeValue.ofCore cv) (st:=final.map RuntimeValue.ofCore)).mpr ⟨cv,final,rfl,rfl,actualBeta⟩); proof equal
          check (mv.toCore?==some cv && (ms.mapM RuntimeValue.toCore?)==some final) "actual full mixed value/store projected only after both directions"
        | _,_ => throw (IO.userError "actual whole closed/Core completion")
    match bodyRun : evaluateClosedSourceBody? 5 owner inner.names (up ie) (s.map RuntimeValue.ofCore) h.body with
    | some (_,_) => proof ((evaluateClosedSourceBody?_sound bodyRun).deterministic bc.closed)
    | none => throw (IO.userError "actual body depth 5")
    for fuel in [0,1,18,19,23] do
      match run : Core.runStateful fuel (.initial core e.values s) with
      | .done v final => check (decide (fuel≥19 ∧ v=bc.value ∧ final=s)) "actual Core full endpoint and cost"; proof (Core.runStateful_evaluation_sound run)
      | .outOfFuel _ => check (fuel<19) "actual Core cost 19"
      | .fault _ _ => throw (IO.userError "unexpected Core fault")
  | _ => throw (IO.userError "original grouped application")
end Tests.ParsedExpectedDataLambdaApplications
open Tests.ParsedExpectedDataLambdaApplications in
def Tests.frontendParsedExpectedDataLambdaApplicationTests : IO Unit := do
  let a := Solcore.Core.Value.closure .unit .word (.var 99) [.hostFunction .storageWrite,.cellRef .unit 700]
  let o := Solcore.Core.Value.cellRef (.function .unit .word) 900
  let q := Solcore.Core.Value.hostFunction .storageWrite
  for text in [mainText,inferredText] do
    for c in [false,true] do
      for d in [false,true] do exercise text a o q c d [o,q,a,.unit]
end

section
-- leanmerge: from Solcore.Test.FrontendParsedExpectedDataLambdaBoundaries
/- Independent raw original witnesses precede every search. Failed admission
does not erase annotations, saved rows, source closures or an unrelated store row. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace Tests.ParsedExpectedDataLambdaBoundaries
open Solcore Solcore.Frontend
private def check (b : Bool) (s : String) : IO Unit := unless b do throw (IO.userError s)
private def proof {p : Prop} (_ : p) : IO Unit := pure ()
private theorem noImage {v : RuntimeValue} (h : v.toCore?=none) : ¬ ∃ c, v=RuntimeValue.ofCore c := by
  rintro ⟨c,rfl⟩; have r := RuntimeValue.toCore?_ofCore c; rw [h] at r; cases r
private theorem noStoreImage {s : List RuntimeValue} (h : s.mapM RuntimeValue.toCore?=none) : ¬ ∃ c : Core.Store, s=c.map RuntimeValue.ofCore := by
  rintro ⟨c,rfl⟩
  have r : (c.map RuntimeValue.ofCore).mapM RuntimeValue.toCore?=some c := by
    clear h
    induction c with | nil => rfl | cons a as ih => simp only [List.map_cons,List.mapM_cons,RuntimeValue.toCore?_ofCore,ih,pure,bind,Option.bind_some]
  rw [h] at r; cases r
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"ExpectedBoundaries",by decide⟩],by decide⟩⟩,178⟩
private def sid (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def foreign (n : Nat) : Resolved.LocalId := ⟨{owner with declarationIndex:=901},n⟩
private def inputs : LocalTypeInputs := ⟨[⟨"x",sid 7,.bool⟩,⟨"saved",sid 31,.unit⟩,⟨"c",sid 11,.bool⟩,
  ⟨"d",sid 20,.bool⟩,⟨"arg",sid 9,.unit⟩,⟨"other",foreign 700,.unit⟩,⟨"x",foreign 701,.word⟩],by decide⟩
private def types : TypeNameTable := [(["Unit"],.unit),(["Word"],.word)]
private def up (e : Resolved.Environment) := e.map (fun r => (r.1,RuntimeValue.ofCore r.2))
private def env (a q : Core.Value) (c : Bool) : Resolved.Environment :=
  [(sid 7,.bool false),(sid 31,q),(sid 11,.bool c),(sid 20,.bool true),(sid 9,a),(foreign 700,a),(foreign 701,.word (Core.Word.ofNatModulo 99))]
private def parsed (text : String) : IO Syntax.Expr := do
  let f : Syntax.SourceFile := ⟨⟨.main,"expected-data-boundaries.sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex f | throw (IO.userError "lexer")
  match Syntax.Parser.expression (Syntax.Parser.State.initial f lexed) with
  | .ok src next => check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && src.span==Syntax.SourceSpan.fullFile f) "original complete source/EOF/diagnostics"; return src
  | _ => throw (IO.userError "original boundary parser")
private structure Shape (src : Syntax.Expr) where
  name : Syntax.Identifier
  body : Syntax.Block
  evidence : SourceUnaryLambdaShape src name body
private def shape (src : Syntax.Expr) : IO (Shape src) := do
  match original : src with
  | ⟨_,.lambda _ ⟨_,[⟨_,.inferred n⟩]⟩ _ b⟩ => return ⟨n,b,by rw [original]; exact .inferred⟩
  | ⟨_,.lambda _ ⟨_,[⟨_,.typed none n _⟩]⟩ _ b⟩ => return ⟨n,b,by rw [original]; exact .typed⟩
  | _ => throw (IO.userError "independent original raw unary shape")
private structure AC (e : Resolved.Environment) (s : Core.Store) (src : Syntax.Expr) where
  core : Core.Expr
  value : Core.Value
  gate : ClosedSourceDataExpression src
  old : LocalExpressionEvaluatesWithCost inputs.names e s src value s 1
  closed : ClosedSourceExpressionEvaluates owner inputs.names (up e) (s.map RuntimeValue.ofCore) src (RuntimeValue.ofCore value) (s.map RuntimeValue.ofCore)
  path : ∀ k, Core.Steps 1 ⟨.eval core e.values,k,s⟩ ⟨.ret value,k,s⟩
private def arg (a q : Core.Value) (s : Core.Store) (src : Syntax.Expr) : IO (AC (env a q true) s src) := do
  match original : src with
  | ⟨_,.identifier ⟨_ ,"arg"⟩⟩ =>
    have n : LocalNameTable.Lookup inputs.names "arg" (sid 9) := LocalNameTable.lookup?_iff.mp rfl
    have f : Resolved.LocalScope.Lookup (env a q true) (sid 9) a := .tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))
    have m : Resolved.LocalScope.Lookup (up (env a q true)) (sid 9) (RuntimeValue.ofCore a) := .tail (by change sid 7≠sid 9; decide) (.tail (by change sid 31≠sid 9; decide) (.tail (by change sid 11≠sid 9; decide) (.tail (by change sid 20≠sid 9; decide) .head)))
    return ⟨.var 4,a,by rw [original]; exact .reference,by rw [original]; exact .identifier n f,
      by rw [original]; exact .reference n m,fun _ => .cons (.var rfl) .refl⟩
  | ⟨_,.literal ⟨ls,.decimal "7"⟩⟩ =>
    let w := Core.Word.ofNatModulo 7
    have meaning : WordLiteralDenotes ⟨ls,.decimal "7"⟩ w := interpretWordLiteral?_sound (by rfl)
    return ⟨.word w,.word w,by rw [original]; exact .literal,by rw [original]; exact .wordLiteral meaning,
      by rw [original]; simpa only [RuntimeValue.ofCore] using ClosedSourceExpressionEvaluates.wordLiteral meaning,fun _ => .cons .word .refl⟩
  | _ => throw (IO.userError "original boundary argument")
private def identity (text : String) (ret : Core.Ty) (headerYes checkedYes : Bool) (a q : Core.Value) (s : Core.Store) : IO Unit := do
  let src ← parsed text; let e := env a q true
  match original : src with
  | ⟨cs,.call ⟨gs,.group fs⟩ ⟨args,[argument]⟩⟩ =>
    let h ← shape fs; let ac ← arg a q s argument
    match bodyShape : h.body with
    | ⟨bs,[⟨rs,.returnStmt (some ⟨es,.identifier name⟩)⟩]⟩ =>
      if equalName : name.value=h.name.value then
        have fragment : ClosedSourceDataBody h.body := by rw [bodyShape]; exact .expression .reference
        have body : ClosedSourceBodyEvaluates owner ((h.name.value,Resolved.freshLocalId owner (inputs.names.map Prod.snd))::inputs.names)
            ((Resolved.freshLocalId owner (inputs.names.map Prod.snd),RuntimeValue.ofCore ac.value)::up e) (s.map RuntimeValue.ofCore) h.body (RuntimeValue.ofCore ac.value) (s.map RuntimeValue.ofCore) := by
          rw [bodyShape]; exact .expression (.reference (equalName ▸ LocalNameTable.Lookup.head) .head)
        have oldBody : ComputationReturnTreeEvaluatesWithCost LocalExpressionEvaluatesWithCost owner ((h.name.value,sid 32)::inputs.names) ((sid 32,ac.value)::e) s h.body ac.value s 1 := by
          rw [bodyShape]; exact .expression (.identifier (equalName ▸ LocalNameTable.Lookup.head) .head)
        have made : ClosedSourceExpressionEvaluates owner inputs.names (up e) (s.map RuntimeValue.ofCore) ⟨gs,.group fs⟩ (.sourceClosure fs owner inputs.names (up e)) (s.map RuntimeValue.ofCore) := .group (.creation h.evidence)
        have closed : ClosedSourceExpressionEvaluates owner inputs.names (up e) (s.map RuntimeValue.ofCore) src (RuntimeValue.ofCore ac.value) (s.map RuntimeValue.ofCore) := by rw [original]; exact .call h.evidence made ac.closed body
        let core := Core.Expr.apply (.lambda .unit ret (.var 0)) ac.core
        have beta : Core.Evaluates (ac.value::e.values) s (.var 0) ac.value s := .var rfl
        have full (k) : Core.Steps 6 ⟨.eval core e.values,k,s⟩ ⟨.ret ac.value,k,s⟩ := CostStepComposition.apply (.cons .lambda .refl) (ac.path _) (.cons (.var rfl) .refl)
        proof oldBody; proof closed; proof (Core.steps_from_initial_sound (full []))
        check ((declareExpectedUnaryLambdaHeader? types owner inputs fs (.function .unit ret)).isSome==headerYes) "actual header disagreement versus body mismatch"
        match run : evaluateClosedSourceExpression? 3 owner inputs.names (up e) (s.map RuntimeValue.ofCore) src with
        | none => throw (IO.userError "raw original ignores annotations and expected type")
        | some (mv,ms) =>
          have actual := evaluateClosedSourceExpression?_sound run
          proof (actual.deterministic closed)
          if checked : elaborateExpectedComputationLambda? elaborateLocalExpression? types owner inputs fs (.function .unit ret)=some (.lambda .unit ret (.var 0)) then
            check checkedYes "only the declared checked boundary is admitted"
            have image {v st} := closedSourceExpectedDataLambda_invocation_core_iff h.evidence fragment checked (show e.ids=inputs.context.ids from rfl) made ac.closed (callSpan:=cs) (argumentsSpan:=args) (actualValue:=v) (actualFinal:=st)
            have transported := (image (v:=mv) (st:=ms)).mp (by simpa only [original] using actual)
            proof ((image (v:=mv) (st:=ms)).mpr transported)
            proof ((image (v:=RuntimeValue.ofCore ac.value) (st:=s.map RuntimeValue.ofCore)).mpr ⟨ac.value,s,rfl,rfl,beta⟩)
            match coreRun : Core.runStateful 6 (.initial core e.values s) with
            | .done v final => proof (Core.evaluation_deterministic (Core.runStateful_evaluation_sound coreRun) (Core.steps_from_initial_sound (full []))); check (mv.toCore?==some v && (ms.mapM RuntimeValue.toCore?)==some final) "actual complete checked-boundary endpoint"
            | _ => throw (IO.userError "actual independent Core cost 6")
            check (Core.infer? inputs.context.values core).isNone "expected checked lambda does not imply whole-call typing"
            check (elaborateLocalExpression? inputs.names inputs.context argument==some (ac.core,.word)) "actual original argument is Word, not checked lambda domain Unit"
          else check (!checkedYes && (elaborateExpectedComputationLambda? elaborateLocalExpression? types owner inputs fs (.function .unit ret)).isNone) "actual checker profile absence, never a raw language fault"
      else throw (IO.userError "original identity parameter reference")
    | _ => throw (IO.userError "original identity body")
  | _ => throw (IO.userError "original grouped identity call")
private structure RC (names : LocalNameTable) (rows : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue) (src : Syntax.Expr) where
  value : RuntimeValue
  gate : ClosedSourceDataExpression src
  evidence : ClosedSourceExpressionEvaluates owner names rows store src value store
private def rawExpr (names : LocalNameTable) (rows : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue) (src : Syntax.Expr) : IO (RC names rows store src) := do
  match original : src with
  | ⟨_,.identifier name⟩ =>
    match named : names.lookup? name.value with
    | some i => match found : rows.lookup? i with
      | some v => return ⟨v,by rw [original]; exact .reference,by rw [original]; exact .reference (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found)⟩
      | none => throw (IO.userError "independent raw row")
    | none => throw (IO.userError "independent raw name")
  | ⟨_,.group child⟩ => let h ← rawExpr names rows store child; return ⟨h.value,by rw [original]; exact .group h.gate,by rw [original]; exact .group h.evidence⟩
  | ⟨_,.tuple ⟨_,[left,right]⟩⟩ =>
    let l ← rawExpr names rows store left; let r ← rawExpr names rows store right
    return ⟨.pair l.value r.value,by rw [original]; exact .pair l.gate r.gate,by rw [original]; exact .pair l.evidence r.evidence⟩
  | ⟨_,.conditional guard _ yes _ no⟩ =>
    let g ← rawExpr names rows store guard; let a ← rawExpr names rows store yes; let b ← rawExpr names rows store no
    match value : g.value with
    | .bool c => return ⟨if c then a.value else b.value,by rw [original]; exact .conditional g.gate a.gate b.gate,
        by rw [original]; cases c <;> first | exact .conditionalTrue (value ▸ g.evidence) a.evidence | exact .conditionalFalse (value ▸ g.evidence) b.evidence⟩
    | _ => throw (IO.userError "independent raw Bool condition")
  | _ => throw (IO.userError "original raw data-child certificate")
termination_by sizeOf src
private structure RB (names : LocalNameTable) (rows : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue) (src : Syntax.Block) where
  value : RuntimeValue
  gate : ClosedSourceDataBody src
  evidence : ClosedSourceBodyEvaluates owner names rows store src value store
private def rawBody (names : LocalNameTable) (rows : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue) (src : Syntax.Block) : IO (RB names rows store src) := do
  match original : src with
  | ⟨bs,[⟨ls,.letDecl name (some ann) (some init)⟩,⟨rs,.returnStmt (some result)⟩]⟩ =>
    let a ← rawExpr names rows store init
    let fresh := Resolved.freshLocalId owner (names.map Prod.snd)
    let b ← rawExpr ((name.value,fresh)::names) ((fresh,a.value)::rows) store result
    return ⟨b.value,by rw [original]; exact .binding a.gate (.expression b.gate),by rw [original]; exact .binding a.evidence (.expression b.evidence)⟩
  | _ => throw (IO.userError "original raw pre-shadow initializer")
private def rawText := "(lam(x){let x:Unit=(x);return c?(x,saved):(saved,x);})(d?arg:other)"
private def rawBoundary (src : Syntax.Expr) (rows : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    (aligned valueImage storeImage : Bool) : IO Unit := do
  match original : src with
  | ⟨cs,.call ⟨gs,.group fs⟩ ⟨args,[argument]⟩⟩ =>
    let h ← shape fs; let ac ← rawExpr inputs.names rows store argument
    let fresh := Resolved.freshLocalId owner (inputs.names.map Prod.snd)
    let bc ← rawBody ((h.name.value,fresh)::inputs.names) ((fresh,ac.value)::rows) store h.body
    have made : ClosedSourceExpressionEvaluates owner inputs.names rows store ⟨gs,.group fs⟩ (.sourceClosure fs owner inputs.names rows) store := .group (.creation h.evidence)
    have closed : ClosedSourceExpressionEvaluates owner inputs.names rows store src bc.value store := by rw [original]; exact .call h.evidence made ac.evidence bc.evidence
    proof closed; proof bc.gate
    check (decide (rows.ids=inputs.context.ids)==aligned) "whole ordered saved IDs, not lookup equivalence"
    check (decide (fresh=sid 32 ∧ Resolved.freshLocalId owner (((h.name.value,fresh)::inputs.names).map Prod.snd)=sid 33)) "runtime-only collisions do not alter names-only freshness"
    check ((elaborateExpectedComputationLambda? elaborateLocalExpression? types owner inputs fs (.function .unit (.product .unit .unit))).isSome) "actual lambda checker cannot establish runtime alignment or image"
    match run : evaluateClosedSourceExpression? 6 owner inputs.names rows store src with
    | none => throw (IO.userError "raw preserved body succeeds before static/image boundaries")
    | some (mv,ms) =>
      proof ((evaluateClosedSourceExpression?_sound run).deterministic closed)
      check (mv.toCore?.isSome==valueImage && (ms.mapM RuntimeValue.toCore?).isSome==storeImage && ac.value.toCore?.isSome==valueImage) "entire actual payload and store, no dropped nonimage row"
      match noValue : mv.toCore? with | none => proof (noImage noValue) | some _ => pure ()
      match noStore : ms.mapM RuntimeValue.toCore? with | none => proof (noStoreImage noStore) | some _ => pure ()
  | _ => throw (IO.userError "original raw grouped application")
private def nonimageArgument (source callSrc : Syntax.Expr) (poison : RuntimeValue) (absent : poison.toCore?=none)
    (a q : Core.Value) (c : Bool) (s : Core.Store) : IO Unit := do
  match outer : source, original : callSrc with
  | ⟨_,.call ⟨_,.group fs⟩ _⟩,⟨cs,.call ⟨sp,.identifier ⟨np,"picked"⟩⟩ ⟨aps,[⟨sa,.identifier ⟨na,"arg"⟩⟩]⟩⟩ =>
    let h ← shape fs; let e := env a q c
    let names : LocalNameTable := [("picked",sid 80),("arg",sid 81)]
    let fn := RuntimeValue.sourceClosure fs owner inputs.names (up e)
    let rows : Resolved.LocalScope RuntimeValue := [(sid 80,fn),(sid 81,poison)]
    let fresh := Resolved.freshLocalId owner (inputs.names.map Prod.snd)
    let bc ← rawBody ((h.name.value,fresh)::inputs.names) ((fresh,poison)::up e) (s.map RuntimeValue.ofCore) h.body
    have callee : ClosedSourceExpressionEvaluates owner names rows (s.map RuntimeValue.ofCore) ⟨sp,.identifier ⟨np,"picked"⟩⟩ fn (s.map RuntimeValue.ofCore) := .reference .head .head
    have arg : ClosedSourceExpressionEvaluates owner names rows (s.map RuntimeValue.ofCore) ⟨sa,.identifier ⟨na,"arg"⟩⟩ poison (s.map RuntimeValue.ofCore) := .reference (.tail (by change "picked"≠"arg"; decide) .head) (.tail (by decide) .head)
    have closed : ClosedSourceExpressionEvaluates owner names rows (s.map RuntimeValue.ofCore) callSrc bc.value (s.map RuntimeValue.ofCore) := by rw [original]; exact .call h.evidence callee arg bc.evidence
    proof closed; proof (noImage absent)
    check (decide (e.ids=inputs.context.ids) && (elaborateExpectedComputationLambda? elaborateLocalExpression? types owner inputs fs (.function .unit (.product .unit .unit))).isSome) "saved Core capture is aligned and checked; only caller argument lacks an image"
    match run : evaluateClosedSourceExpression? 6 owner names rows (s.map RuntimeValue.ofCore) callSrc with
    | some (mv,ms) =>
      proof ((evaluateClosedSourceExpression?_sound run).deterministic closed)
      match failed : mv.toCore? with | none => proof (noImage failed) | some _ => throw (IO.userError "actual source closure argument unexpectedly projected")
      check ((ms.mapM RuntimeValue.toCore?)==some s) "entire raw argument call store remains a Core image"
    | none => throw (IO.userError "independent raw nonimage argument invocation")
  | _,_ => throw (IO.userError "original nonimage-argument call")
end Tests.ParsedExpectedDataLambdaBoundaries
open Tests.ParsedExpectedDataLambdaBoundaries in
def Tests.frontendParsedExpectedDataLambdaBoundaryTests : IO Unit := do
  let a := Solcore.Core.Value.closure .unit .word (.var 99) [.hostFunction .storageWrite,.cellRef .unit 700]
  let q := Solcore.Core.Value.cellRef (.function .unit .word) 900
  let store := [q,a,Solcore.Core.Value.hostFunction .storageWrite]
  identity "(lam(x:Unknown){return x;})(arg)" .unit false false a q store
  identity "(lam(x:Unit)->Unknown{return x;})(arg)" .unit false false a q store
  identity "(lam(x:Word){return x;})(arg)" .unit false false a q store
  identity "(lam(x:Unit)->Word{return x;})(arg)" .unit false false a q store
  identity "(lam(x){return x;})(arg)" .word true false a q store
  identity "(lam(x:Unit){return x;})(7)" .unit true true a q store
  let src ← parsed rawText; let inert ← parsed "lam(){return absent;}"; let called ← parsed "picked(arg)"
  let poison := Solcore.Frontend.RuntimeValue.sourceClosure inert owner [] [(sid 700,.bool true)]
  for c in [false,true] do
    let rows := up (env a q c); let heap := store.map Solcore.Frontend.RuntimeValue.ofCore
    rawBoundary src rows heap true true true
    rawBoundary src rows.tail heap false true true
    rawBoundary src rows.reverse heap false true true
    rawBoundary src ((sid 7,.unit)::rows) heap false true true
    rawBoundary src ((sid 32,poison)::rows) heap false true true
    rawBoundary src rows (heap++[poison]) true true false
    rawBoundary src (rows.map (fun r => (r.1,if r.1==sid 9 then poison else r.2))) heap true false true
    nonimageArgument src called poison (by simp only [poison,Solcore.Frontend.RuntimeValue.toCore?]) a q c store
end

section
-- leanmerge: from Solcore.Test.FrontendParsedExpectedDataLambdaInvocations
/- Original source/Core paths precede execution. Actual returned closure and
caller prefix stores remain data; image existentials are used only inside Prop. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace Tests.ParsedExpectedDataLambdaInvocations
open Solcore Solcore.Frontend
private def check (b : Bool) (s : String) : IO Unit := unless b do throw (IO.userError s)
private def proof {p : Prop} (_ : p) : IO Unit := pure ()
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"ExpectedInvocations",by decide⟩],by decide⟩⟩,176⟩
private def sid (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def foreign (n : Nat) : Resolved.LocalId := ⟨{owner with declarationIndex:=901},n⟩
private def inputs : LocalTypeInputs := ⟨[⟨"x",sid 7,.bool⟩,⟨"saved",sid 31,.unit⟩,⟨"c",sid 11,.bool⟩,
  ⟨"d",sid 20,.bool⟩,⟨"arg",sid 9,.unit⟩,⟨"other",foreign 700,.unit⟩,⟨"x",foreign 701,.word⟩],by decide⟩
private def types : TypeNameTable := [(["Unit"],.unit),(["Word"],.word)]
private def up (e : Resolved.Environment) := e.map (fun r => (r.1,RuntimeValue.ofCore r.2))
private def env (a o q : Core.Value) (c d : Bool) : Resolved.Environment :=
  [(sid 7,.bool false),(sid 31,q),(sid 11,.bool c),(sid 20,.bool d),(sid 9,a),(foreign 700,o),(foreign 701,.word (Core.Word.ofNatModulo 99))]
private abbrev Child (n : LocalNameTable) (t : Resolved.Context) (s : Syntax.Expr) (c : Core.Expr) (v : Core.Ty) :=
  ∃ r, ResolvesLocalExpression n s r ∧ Resolved.Lowers t.ids r c ∧ Resolved.HasType t r v
private structure EC (t : LocalTypeInputs) (e : Resolved.Environment) (s : Core.Store) (src : Syntax.Expr) where
  core : Core.Expr
  type : Core.Ty
  value : Core.Value
  cost : Nat
  gate : ClosedSourceDataExpression src
  elaboration : Child t.names t.context src core type
  old : LocalExpressionEvaluatesWithCost t.names e s src value s cost
  closed : ClosedSourceExpressionEvaluates owner t.names (up e) (s.map RuntimeValue.ofCore) src (RuntimeValue.ofCore value) (s.map RuntimeValue.ofCore)
private theorem mapped {e : Resolved.Environment} {i : Resolved.LocalId} {v : Core.Value}
    (h : Resolved.LocalScope.Lookup e i v) : Resolved.LocalScope.Lookup (up e) i (RuntimeValue.ofCore v) := by
  induction h with | head => exact .head | tail different _ ih => exact .tail different ih
private theorem path {t e s src} (h : EC t e s src) (same : e.ids=t.context.ids) (k : List Core.Frame) :
    Core.Steps h.cost ⟨.eval h.core e.values,k,s⟩ ⟨.ret h.value,k,s⟩ := by
  obtain ⟨r,res,low,_⟩ := h.elaboration
  exact h.old.toStepsWithContinuation res (same ▸ low) k
private def expr (t : LocalTypeInputs) (e : Resolved.Environment) (s : Core.Store) (src : Syntax.Expr) : IO (EC t e s src) := do
  match shape : src with
  | ⟨_,.identifier name⟩ =>
    match named : t.names.lookup? name.value with
    | some i => match typed : t.context.lookup? i, found : e.lookup? i, indexed : Resolved.LocalScope.index? t.context.ids i with
      | some ty,some v,some n => return ⟨.var n,ty,v,1,by rw [shape]; exact .reference,
          by rw [shape]; exact ⟨.var i,.identifier (LocalNameTable.lookup?_iff.mp named),.var (Resolved.LocalScope.index?_iff.mp indexed),.var (Resolved.LocalScope.lookup?_iff.mp typed)⟩,
          by rw [shape]; exact .identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found),
          by rw [shape]; exact .reference (LocalNameTable.lookup?_iff.mp named) (mapped (Resolved.LocalScope.lookup?_iff.mp found))⟩
      | _,_,_ => throw (IO.userError "independent original reference row")
    | none => throw (IO.userError "independent original name")
  | ⟨span,.group child⟩ =>
    check (span.startByte+1==child.span.startByte && child.span.endByte+1==span.endByte) "original group margins"
    let h ← expr t e s child
    return ⟨h.core,h.type,h.value,h.cost,by rw [shape]; exact .group h.gate,
      by obtain ⟨r,a,b,c⟩ := h.elaboration; rw [shape]; exact ⟨r,.group a,b,c⟩,
      by rw [shape]; exact .group h.old,by rw [shape]; exact .group h.closed⟩
  | ⟨span,.tuple ⟨ts,[left,right]⟩⟩ =>
    check (span==ts && span.contains left.span && span.contains right.span && left.span.endByte<right.span.startByte) "original pair ranges"
    let l ← expr t e s left; let r ← expr t e s right
    return ⟨.pair l.core r.core,.product l.type r.type,.pair l.value r.value,l.cost+r.cost+3,
      by rw [shape]; exact .pair l.gate r.gate,
      by obtain ⟨a,ar,al,alt⟩ := l.elaboration; obtain ⟨b,br,bl,bt⟩ := r.elaboration; rw [shape]; exact ⟨.pair a b,.pair ar br,.pair al bl,.pair alt bt⟩,
      by rw [shape]; exact .pair l.old r.old,by rw [shape]; simpa only [RuntimeValue.ofCore] using ClosedSourceExpressionEvaluates.pair l.closed r.closed⟩
  | ⟨span,.conditional guard qm yes colon no⟩ =>
    check (span.contains guard.span && span.contains yes.span && span.contains no.span && qm.endByte==qm.startByte+1 && colon.endByte==colon.startByte+1 && guard.span.endByte==qm.startByte && qm.endByte==yes.span.startByte && yes.span.endByte==colon.startByte && colon.endByte==no.span.startByte) "original conditional children and markers"
    let g ← expr t e s guard; let a ← expr t e s yes; let b ← expr t e s no
    if typed : g.type=.bool ∧ a.type=b.type then
      match value : g.value with
      | .bool c => return ⟨.ifE g.core a.core b.core,a.type,if c then a.value else b.value,g.cost+(if c then a.cost else b.cost)+2,
          by rw [shape]; exact .conditional g.gate a.gate b.gate,
          by obtain ⟨r,rr,rl,rt⟩ := g.elaboration; obtain ⟨u,ur,ul,ut⟩ := a.elaboration; obtain ⟨v,vr,vl,vt⟩ := b.elaboration
             rw [shape]; exact ⟨.ifE r u v,.conditional rr ur vr,.ifE rl ul vl,.ifE (typed.1 ▸ rt) ut (typed.2 ▸ vt)⟩,
          by rw [shape]; cases c <;> first | exact .ifTrue (value ▸ g.old) a.old | exact .ifFalse (value ▸ g.old) b.old,
          by rw [shape]; cases c <;> first | exact .conditionalTrue (by simpa only [value,RuntimeValue.ofCore] using g.closed) a.closed | exact .conditionalFalse (by simpa only [value,RuntimeValue.ofCore] using g.closed) b.closed⟩
      | _ => throw (IO.userError "original Bool guard payload")
    else throw (IO.userError "independent original conditional types")
  | _ => throw (IO.userError "bounded original certificate profile")
termination_by sizeOf src
private structure Meaning (src : Syntax.TypeExpr) where
  type : Core.Ty
  evidence : StructuralTypeDenotes types src type
private def meaning (src : Syntax.TypeExpr) : IO (Meaning src) := do
  match shape : src with
  | ⟨_,.named name none⟩ => match found : types.lookup? (qualifiedTypeNameKey name) with
    | some ty => return ⟨ty,by rw [shape]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩
    | none => throw (IO.userError "original annotation meaning")
  | ⟨_,.tuple [a,b]⟩ => let l ← meaning a; let r ← meaning b; return ⟨.product l.type r.type,by rw [shape]; exact .pair l.evidence r.evidence⟩
  | _ => throw (IO.userError "original annotation profile")
termination_by sizeOf src
private structure BC (t : LocalTypeInputs) (e : Resolved.Environment) (s : Core.Store) (src : Syntax.Block) where
  core : Core.Expr
  value : Core.Value
  cost : Nat
  gate : ClosedSourceDataBody src
  elaboration : ComputationReturnTreeElaborates Child types owner t src core (.product .unit .unit)
  old : ComputationReturnTreeEvaluatesWithCost LocalExpressionEvaluatesWithCost owner t.names e s src value s cost
  closed : ClosedSourceBodyEvaluates owner t.names (up e) (s.map RuntimeValue.ofCore) src (RuntimeValue.ofCore value) (s.map RuntimeValue.ofCore)
  path : ∀ k, Core.Steps cost ⟨.eval core e.values,k,s⟩ ⟨.ret value,k,s⟩
private def body (t : LocalTypeInputs) (e : Resolved.Environment) (s : Core.Store) (src : Syntax.Block) (same : e.ids=t.context.ids) : IO (BC t e s src) := do
  match shape : src with
  | ⟨bs,[⟨ls,.letDecl name (some ann) (some init)⟩,⟨rs,.returnStmt (some result)⟩]⟩ =>
    let h ← expr t e s init; let m ← meaning ann
    if typed : m.type=.unit ∧ h.type=.unit then
      let t1 := t.bindFresh owner name.value .unit
      let e1 : Resolved.Environment := (Resolved.freshLocalId owner t.ids,h.value)::e
      have same1 : e1.ids=t1.context.ids := by simpa only [e1,t1,LocalTypeInputs.bindFresh_context,Resolved.LocalScope.ids,List.map_cons] using congrArg (List.cons _) same
      let r ← expr t1 e1 s result
      if rt : r.type=.product .unit .unit then
        return ⟨.letE h.core r.core,r.value,h.cost+r.cost+2,by rw [shape]; exact .binding h.gate (.expression r.gate),
          by rw [shape]; exact .binding (typed.1 ▸ m.evidence) (typed.2 ▸ h.elaboration) (.expression (rt ▸ r.elaboration)),
          by rw [shape]; apply ComputationReturnTreeEvaluatesWithCost.binding h.old
             simpa only [e1,t1,LocalTypeInputs.bindFresh_names,LocalTypeInputs.names_ids] using ComputationReturnTreeEvaluatesWithCost.expression (blockSpan:=bs) (returnSpan:=rs) (owner:=owner) r.old,
          by rw [shape]; apply ClosedSourceBodyEvaluates.binding h.closed
             simpa only [e1,t1,LocalTypeInputs.bindFresh_names,LocalTypeInputs.names_ids,up,List.map_cons] using ClosedSourceBodyEvaluates.expression (blockSpan:=bs) (returnSpan:=rs) r.closed,
          fun k => CostStepComposition.letE (path h same _) (by simpa only [e1,Resolved.LocalScope.values,List.map_cons] using path r same1 k)⟩
      else throw (IO.userError "independent pair result type")
    else throw (IO.userError "independent Unit local shadow")
  | _ => throw (IO.userError "original typed shadow and conditional return")
private structure Header (src : Syntax.Expr) where
  name : Syntax.Identifier
  body : Syntax.Block
  shape : SourceUnaryLambdaShape src name body
  declaration : ExpectedUnaryLambdaHeaderDeclares types owner inputs src (.function .unit (.product .unit .unit))
    ⟨inputs.bindFresh owner name.value .unit,body,.unit,.product .unit .unit⟩
private def header (src : Syntax.Expr) : IO (Header src) := do
  match shape : src with
  | ⟨span,.lambda keyword ⟨ps,[⟨_,.inferred n⟩]⟩ none b⟩ =>
    check (span.contains keyword && span.contains ps && ps.contains n.span && span.contains b.span && b.value.all (fun st => b.span.contains st.span)) "original saved lambda/header/body ranges"
    return ⟨n,b,by rw [shape]; exact .inferred,by rw [shape]; exact .lambda .inferred .omitted⟩
  | _ => throw (IO.userError "original inferred saved lambda")
private def parsed (text : String) : IO Syntax.Expr := do
  let f : Syntax.SourceFile := ⟨⟨.main,"expected-data-invocations.sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex f | throw (IO.userError "lexer")
  match Syntax.Parser.expression (Syntax.Parser.State.initial f lexed) with
  | .ok src next =>
    check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && src.span==Syntax.SourceSpan.fullFile f) "original source, complete EOF and diagnostics"
    return src
  | _ => throw (IO.userError "original expression parser")
private def mainText := "(lam(x:Unit)->(Unit,Unit){let x:Unit=(x);return c?(x,saved):(saved,x);})(d?arg:other)"
private def inferredText := "(lam(x){let x:Unit=(x);return c?(x,saved):(saved,x);})(d?arg:other)"
private def caller : Resolved.DeclarationId := {owner with declarationIndex:=177}
private def cid (n : Nat) : Resolved.LocalId := ⟨caller,n⟩
private def callerNames : LocalNameTable := [("picked",cid 7),("arg",cid 900),("saved",cid 42),("c",cid 20),("picked",cid 7)]
private def callerRows (fn : RuntimeValue) (v : Core.Value) (c : Bool) :=
  [(cid 900,RuntimeValue.ofCore v),(cid 7,fn),(cid 42,.word (Core.Word.ofNatModulo 88)),(cid 20,.bool (!c)),(cid 7,fn),(foreign 999,fn)]
private def invoke (text : String) (a o q : Core.Value) (c : Bool) (s : Core.Store) : IO Unit := do
  let parsedCall ← parsed text; let callSrc ← parsed "picked(arg)"; let e := env a o q c false
  match outer : parsedCall, original : callSrc with
  | ⟨_,.call ⟨gs,.group fs⟩ _⟩,⟨cs,.call ⟨fnSpan,.identifier ⟨fnName,"picked"⟩⟩ ⟨args,[⟨argSpan,.identifier ⟨argName,"arg"⟩⟩]⟩⟩ =>
    let h ← header fs
    let inner := inputs.bindFresh owner h.name.value .unit
    let ie : Resolved.Environment := (Resolved.freshLocalId owner inputs.ids,a)::e
    have same : e.ids=inputs.context.ids := rfl
    have same1 : ie.ids=inner.context.ids := by simpa only [ie,inner,LocalTypeInputs.bindFresh_context,Resolved.LocalScope.ids,List.map_cons] using congrArg (List.cons _) same
    let bc ← body inner ie s h.body same1
    have expected : ExpectedComputationLambdaElaborates Child types owner inputs fs (.lambda .unit (.product .unit .unit) bc.core) (.function .unit (.product .unit .unit)) := .lambda h.declaration .unit (.product .unit .unit) bc.elaboration
    let saved := RuntimeValue.sourceClosure fs owner inputs.names (up e)
    let oldStore : Core.Store := [.word (Core.Word.ofNatModulo 5)]
    have creation : ClosedSourceExpressionEvaluates owner inputs.names (up e) (oldStore.map RuntimeValue.ofCore) ⟨gs,.group fs⟩ saved (oldStore.map RuntimeValue.ofCore) := .group (.creation h.shape)
    have fn (f : RuntimeValue) (hf : f=saved) : ClosedSourceExpressionEvaluates caller callerNames (callerRows f a c) (s.map RuntimeValue.ofCore) ⟨fnSpan,.identifier ⟨fnName,"picked"⟩⟩ saved (s.map RuntimeValue.ofCore) := by
      rw [← hf]; exact .reference .head (.tail (by decide) .head)
    have arg (f : RuntimeValue) : ClosedSourceExpressionEvaluates caller callerNames (callerRows f a c) (s.map RuntimeValue.ofCore) ⟨argSpan,.identifier ⟨argName,"arg"⟩⟩ (RuntimeValue.ofCore a) (s.map RuntimeValue.ofCore) := .reference (.tail (by change "picked" ≠ "arg"; decide) .head) .head
    have call (f : RuntimeValue) (hf : f=saved) : ClosedSourceExpressionEvaluates caller callerNames (callerRows f a c) (s.map RuntimeValue.ofCore) callSrc (RuntimeValue.ofCore bc.value) (s.map RuntimeValue.ofCore) := by
      rw [original]; apply ClosedSourceExpressionEvaluates.call h.shape (fn f hf) (arg f)
      simpa only [saved,ie,inner,LocalTypeInputs.bindFresh_names,LocalTypeInputs.names_ids,up,List.map_cons] using bc.closed
    have beta (k) : Core.Steps bc.cost ⟨.eval bc.core (a::e.values),k,s⟩ ⟨.ret bc.value,k,s⟩ := by simpa only [ie,Resolved.LocalScope.values,List.map_cons] using bc.path k
    let core := Core.Expr.apply (.var 0) (.var 1)
    let coreEnv := [Core.Value.closure .unit (.product .unit .unit) bc.core e.values,a,.word (Core.Word.ofNatModulo 88)]
    have full (k) : Core.Steps (1+1+bc.cost+3) ⟨.eval core coreEnv,k,s⟩ ⟨.ret bc.value,k,s⟩ := CostStepComposition.apply (.cons (.var rfl) .refl) (.cons (.var rfl) .refl) (beta [])
    proof expected; proof creation; proof (call saved rfl); proof (Core.steps_from_initial_sound (full []))
    check (decide (bc.value=(if c then .pair a q else .pair q a))) "independent saved capture and caller argument endpoint"
    check (gs.startByte==0 && fs.span.startByte==1 && fs.span.endByte+1==gs.endByte && cs.startByte==0 && cs.endByte==11 && cs.contains args && fnSpan==fnName && argSpan==argName) "original creation subtree and separate call spans"
    check (decide (bc.cost=11 ∧ owner≠caller ∧ Resolved.freshLocalId owner inputs.ids=sid 32 ∧ Resolved.freshLocalId owner inner.ids=sid 33 ∧ Resolved.freshLocalId caller (callerNames.map Prod.snd)=cid 901 ∧ oldStore≠s)) "independent beta cost, saved/caller IDs and no heap snapshot"
    have independentChecked := (elaborateExpectedComputationLambda?_iff elaborateLocalExpression?_iff).mpr expected
    proof independentChecked
    check (elaborateExpectedComputationLambda? elaborateLocalExpression? types owner inputs fs (.function .unit (.product .unit .unit))==some (.lambda .unit (.product .unit .unit) bc.core) && elaborateComputationReturnTree? elaborateLocalExpression? types owner inner h.body==some (bc.core,.product .unit .unit)) "actual saved expected and original shared body checker"
    match Core.runStateful 15 (.initial core coreEnv s) with
    | .outOfFuel _ => pure ()
    | _ => throw (IO.userError "Core harness requires 16 transitions")
    match made : evaluateClosedSourceExpression? 2 owner inputs.names (up e) (oldStore.map RuntimeValue.ofCore) ⟨gs,.group fs⟩ with
    | none => throw (IO.userError "actual original grouped creation")
    | some (actualClosure,actualCreationStore) =>
      have creationEq := (evaluateClosedSourceExpression?_sound made).deterministic creation
      let rows := callerRows actualClosure a c
      proof creationEq
      match fetched : evaluateClosedSourceExpression? 1 caller callerNames rows (s.map RuntimeValue.ofCore) ⟨fnSpan,.identifier ⟨fnName,"picked"⟩⟩ with
      | none => throw (IO.userError "actual returned closure lookup")
      | some (actualFn,calleeStore) =>
        have fnEq := (evaluateClosedSourceExpression?_sound fetched).deterministic (fn actualClosure creationEq.1)
        match argument : evaluateClosedSourceExpression? 1 caller callerNames rows calleeStore ⟨argSpan,.identifier ⟨argName,"arg"⟩⟩ with
        | none => throw (IO.userError "actual caller argument after actual callee store")
        | some (actualArg,bodyStore) =>
          have argEq := (evaluateClosedSourceExpression?_sound (fnEq.2 ▸ argument)).deterministic (arg actualClosure)
          proof fnEq; proof argEq
          have fnEval : ClosedSourceExpressionEvaluates caller callerNames rows (s.map RuntimeValue.ofCore) ⟨fnSpan,.identifier ⟨fnName,"picked"⟩⟩ saved calleeStore := by simpa only [fnEq.1] using evaluateClosedSourceExpression?_sound fetched
          have argEval : ClosedSourceExpressionEvaluates caller callerNames rows calleeStore ⟨argSpan,.identifier ⟨argName,"arg"⟩⟩ (RuntimeValue.ofCore a) (s.map RuntimeValue.ofCore) := by simpa only [argEq.1,argEq.2] using evaluateClosedSourceExpression?_sound argument
          have image {v st} := closedSourceExpectedDataLambda_invocation_core_iff h.shape bc.gate independentChecked same fnEval argEval (callSpan:=cs) (argumentsSpan:=args) (actualValue:=v) (actualFinal:=st)
          for depth in [0,1,5,6,9] do
            match run : evaluateClosedSourceExpression? depth caller callerNames rows (s.map RuntimeValue.ofCore) callSrc with
            | none => check (depth<6) "actual invocation depth below 6"
            | some (mv,ms) =>
              have actual := evaluateClosedSourceExpression?_sound run
              proof (actual.deterministic (call actualClosure creationEq.1)); check (depth≥6) "actual invocation depth 6"
              have forward := (image (v:=mv) (st:=ms)).mp (by simpa only [original] using actual)
              match coreRun : Core.runStateful 16 (.initial core coreEnv s) with
              | .done cv final =>
                have actualCore := Core.runStateful_evaluation_sound coreRun
                have fc : Core.Evaluates coreEnv s (.var 0) (.closure .unit (.product .unit .unit) bc.core e.values) s := .var rfl
                have av : Core.Evaluates coreEnv s (.var 1) a s := .var rfl
                have equal : mv=RuntimeValue.ofCore cv ∧ ms=final.map RuntimeValue.ofCore := by
                  obtain ⟨v,st,hv,hs,ev⟩ := forward
                  have both := Core.evaluation_deterministic (Core.Evaluates.apply fc av ev) actualCore
                  simpa only [both.1,both.2] using And.intro hv hs
                have actualBeta : Core.Evaluates (a::e.values) s bc.core cv final := by
                  change Core.Evaluates coreEnv s (.apply (.var 0) (.var 1)) cv final at actualCore
                  cases actualCore with
                  | apply f ar b =>
                    obtain ⟨hf,hs⟩ := Core.evaluation_deterministic f fc; cases hf; cases hs
                    obtain ⟨ha,hs⟩ := Core.evaluation_deterministic ar av; cases ha; cases hs; exact b
                proof ((image (v:=mv) (st:=ms)).mpr ⟨cv,final,equal.1,equal.2,actualBeta⟩)
                proof ((image (v:=RuntimeValue.ofCore cv) (st:=final.map RuntimeValue.ofCore)).mpr ⟨cv,final,rfl,rfl,actualBeta⟩); proof equal
                check (mv.toCore?==some cv && (ms.mapM RuntimeValue.toCore?)==some final) "actual full endpoint projected only after both directions"
              | _ => throw (IO.userError "actual Core harness cost 16")
  | _,_ => throw (IO.userError "original saved grouped lambda and lookup call")
end Tests.ParsedExpectedDataLambdaInvocations
open Tests.ParsedExpectedDataLambdaInvocations in
def Tests.frontendParsedExpectedDataLambdaInvocationTests : IO Unit := do
  let a := Solcore.Core.Value.closure .unit .word (.var 99) [.hostFunction .storageWrite,.cellRef .unit 700]
  let o := Solcore.Core.Value.cellRef (.function .unit .word) 900
  let q := Solcore.Core.Value.hostFunction .storageWrite
  for c in [false,true] do invoke inferredText a o q c [o,q,a,.unit]
end

section
-- leanmerge: from Solcore.Test.FrontendParsedExpectedLambdaArgumentApplication
/-! A parsed ADR0317 consumer whose declarative children and Core endpoint are
constructed independently before the executable correspondence is consumed. -/

set_option autoImplicit false

namespace Tests.ADR0317ParsedExpectedLambdaArgumentConsumerIndependent

open Solcore Solcore.Frontend

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def proof {proposition : Prop} (_ : proposition) : IO Unit := pure ()

private def declaration (index : Nat) : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"ParsedExpectedArgument", by decide⟩], by decide⟩⟩, index⟩
private def owner := declaration 317
private def foreignOwner := declaration 9317
private def localId (owner : Resolved.DeclarationId) (index : Nat) : Resolved.LocalId :=
  ⟨owner, index⟩
private def applyId := localId owner 17
private def opaqueId := localId foreignOwner 700
private def duplicateId := localId owner 3
private def flagId := localId foreignOwner 701
private def ordinaryId := localId owner 29

private def functionType : Core.Ty := .function .word .word
private def inputs : LocalTypeInputs := ⟨[
  ⟨"apply", applyId, .function functionType .word⟩,
  ⟨"opaque", opaqueId, .cell .word⟩,
  ⟨"apply", duplicateId, .unit⟩,
  ⟨"flag", flagId, .bool⟩,
  ⟨"ordinary", ordinaryId, functionType⟩
], by decide⟩
private def types : TypeNameTable := []

private def range (file : Syntax.SourceFile) (start stop : Nat) : Syntax.SourceSpan :=
  ⟨file.id, start, stop⟩
private def reference (file : Syntax.SourceFile) (start stop : Nat) (name : String) :
    Syntax.Expr :=
  ⟨range file start stop, .identifier ⟨range file start stop, name⟩⟩
private def body (file : Syntax.SourceFile) : Syntax.Block :=
  ⟨range file 12 23,
    [⟨range file 13 22, .returnStmt (some (reference file 20 21 "x"))⟩]⟩
private def argument (file : Syntax.SourceFile) : Syntax.Expr :=
  ⟨range file 6 23, .lambda (range file 6 9)
    ⟨range file 9 12,
      [⟨range file 10 11, .inferred ⟨range file 10 11, "x"⟩⟩]⟩
    none (body file)⟩
private def source (file : Syntax.SourceFile) : Syntax.Expr :=
  ⟨range file 0 24, .call (reference file 0 5 "apply")
    ⟨range file 5 24, [argument file]⟩⟩

private def core : Core.Expr :=
  .apply (.var 0) (.lambda .word .word (.var 0))

private theorem calleeElaboration (file : Syntax.SourceFile) :
    RecursiveLocalComputationElaborates inputs.names inputs.context
      (reference file 0 5 "apply") (.var 0) (.function functionType .word) :=
  .pure (.identifier .head) (.var .head) (.var .head)

private theorem argumentElaboration (file : Syntax.SourceFile) :
    ExpectedComputationLambdaElaborates RecursiveLocalComputationElaborates
      types owner inputs (argument file) (.lambda .word .word (.var 0)) functionType := by
  apply ExpectedComputationLambdaElaborates.lambda
    (header := ⟨inputs.bindFresh owner "x" .word, body file, .word, .word⟩)
  · exact ExpectedUnaryLambdaHeaderDeclares.lambda
      ExpectedLambdaParameterDeclares.inferred ExpectedLambdaReturnDenotes.omitted
  · exact .word
  · exact .word
  · exact ComputationReturnTreeElaborates.expression
      (RecursiveLocalComputationElaborates.pure
        (ResolvesLocalExpression.identifier .head) (Resolved.Lowers.var .head)
        (Resolved.HasType.var .head))

private theorem independentElaboration (file : Syntax.SourceFile) :
    ExpectedLambdaArgumentApplicationElaborates
      types owner inputs (source file) core .word :=
  .application (calleeElaboration file) (argumentElaboration file)

private theorem oldCheckerRejects (file : Syntax.SourceFile) :
    elaborateRecursiveLocalComputation? inputs.names inputs.context (source file) = none := by
  change elaborateRecursiveLocalComputation?
    [("apply", applyId), ("opaque", opaqueId), ("apply", duplicateId),
      ("flag", flagId), ("ordinary", ordinaryId)]
    [(applyId, .function functionType .word), (opaqueId, .cell .word),
      (duplicateId, .unit), (flagId, .bool), (ordinaryId, functionType)]
    (source file) = none
  simp [source, argument, body, reference, elaborateRecursiveLocalComputation?,
    elaborateLocalExpression?, resolveLocalExpression?, functionType,
    LocalNameTable.lookup?]

/-- Static evidence is written independently; only then is the adapter iff used
to recover its exact executable result and Core type. -/
theorem parsed_expected_lambda_argument_static_contract (file : Syntax.SourceFile) :
    inputs.names[2]? = some ("apply", duplicateId) ∧
    inputs.names[1]?.map Prod.snd = some opaqueId ∧
    ExpectedLambdaArgumentApplicationElaborates
      types owner inputs (source file) core .word ∧
    elaborateRecursiveLocalComputation? inputs.names inputs.context (source file) = none ∧
    elaborateExpectedLambdaArgumentApplication? types owner inputs (source file) =
      some (core, .word) ∧
    Core.HasType inputs.context.values core .word := by
  have evidence := independentElaboration file
  have checked := elaborateExpectedLambdaArgumentApplication?_iff.mpr evidence
  have restored := elaborateExpectedLambdaArgumentApplication?_iff.mp checked
  exact ⟨rfl, rfl, evidence, oldCheckerRejects file, checked, restored.core_hasType⟩

private def seven : Core.Word := Core.Word.ofNatModulo 7
private def opaqueValue : Core.Value :=
  .closure .unit .word (.var 99)
    [.hostFunction .storageWrite, .cellRef (.function .word .unit) 700]
private def duplicateValue : Core.Value := .cellRef (.function .unit .word) 31
private def ordinaryValue : Core.Value :=
  .closure .word .word (.var 0) [.hostFunction .storageRead]
private def applyBody : Core.Expr := .apply (.var 0) (.word seven)
private def applyValue : Core.Value :=
  .closure functionType .word applyBody [opaqueValue, .hostFunction .storageWrite]
private def environment : List (Resolved.LocalId × Core.Value) := [
  (applyId, applyValue), (opaqueId, opaqueValue), (duplicateId, duplicateValue),
  (flagId, .bool false), (ordinaryId, ordinaryValue)]
private def store : Core.Store :=
  [opaqueValue, .cellRef (.function .word .word) 23, .hostFunction .storageWrite]

/-- The Core result does not depend on the four unrelated rows or on the
initial store, including closures, cells and host values. -/
theorem independently_executed_core_application
    (opaqueRow duplicateRow flagRow ordinaryRow : Core.Value) (initialStore : Core.Store) :
    Core.Evaluates [applyValue, opaqueRow, duplicateRow, flagRow, ordinaryRow] initialStore
      core (.word seven) initialStore := by
  exact .apply (.var rfl) .lambda
    (.apply (.var rfl) .word (.var rfl))

private def parseComplete (path text : String) : IO (Syntax.SourceFile × Syntax.Expr) := do
  let file : Syntax.SourceFile := ⟨⟨.main, path⟩, text⟩
  let .ok lexed := Syntax.Lexer.lex file |
    throw (IO.userError s!"{path}: lexer rejected")
  check lexed.diagnostics.isEmpty s!"{path}: lexer diagnostics"
  match Syntax.Parser.expression (Syntax.Parser.State.initial file lexed) with
  | .ok parsed next =>
    check (next.diagnostics.isEmpty && next.atEnd &&
      parsed.span == Syntax.SourceSpan.fullFile file)
      s!"{path}: parser diagnostics, EOF or full span"
    pure (file, parsed)
  | _ => throw (IO.userError s!"{path}: parser rejected")

private def rejectedParsed (label text : String) : IO Unit := do
  let (_, parsed) ← parseComplete s!"adr0317-{label}.sol" text
  check (elaborateExpectedLambdaArgumentApplication? types owner inputs parsed).isNone
    s!"{label}: adapter unexpectedly accepted"

private def exercise : IO Unit := do
  let (file, parsed) ← parseComplete "adr0317-parsed-expected-argument.sol"
    "apply(lam(x){return x;})"
  match parsedShape : parsed with
  | ⟨callSpan, .call
      ⟨calleeSpan, .identifier ⟨calleeNameSpan, calleeName⟩⟩
      ⟨argumentsSpan, [⟨lambdaSpan, .lambda keywordSpan
        ⟨parametersSpan,
          [⟨parameterSpan, .inferred ⟨parameterNameSpan, parameterName⟩⟩]⟩ none
        ⟨bodySpan, [⟨statementSpan, .returnStmt
          (some ⟨resultSpan, .identifier ⟨resultNameSpan, resultName⟩⟩)⟩]⟩⟩]⟩⟩ =>
    if exactSpans : calleeName = "apply" ∧ parameterName = "x" ∧ resultName = "x" ∧
        callSpan = range file 0 24 ∧
        calleeSpan = range file 0 5 ∧ calleeNameSpan = range file 0 5 ∧
        argumentsSpan = range file 5 24 ∧ lambdaSpan = range file 6 23 ∧
        keywordSpan = range file 6 9 ∧ parametersSpan = range file 9 12 ∧
        parameterSpan = range file 10 11 ∧ parameterNameSpan = range file 10 11 ∧
        bodySpan = range file 12 23 ∧ statementSpan = range file 13 22 ∧
        resultSpan = range file 20 21 ∧ resultNameSpan = range file 20 21 then
      have parsedEq : parsed = source file := by
        rcases exactSpans with
          ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        exact parsedShape
      check ([range file 0 24, range file 0 5, range file 5 24, range file 6 23,
        range file 6 9, range file 9 12, range file 10 11, range file 12 23,
        range file 13 22, range file 20 21].all (fun span => span.isValidFor file))
        "main: exact nested spans are not valid"
      check (elaborateRecursiveLocalComputation? inputs.names inputs.context parsed).isNone
        "main: old recursive checker accepted the literal argument"
      check (elaborateExpectedLambdaArgumentApplication? types owner inputs parsed ==
        some (core, .word)) "main: adapter did not return the literal Core apply"
      proof (show elaborateRecursiveLocalComputation? inputs.names inputs.context parsed = none by
        rw [parsedEq]; exact oldCheckerRejects file)

      match shortRun : Core.runStateful 10
          (Core.State.initial core (environment.map Prod.snd) store) with
      | .outOfFuel _ => pure ()
      | _ => throw (IO.userError "Core completed below exact fuel 11")
      match exactRun : Core.runStateful 11
          (Core.State.initial core (environment.map Prod.snd) store) with
      | .done value finalStore =>
        check (value == .word seven && finalStore == store)
          "Core exact value or opaque store changed"
        have actual := Core.runStateful_evaluation_sound exactRun
        have expected : Core.Evaluates (environment.map Prod.snd) store core
            (.word seven) store := by
          simpa [environment] using independently_executed_core_application
            opaqueValue duplicateValue (.bool false) ordinaryValue store
        proof (Core.evaluation_deterministic actual expected)
      | .outOfFuel _ => throw (IO.userError "Core did not complete at exact fuel 11")
      | .fault _ _ => throw (IO.userError "Core faulted")

      have evidence := independentElaboration file
      proof evidence
      have checked : elaborateExpectedLambdaArgumentApplication? types owner inputs parsed =
          some (core, .word) := by
        rw [parsedEq]
        exact elaborateExpectedLambdaArgumentApplication?_iff.mpr evidence
      proof checked
      proof (elaborateExpectedLambdaArgumentApplication?_iff.mp checked)
      proof (parsed_expected_lambda_argument_static_contract file)
    else throw (IO.userError "main: exact parsed AST or nested spans differ")
  | _ => throw (IO.userError "main: parsed AST shape differs")

  rejectedParsed "bad-body" "apply(lam(x){return flag;})"
  rejectedParsed "nonfunction" "flag(lam(x){return x;})"
  rejectedParsed "empty-arity" "apply()"
  rejectedParsed "many-arity" "apply(lam(x){return x;},lam(y){return y;})"
  rejectedParsed "top-level" "lam(x){return x;}"

  let (_, ordinary) ← parseComplete "adr0317-ordinary.sol" "apply(ordinary)"
  check (elaborateExpectedLambdaArgumentApplication? types owner inputs ordinary).isNone
    "ordinary: nonliteral argument entered the adapter"
  check (elaborateRecursiveLocalComputation? inputs.names inputs.context ordinary ==
    some (.apply (.var 0) (.var 4), .word))
    "ordinary: existing recursive call path was not preserved"

end Tests.ADR0317ParsedExpectedLambdaArgumentConsumerIndependent

def Tests.adr0317ParsedExpectedLambdaArgumentTests : IO Unit := do
  ADR0317ParsedExpectedLambdaArgumentConsumerIndependent.exercise
  IO.println "ADR0317 parsed expected-lambda argument consumer GREEN"
end

section
-- leanmerge: from Solcore.Test.FrontendParsedExpectedLambdaHeaders
/-! Original parsed headers are certified before the opt-in checker is used.
Separate inner-body evidence never becomes lambda admission or a runtime closure. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedExpectedLambdaHeaders
private def check (p : Bool) (label : String) : IO Unit := do unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"ExpectedLambdaHeaders",by decide⟩],by decide⟩⟩,146⟩
private def id (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def foreign : Resolved.LocalId := ⟨{owner with declarationIndex:=900},700⟩
private def outer : LocalTypeInputs :=
  ⟨[⟨"x",id 7,.bool⟩,⟨"saved",id 31,.word⟩,⟨"x",foreign,.unit⟩],by decide⟩
private def types : TypeNameTable := [(["A"],.word),(["B"],.bool),(["A"],.bool),(["B"],.word)]
private def file (text : String) : Syntax.SourceFile := ⟨⟨.main,"expected-lambda-headers.sol"⟩,text⟩
private def parsed (text : String) (diagnostics : Nat := 0) : IO Syntax.Expr := do
  let .ok lexed := Syntax.Lexer.lex (file text) | throw (IO.userError "lexer invariant")
  match Syntax.Parser.expression (Syntax.Parser.State.initial (file text) lexed) with
  | .ok source next =>
      check (lexed.diagnostics.isEmpty && next.atEnd && decide (next.diagnostics.length=diagnostics ∧
        source.span=⟨(file text).id,0,text.utf8ByteSize⟩)) "original full range and explicit recovery count"
      match source.value with
      | .lambda keyword parameters result body =>
          check (source.span.contains keyword && source.span.contains parameters.span && source.span.contains body.span &&
            decide (keyword.startByte=0 ∧ keyword.endByte=3 ∧ keyword.endByte≤parameters.span.startByte ∧ parameters.span.endByte≤body.span.startByte) &&
            parameters.elements.all (fun p => parameters.span.contains p.span && match p.value with
              | .inferred name => decide (p.span=name.span)
              | .typed marker name annotation => p.span.contains name.span && p.span.contains annotation.span &&
                  marker.toList.all (fun m => p.span.contains m && decide (m.endByte≤name.span.startByte))
              | .error => true) &&
            (result.toList.all fun r => source.span.contains r.span && decide (parameters.span.endByte≤r.span.startByte ∧ r.span.endByte≤body.span.startByte))) "original lambda fields and order"
      | _ => pure ()
      return source
  | .reject _ _ => throw (IO.userError "source rejected")
  | .invariant _ => throw (IO.userError "parser invariant")
private structure Meaning (table : TypeNameTable) (source : Syntax.TypeExpr) where
  type : Core.Ty
  evidence : StructuralTypeDenotes table source type
private def meaning (table : TypeNameTable) (source : Syntax.TypeExpr) : IO (Option (Meaning table source)) := do
  match shape : source with
  | ⟨_,.named name none⟩ => match found : table.lookup? (qualifiedTypeNameKey name) with
      | none => return none
      | some type => return some ⟨type,by rw [shape]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩
  | ⟨_,.tuple []⟩ => return some ⟨.unit,by rw [shape]; exact .unit⟩
  | ⟨_,.tuple [child]⟩ =>
      let some m ← meaning table child | return none
      return some ⟨m.type,by rw [shape]; exact .single m.evidence⟩
  | ⟨_,.tuple [left,right]⟩ =>
      let some a ← meaning table left | return none
      let some b ← meaning table right | return none
      return some ⟨.product a.type b.type,by rw [shape]; exact .pair a.evidence b.evidence⟩
  | ⟨_,.function _ ⟨_,[parameter]⟩ none⟩ =>
      let some a ← meaning table parameter | return none
      return some ⟨.function a.type .unit,by rw [shape]; exact .functionDefault a.evidence⟩
  | ⟨_,.function _ ⟨_,[parameter]⟩ (some ⟨span,results⟩)⟩ =>
      let some a ← meaning table parameter | return none
      let some b ← meaning table ⟨span,.tuple results⟩ | return none
      return some ⟨.function a.type b.type,by rw [shape]; exact .functionReturns a.evidence b.evidence⟩
  | _ => return none
termination_by sizeOf source
private structure Parameter (table : TypeNameTable) (p : Syntax.LambdaParameter) (a : Core.Ty) where
  name : String
  evidence : ExpectedLambdaParameterDeclares table owner outer p a (outer.bindFresh owner name a)
private def parameter (table : TypeNameTable) (p : Syntax.LambdaParameter) (a : Core.Ty) : IO (Option (Parameter table p a)) := do
  match shape : p with
  | ⟨_,.inferred name⟩ => return some ⟨name.value,by rw [shape]; exact .inferred⟩
  | ⟨_,.typed none name annotation⟩ =>
      let some m ← meaning table annotation | return none
      if same : m.type=a then return some ⟨name.value,by rw [shape]; exact .typed (same ▸ m.evidence)⟩
      else return none
  | _ => return none
private structure Header (table : TypeNameTable) (source : Syntax.Expr) (expected : Core.Ty) where
  output : DeclaredUnaryLambdaHeader
  evidence : ExpectedUnaryLambdaHeaderDeclares table owner outer source expected output
private def header (table : TypeNameTable) (source : Syntax.Expr) (expected : Core.Ty) : IO (Option (Header table source expected)) := do
  match shape : source, expectedShape : expected with
  | ⟨_,.lambda _ ⟨_,[p]⟩ result body⟩,.function a b =>
      let some declared ← parameter table p a | return none
      let output : DeclaredUnaryLambdaHeader := ⟨outer.bindFresh owner declared.name a,body,a,b⟩
      match present : result with
      | none => return some ⟨output,by rw [shape,present,expectedShape]; exact .lambda declared.evidence .omitted⟩
      | some annotation =>
          let some m ← meaning table annotation | return none
          if same : m.type=b then return some ⟨output,by rw [shape,present,expectedShape]; exact .lambda declared.evidence (.annotated (same ▸ m.evidence))⟩
          else return none
  | _,_ => return none
private structure Body (table : TypeNameTable) (inputs : LocalTypeInputs) (source : Syntax.Block) where
  core : Core.Expr
  type : Core.Ty
  evidence : ComputationReturnTreeElaborates RecursiveLocalComputationElaborates table owner inputs source core type
  typing : ComputationReturnTreeHasType RecursiveLocalComputationHasType table owner inputs source type
private def body (table : TypeNameTable) (inputs : LocalTypeInputs) (source : Syntax.Block) : IO (Option (Body table inputs source)) := do
  match shape : source with
  | ⟨_,[⟨_,.returnStmt none⟩]⟩ => return some ⟨.unit,.unit,by rw [shape]; exact .bare,by rw [shape]; exact .bare⟩
  | ⟨_,[⟨_,.returnStmt (some ⟨_,.identifier name⟩)⟩]⟩ =>
      match named : inputs.names.lookup? name.value with
      | none => return none
      | some i => match typed : inputs.context.lookup? i, position : Resolved.LocalScope.index? inputs.context.ids i with
          | some t,some n => return some ⟨.var n,t,by
              rw [shape]; exact .expression (.pure (.identifier (LocalNameTable.lookup?_iff.mp named))
                (.var (Resolved.LocalScope.index?_iff.mp position)) (.var (Resolved.LocalScope.lookup?_iff.mp typed))),by
              rw [shape]; exact .expression (.pure (.identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp typed)))⟩
          | _,_ => return none
  | _ => return none
private def accepted (text : String) (table : TypeNameTable) (a b : Core.Ty)
    (name : String := "x") (diagnostics : Nat := 0) (bodyExpected : Option (Core.Expr × Core.Ty) := none) : IO Unit := do
  let source ← parsed text diagnostics
  let some independent ← header table source (.function a b) | throw (IO.userError "independent original header")
  have complete := declareExpectedUnaryLambdaHeader?_iff.mpr independent.evidence
  match accepted : declareExpectedUnaryLambdaHeader? table owner outer source (.function a b) with
  | none => nomatch complete.symm.trans accepted
  | some output =>
      have restored := declareExpectedUnaryLambdaHeader?_iff.mp accepted
      have identical := independent.evidence.result_unique restored
      have provenance := independent.evidence.provenance_and_layout
      have notNone : declareExpectedUnaryLambdaHeader? table owner outer source (.function a b)≠none :=
        fun rejected => (declareExpectedUnaryLambdaHeader?_eq_none_iff.mp rejected) ⟨_,independent.evidence⟩
      have sameBody : output.body=independent.output.body := congrArg (·.body) identical.symm
      have _ := provenance; have _ := notNone
      check (decide (output.inputs.names=(name,id 32)::outer.names ∧ output.inputs.context=(id 32,a)::outer.context ∧
        output.parameterType=a ∧ output.returnType=b) && output.body==independent.output.body) "exact computed record, fresh owner-local row and original body"
      have _ := sameBody
      check (decide (outer.names.lookup? "x"=some (id 7) ∧ outer.context.lookup? (id 7)=some .bool ∧
        output.inputs.names.lookup? name=some (id 32))) "inner-first lookup retains old x and foreign sparse row"
      if let some expectedBody := bodyExpected then
        let some originalBody ← body table independent.output.inputs independent.output.body | throw (IO.userError "independent inner body")
        check (decide ((originalBody.core,originalBody.type)=expectedBody)) "literal body expectation independent of declared codomain"
        have checked := (elaborateComputationReturnTree?_iff elaborateRecursiveLocalComputation?_iff).mpr originalBody.evidence
        check (decide (elaborateComputationReturnTree? elaborateRecursiveLocalComputation? table owner
          independent.output.inputs independent.output.body=some expectedBody)) "separate body checking only"
        have _ := checked; have _ := originalBody.typing
      check (elaborateRecursiveLocalComputation? outer.names outer.context source).isNone "source lambda still excluded from recursive child"
private def rejected (text : String) (expected : Core.Ty) (diagnostics : Nat := 0) (table : TypeNameTable := types) : IO Unit := do
  let source ← parsed text diagnostics
  check (← header table source expected).isNone "independent header profile rejects"
  if rejected : declareExpectedUnaryLambdaHeader? table owner outer source expected=none then
    have noHeader := declareExpectedUnaryLambdaHeader?_eq_none_iff.mp rejected
    have _ := noHeader
  else throw (IO.userError "unsupported original header accepted")
private def bodyRejected (text : String) (diagnostics : Nat := 0) : IO Unit := do
  let source ← parsed text diagnostics
  let some independent ← header types source (.function .word .bool) | throw (IO.userError "body-independent header")
  have _ := declareExpectedUnaryLambdaHeader?_iff.mpr independent.evidence
  check (declareExpectedUnaryLambdaHeader? types owner outer source (.function .word .bool)).isSome "computed header accepts the unchanged bad body"
  check (elaborateRecursiveLocalComputation? outer.names outer.context source).isNone "bad lambda body does not change the old child boundary"
  check (elaborateComputationReturnTree? elaborateRecursiveLocalComputation? types owner
    independent.output.inputs independent.output.body).isNone "valid header does not validate unresolved, ill-typed or recovered body"
private def wholeRejected (lambda : String) : IO Unit := do
  let text := "function outer() returns(function(A) returns(A)){return "++lambda++";}"
  let .ok lexed := Syntax.Lexer.lex (file text) | throw (IO.userError "function lexer invariant")
  match Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial (file text) lexed) with
  | .ok declaration next =>
      check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
        decide (declaration.span=⟨(file text).id,0,text.utf8ByteSize⟩)) "original complete function"
      check (decide (interpretRuntimeFunctionHeader? types declaration.value.signature=some (.function .word .word)) &&
        (declareRuntimeParameters? types owner declaration.value.signature.parameters.elements).isSome) "named header and parameter policies already accept this original wrapper"
      match declaration.value.body.value with
      | [⟨_,.returnStmt (some source)⟩] =>
          let some independent ← header types source (.function .word .word) | throw (IO.userError "actual original returned lambda header")
          have _ := declareExpectedUnaryLambdaHeader?_iff.mpr independent.evidence
          check (declaration.value.body.span.contains source.span && (elaborateRecursiveLocalComputation? [] [] source).isNone) "actual returned source, not a fabricated lambda body"
      | _ => throw (IO.userError "original function body shape")
      check (compileComputationFunction? elaborateRecursiveLocalComputation? types owner declaration).isNone "old value-free compilation unchanged"
      check (prepareComputationFunction? elaborateRecursiveLocalComputation? types owner declaration []).isNone "old actual preparation unchanged"
      for fuel in [0,1,50] do
        check (runComputationFunction? elaborateRecursiveLocalComputation? types owner declaration [] fuel []).isNone "no source lambda runner admission"
  | .reject _ _ => throw (IO.userError "function rejected")
  | .invariant _ => throw (IO.userError "function parser invariant")
end ParsedExpectedLambdaHeaders
open ParsedExpectedLambdaHeaders
def frontendParsedExpectedLambdaHeaderTests : IO Unit := do
  for text in ["lam(x){return x;}","lam(x,){return x;}","lam(x:A){return x;}","lam(x)->A{return x;}",
      "lam(x:A)->A{return x;}","lam /* keyword */ ( x : (A,) , ) -> (A,) { return x; }"] do
    accepted text types .word .word "x" 0 (some (.var 0,.word))
  accepted "lam(x:A)->B{return x;}" types .word .bool "x" 0 (some (.var 0,.word))
  accepted "lam(x){return x;}" types .word .bool "x" 0 (some (.var 0,.word))
  accepted "lam(x){return;}" types .word .bool "x" 0 (some (.unit,.unit))
  accepted "lam(x){return x;}" types .word (.cell .word) "x" 0 (some (.var 0,.word))
  accepted "lam(x:A)->(){return;}" types .word .unit "x" 0 (some (.unit,.unit))
  accepted "lam(x:(A,B))->(A,B){return x;}" types (.product .word .bool) (.product .word .bool) "x" 0 (some (.var 0,.product .word .bool))
  accepted "lam(x:function(A) returns(B))->function(A) returns(B){return x;}" types (.function .word .bool) (.function .word .bool) "x" 0 (some (.var 0,.function .word .bool))
  accepted "lam(comptime){return comptime;}" types .word .word "comptime" 1 (some (.var 0,.word))
  accepted "lam(comptime:A)->A{return comptime;}" types .word .word "comptime" 1 (some (.var 0,.word))
  for text in ["lam(x){return Missing;}","lam(x){let x:B=saved;return x;}"] do bodyRejected text
  bodyRejected "lam(x){let ;}" 1
  for text in ["lam(){return x;}","lam(x,y){return x;}","lam(x:A,x:A){return x;}",
      "lam(comptime x:A){return x;}","lam(x:B){return x;}","lam(x:Missing){return x;}",
      "lam(x)->B{return x;}","lam(x)->Missing{return x;}","lam(x:@A){return x;}",
      "lam(x)->mapping(A => B){return x;}","lam(x:function(A,B)){return x;}","x"] do
    rejected text (.function .word .word)
  rejected "lam(comptime x){return x;}" (.function .word .word) 1
  for expected in [Core.Ty.unit,.word,.bool,.product .word .bool,.cell .word] do rejected "lam(x){return x;}" expected
  let front : TypeNameTable := (["A"],.bool)::types
  accepted "lam(x:A)->A{return x;}" front .bool .bool "x" 0 (some (.var 0,.bool))
  rejected "lam(x:A)->A{return x;}" (.function .word .word) 0 front
  accepted "lam(x:A)->A{return x;}" (types++[(["A"],.unit),(["New"],.unit)]) .word .word "x" 0 (some (.var 0,.word))
  for lambda in ["lam(x){return x;}","lam(x:A)->A{return x;}","lam(x){return Missing;}"] do wholeRejected lambda
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedExpectedLambdaLetBodies
/-! Original source typing precedes elaboration/checking. The lambda sees the
pre-binder scope; its parameter and the tail binder reuse one fresh ID in disjoint scopes.
The parsed declaration supplies the original block, not a parameter-preparation claim. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedExpectedLambdaLetBodies
private def check (p : Bool) (label : String) : IO Unit := do unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"ExpectedLambdaLet",by decide⟩],by decide⟩⟩,150⟩
private def id (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def base : List LocalTypeBinding := [⟨"saved",id 31,.word⟩,⟨"x",id 20,.word⟩,
  ⟨"c",⟨{owner with declarationIndex:=900},700⟩,.bool⟩]
private def inputs (self : Option Core.Ty) : LocalTypeInputs :=
  match self with
  | none => ⟨base,by decide⟩
  | some t => ⟨⟨"f",id 7,t⟩::base,by change (id 7 :: base.map (fun b => b.id)).Nodup; decide⟩
private def functionType : Core.Ty := .function .word .word
private def types : TypeNameTable := [(["A"],.word),(["B"],.bool),(["F"],functionType),(["F"],.bool)]
private def parsed (statements : String) (returnsClosure : Bool := false) : IO Syntax.FunctionDecl := do
  let text := "function route(f:A,saved:A,x:A,c:B) returns(" ++ (if returnsClosure then "F" else "A") ++ "){" ++ statements ++ "}"
  let file : Syntax.SourceFile := ⟨⟨.main,"expected-lambda-let.sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer invariant")
  match Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file lexed) with
  | .ok source next =>
      check (lexed.diagnostics.isEmpty && next.atEnd && next.diagnostics.isEmpty &&
        decide (source.span=⟨file.id,0,text.utf8ByteSize⟩) && source.span.contains source.value.body.span) "original full source and body range"
      return source
  | .reject _ _ => throw (IO.userError "function parse rejection")
  | .invariant _ => throw (IO.userError "parser invariant")
private structure Meaning (source : Syntax.TypeExpr) where
  type : Core.Ty
  evidence : StructuralTypeDenotes types source type
private def meaning (source : Syntax.TypeExpr) : IO (Meaning source) := do
  match shape : source with
  | ⟨_,.named name none⟩ => match found : types.lookup? (qualifiedTypeNameKey name) with
      | some t => return ⟨t,by rw [shape]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩
      | none => throw (IO.userError "annotation name")
  | ⟨_,.tuple []⟩ => return ⟨.unit,by rw [shape]; exact .unit⟩
  | ⟨_,.tuple [child]⟩ => let c ← meaning child; return ⟨c.type,by rw [shape]; exact .single c.evidence⟩
  | ⟨_,.function _ ⟨_,[parameter]⟩ (some ⟨span,results⟩)⟩ =>
      let a ← meaning parameter; let b ← meaning ⟨span,.tuple results⟩
      return ⟨.function a.type b.type,by rw [shape]; exact .functionReturns a.evidence b.evidence⟩
  | _ => throw (IO.userError "independent annotation profile")
termination_by sizeOf source
private def wellFormed : (t : Core.Ty) → Option (PLift (Core.Ty.WellFormed [] t))
  | .unit => some ⟨.unit⟩ | .bool => some ⟨.bool⟩ | .word => some ⟨.word⟩
  | .function a b => do let p ← wellFormed a; let r ← wellFormed b; return ⟨.function p.down r.down⟩
  | _ => none
private structure Child (i : LocalTypeInputs) (s : Syntax.Expr) where
  type : Core.Ty
  evidence : RecursiveLocalComputationHasType i.names i.context s type
private def child (i : LocalTypeInputs) (s : Syntax.Expr) : IO (Child i s) := do
  match shape : s with
  | ⟨_,.identifier name⟩ => match found : i.names.lookup? name.value with
      | some ident => match typed : i.context.lookup? ident with
          | some t => return ⟨t,by rw [shape]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp found) (Resolved.LocalScope.lookup?_iff.mp typed))⟩
          | none => throw (IO.userError "source type row")
      | none => throw (IO.userError "source name")
  | ⟨_,.group original⟩ => let c ← child i original; return ⟨c.type,by rw [shape]; exact .group c.evidence⟩
  | ⟨_,.call original ⟨_,[arg]⟩⟩ =>
      let f ← child i original; let a ← child i arg
      match ft : f.type with
      | .function p r =>
          if same : a.type=p then return ⟨r,by rw [shape]; exact .application (ft ▸ f.evidence) (same ▸ a.evidence)⟩
          else throw (IO.userError "argument source type")
      | _ => throw (IO.userError "source callable type")
  | _ => throw (IO.userError "independent child profile")
termination_by sizeOf s
private structure Body (i : LocalTypeInputs) (s : Syntax.Block) where
  type : Core.Ty
  evidence : ComputationReturnTreeHasType RecursiveLocalComputationHasType types owner i s type
private def body (i : LocalTypeInputs) (s : Syntax.Block) : IO (Body i s) := do
  match shape : s with
  | ⟨_,[⟨_,.returnStmt none⟩]⟩ => return ⟨.unit,by rw [shape]; exact .bare⟩
  | ⟨_,[⟨_,.returnStmt (some original)⟩]⟩ =>
      let c ← child i original; return ⟨c.type,by rw [shape]; exact .expression c.evidence⟩
  | ⟨_,[⟨span,.block statements⟩]⟩ =>
      let t ← body i ⟨span,statements⟩; return ⟨t.type,by rw [shape]; exact .block t.evidence⟩
  | ⟨span,⟨_,.letDecl name annotation (some original)⟩::rest⟩ =>
      let c ← child i original
      let t ← body (i.bindFresh owner name.value c.type) ⟨span,rest⟩
      match present : annotation with
      | none => return ⟨t.type,by rw [shape,present]; exact .inferred c.evidence t.evidence⟩
      | some annotation =>
          let m ← meaning annotation
          if same : m.type=c.type then return ⟨t.type,by rw [shape,present]; exact .binding (same ▸ m.evidence) c.evidence t.evidence⟩
          else throw (IO.userError "source let type")
  | ⟨span,⟨_,.expression original true⟩::rest⟩ =>
      let c ← child i original; let t ← body i ⟨span,rest⟩
      return ⟨t.type,by rw [shape]; exact .discard c.evidence t.evidence⟩
  | ⟨_,[⟨_,.ifThen condition yes (some no)⟩]⟩ =>
      let c ← child i condition; let t ← body i yes; let f ← body i no
      match barrier : yes with
      | ⟨_,[⟨_,.block _⟩]⟩ =>
          have protects : ComputationNamesProtected (i.names.map Prod.fst) yes := by
            intro name exposed; rw [barrier] at exposed; cases exposed with | tail impossible => cases impossible
          if same : c.type=.bool ∧ f.type=t.type then return ⟨t.type,by rw [shape]; exact .conditional (same.1 ▸ c.evidence) protects t.evidence (same.2 ▸ f.evidence)⟩
          else throw (IO.userError "original branch types")
      | _ => throw (IO.userError "explicit source scope barrier")
  | _ => throw (IO.userError "independent body profile")
termination_by sizeOf s
private def lambdaTyped (i : LocalTypeInputs) (s : Syntax.Expr) (a b : Core.Ty) :
    IO (PLift (ExpectedComputationLambdaHasType RecursiveLocalComputationHasType types owner i s (.function a b))) := do
  match shape : s with
  | ⟨span,.lambda keyword ⟨ps,[parameter]⟩ returns original⟩ =>
      check (span.contains keyword && span.contains ps && ps.contains parameter.span && span.contains original.span) "unchanged lambda header and body ranges"
      let ⟨name,parameterProof⟩ : Σ name,PLift (ExpectedLambdaParameterDeclares types owner i parameter a (i.bindFresh owner name a)) ←
        match pshape : parameter with
        | ⟨_,.inferred name⟩ => pure ⟨name.value,⟨by rw [pshape]; exact .inferred⟩⟩
        | ⟨_,.typed none name annotation⟩ => do
            let m ← meaning annotation
            if same : m.type=a then pure ⟨name.value,⟨by rw [pshape]; exact .typed (same ▸ m.evidence)⟩⟩
            else throw (IO.userError "lambda domain annotation")
        | _ => throw (IO.userError "lambda parameter shape")
      let returnProof : PLift (ExpectedLambdaReturnDenotes types returns b) ← match present : returns with
        | none => pure ⟨by rw [present]; exact .omitted⟩
        | some annotation => do
            let m ← meaning annotation
            if same : m.type=b then pure ⟨by rw [present]; exact .annotated (same ▸ m.evidence)⟩
            else throw (IO.userError "lambda codomain annotation")
      let inner := i.bindFresh owner name a
      check (decide (inner.names=(name,Resolved.freshLocalId owner i.ids)::i.names ∧
        inner.context=(Resolved.freshLocalId owner i.ids,a)::i.context)) "parameter extends only its old-scope inputs"
      let t ← body inner original
      let some aw := wellFormed a | throw (IO.userError "domain guard")
      let some bw := wellFormed b | throw (IO.userError "codomain guard")
      if same : t.type=b then return ⟨by
        rw [shape]; exact .lambda (.lambda parameterProof.down returnProof.down) aw.down bw.down (same ▸ t.evidence)⟩
      else throw (IO.userError "original lambda body type")
  | _ => throw (IO.userError "original unary lambda head")
private structure Original (i : LocalTypeInputs) (s : Syntax.Block) where
  type : Core.Ty
  evidence : ExpectedLambdaLetBodyHasType RecursiveLocalComputationHasType types owner i s type
private def original (i : LocalTypeInputs) (s : Syntax.Block) : IO (Original i s) := do
  match shape : s with
  | ⟨span,⟨headSpan,.letDecl name (some annotation) (some init)⟩::rest⟩ =>
      check (span.contains headSpan && headSpan.contains annotation.span && headSpan.contains init.span &&
        decide (annotation.span.endByte≤init.span.startByte) && rest.all (fun stmt => span.contains stmt.span)) "exact original typed head and tail ranges"
      let m ← meaning annotation
      match mt : m.type with
      | .function a b =>
          let initializer ← lambdaTyped i init a b
          let tailInputs := i.bindFresh owner name.value (.function a b)
          let tail ← body tailInputs ⟨span,rest⟩
          check (decide (tailInputs.names=(name.value,Resolved.freshLocalId owner i.ids)::i.names ∧
            tailInputs.context=(Resolved.freshLocalId owner i.ids,.function a b)::i.context)) "tail does not inherit the initializer parameter row"
          return ⟨tail.type,by rw [shape]; exact .binding (mt ▸ m.evidence) initializer.down tail.evidence⟩
      | _ => throw (IO.userError "explicit expected function type")
  | _ => throw (IO.userError "original typed lambda-let head")
private def oldRejected (declaration : Syntax.FunctionDecl) (i : LocalTypeInputs) : IO Unit := do
  check (elaborateComputationReturnTree? elaborateRecursiveLocalComputation? types owner i declaration.value.body).isNone "old shared checker sees the same complete original block"
  check (compileComputationFunction? elaborateRecursiveLocalComputation? types owner declaration).isNone "old function entry sees the same original declaration"
private def accepted (text : String) (self : Option Core.Ty) (expected : Core.Ty) : IO Unit := do
  let declaration ← parsed text (expected == functionType)
  let i := inputs self
  let typed ← original i declaration.value.body
  check (decide (typed.type=expected)) "independent source result type"
  have elaborates := (expectedLambdaLetBodyHasType_iff_elaborates recursiveLocalComputationHasType_iff_elaborates).mp typed.evidence
  have checked := (expectedLambdaLetBodyHasType_iff_checked recursiveLocalComputationHasType_iff_elaborates elaborateRecursiveLocalComputation?_iff).mp typed.evidence
  have _ := (expectedLambdaLetBodyHasType_iff_elaborates recursiveLocalComputationHasType_iff_elaborates).mpr elaborates
  have _ := (expectedLambdaLetBodyHasType_iff_checked recursiveLocalComputationHasType_iff_elaborates elaborateRecursiveLocalComputation?_iff).mpr checked
  have present : (elaborateExpectedLambdaLetBody? elaborateRecursiveLocalComputation? types owner i declaration.value.body).isSome=true := by
    obtain ⟨core,found⟩ := checked; rw [found]; rfl
  have _ := present
  match found : elaborateExpectedLambdaLetBody? elaborateRecursiveLocalComputation? types owner i declaration.value.body with
  | some result =>
      have evidence := (elaborateExpectedLambdaLetBody?_iff elaborateRecursiveLocalComputation?_iff).mp found
      have _ := (elaborateExpectedLambdaLetBody?_iff elaborateRecursiveLocalComputation?_iff).mpr evidence
      have _ := evidence.core_hasType (fun e => e.core_hasType)
      have _ := evidence.provenance
      check (decide (result.2=expected)) "checker result only after original source typing"
  | none => throw (IO.userError "source-typed body rejected")
  oldRejected declaration i
private def rejected (text : String) (self : Option Core.Ty) (ordinary : Bool := false) : IO Unit := do
  let declaration ← parsed text
  if ordinary then
    let typed ← body (inputs self) declaration.value.body
    have present : (elaborateComputationReturnTree? elaborateRecursiveLocalComputation? types owner (inputs self) declaration.value.body).isSome=true := by
      obtain ⟨core,evidence⟩ := (computationReturnTreeHasType_iff_elaborates recursiveLocalComputationHasType_iff_elaborates).mp typed.evidence
      rw [(elaborateComputationReturnTree?_iff elaborateRecursiveLocalComputation?_iff).mpr evidence]; rfl
    have _ := present
    check (elaborateComputationReturnTree? elaborateRecursiveLocalComputation? types owner (inputs self) declaration.value.body).isSome "well-typed ordinary nonlambda head stays in the old profile"
  if absent : elaborateExpectedLambdaLetBody? elaborateRecursiveLocalComputation? types owner (inputs self) declaration.value.body=none then
    have noElab := (elaborateExpectedLambdaLetBody?_eq_none_iff elaborateRecursiveLocalComputation?_iff).mp absent
    have _ := (elaborateExpectedLambdaLetBody?_eq_none_iff elaborateRecursiveLocalComputation?_iff).mpr noElab
    have noTyping : ∀ type,¬ExpectedLambdaLetBodyHasType RecursiveLocalComputationHasType types owner (inputs self) declaration.value.body type := by
      intro type typed
      obtain ⟨core,evidence⟩ := (expectedLambdaLetBodyHasType_iff_elaborates recursiveLocalComputationHasType_iff_elaborates).mp typed
      exact noElab ⟨core,type,evidence⟩
    have _ := noTyping
  else throw (IO.userError "outside opt-in profile accepted")
private def scopes : IO Unit := do
  let i := inputs (some .word)
  let inner := i.bindFresh owner "x" .word
  let tail := i.bindFresh owner "f" functionType
  check (decide (inner.names.lookup? "f"=some (id 7) ∧ inner.names.lookup? "x"=some (id 32) ∧
    tail.names.lookup? "f"=some (id 32) ∧ tail.names.lookup? "x"=some (id 20))) "same fresh 32 reused in separate scopes with different meanings"
  check (decide (inner.context.lookup? (id 7)=some .word ∧ tail.context.lookup? (id 32)=some functionType ∧
    types.lookup? ["F"]=some functionType)) "old self payload type and first-match alias retained"
end ParsedExpectedLambdaLetBodies
open ParsedExpectedLambdaLetBodies
def frontendParsedExpectedLambdaLetBodyTests : IO Unit := do
  scopes
  for text in ["let f:F=lam(x){return f;};return f(x);",
      "let f:F=lam(x:A)->A{return f;};return f(x);",
      "let f:F=lam(f){return f;};return f(x);",
      "let f:function(A) returns(A)=lam(x:A)->A{let x:A=x;return saved;};let y:A=f(x);let y=y;if(c){{let f=y;return f;}}else{return f(y);}",
      "let f:F=lam(x){return saved;};f(x);return f(x);"] do accepted text (some .word) .word
  accepted "let f:F=lam(x){return f;};return f;" (some .word) functionType
  accepted "let f:F=lam(x){return f(x);};return f(x);" (some functionType) .word
  accepted "let f:F=lam(x){return x;};return f(x);" none .word
  for self in [none,some .word,some .bool] do rejected "let f:F=lam(x){return f(x);};return f(x);" self
  rejected "let f:F=lam(x){return f;};return f(x);" none
  rejected "let f:A=x;return f;" (some .word) true
  for text in ["let f=lam(x){return x;};return f(x);","let f:F;return x;",
      "let f:Missing=lam(x){return x;};return f;","let f:A=lam(x){return x;};return f;",
      "let f:F=lam(){return saved;};return f(x);","let f:F=lam(x,y){return x;};return f(x);",
      "let f:F=lam(x:B){return saved;};return f(x);","let f:F=lam(x)->B{return c;};return f(x);",
      "let f:F=lam(x){return c;};return f(x);","let f:F=lam(x){return Missing;};return f(x);",
      "let f:F=lam(x){return x;};let g:F=lam(y){return y;};return f(x);",
      "let f:F=lam(x){return x;};if(c){{return f(x);}}else{return Missing;}",
      "let f:F=lam(x){return x;};if(c){let f=x;return f;}else{return f(x);}"] do rejected text (some .word)
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedExpectedLambdaLetSpines
/-! Every original prefix head is source-typed before elaboration/checking.
At the first non-head, the complete original remainder is typed by the shared body.
The parsed declaration supplies the original block, not a parameter-preparation claim. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedExpectedLambdaLetSpines
private def check (p : Bool) (label : String) : IO Unit := do unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"ExpectedLambdaSpine",by decide⟩],by decide⟩⟩,151⟩
private def id (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def base : List LocalTypeBinding := [⟨"saved",id 31,.word⟩,⟨"x",id 20,.word⟩,
  ⟨"c",⟨{owner with declarationIndex:=900},700⟩,.bool⟩]
private def inputs (self : Option Core.Ty) : LocalTypeInputs :=
  match self with
  | none => ⟨base,by decide⟩
  | some t => ⟨⟨"f",id 7,t⟩::base,by change (id 7 :: base.map (fun b => b.id)).Nodup; decide⟩
private def functionType : Core.Ty := .function .word .word
private def higherType : Core.Ty := .function functionType .word
private def types : TypeNameTable := [(["A"],.word),(["B"],.bool),(["F"],functionType),
  (["H"],higherType),(["F"],.bool),(["H"],.bool)]
private def parsed (statements : String) (returnsClosure : Bool := false) (diagnostics : Nat := 0) : IO Syntax.FunctionDecl := do
  let text := "function route(f:A,saved:A,x:A,c:B) returns(" ++ (if returnsClosure then "F" else "A") ++ "){" ++ statements ++ "}"
  let file : Syntax.SourceFile := ⟨⟨.main,"expected-lambda-spine.sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer invariant")
  match Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file lexed) with
  | .ok source next =>
      check (lexed.diagnostics.isEmpty && next.atEnd &&
        decide (next.diagnostics.length=diagnostics ∧ source.span=⟨file.id,0,text.utf8ByteSize⟩) &&
        source.span.contains source.value.body.span) "original full source, diagnostics and body range"
      return source
  | .reject _ _ => throw (IO.userError "function parse rejection")
  | .invariant _ => throw (IO.userError "parser invariant")
private structure Meaning (source : Syntax.TypeExpr) where
  type : Core.Ty
  evidence : StructuralTypeDenotes types source type
private def meaning (source : Syntax.TypeExpr) : IO (Meaning source) := do
  match shape : source with
  | ⟨_,.named name none⟩ => match found : types.lookup? (qualifiedTypeNameKey name) with
      | some t => return ⟨t,by rw [shape]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩
      | none => throw (IO.userError "annotation name")
  | ⟨_,.tuple []⟩ => return ⟨.unit,by rw [shape]; exact .unit⟩
  | ⟨_,.tuple [child]⟩ => let c ← meaning child; return ⟨c.type,by rw [shape]; exact .single c.evidence⟩
  | ⟨_,.function _ ⟨_,[parameter]⟩ (some ⟨span,results⟩)⟩ =>
      let a ← meaning parameter; let b ← meaning ⟨span,.tuple results⟩
      return ⟨.function a.type b.type,by rw [shape]; exact .functionReturns a.evidence b.evidence⟩
  | _ => throw (IO.userError "independent annotation profile")
termination_by sizeOf source
private def wellFormed : (t : Core.Ty) → Option (PLift (Core.Ty.WellFormed [] t))
  | .unit => some ⟨.unit⟩ | .bool => some ⟨.bool⟩ | .word => some ⟨.word⟩
  | .function a b => do let p ← wellFormed a; let r ← wellFormed b; return ⟨.function p.down r.down⟩
  | _ => none
private structure Child (i : LocalTypeInputs) (s : Syntax.Expr) where
  type : Core.Ty
  evidence : RecursiveLocalComputationHasType i.names i.context s type
private def child (i : LocalTypeInputs) (s : Syntax.Expr) : IO (Child i s) := do
  match shape : s with
  | ⟨_,.identifier name⟩ => match found : i.names.lookup? name.value with
      | some ident => match typed : i.context.lookup? ident with
          | some t => return ⟨t,by rw [shape]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp found) (Resolved.LocalScope.lookup?_iff.mp typed))⟩
          | none => throw (IO.userError "source type row")
      | none => throw (IO.userError "source name")
  | ⟨_,.group original⟩ => let c ← child i original; return ⟨c.type,by rw [shape]; exact .group c.evidence⟩
  | ⟨_,.call original ⟨_,[arg]⟩⟩ =>
      let f ← child i original; let a ← child i arg
      match ft : f.type with
      | .function p r =>
          if same : a.type=p then return ⟨r,by rw [shape]; exact .application (ft ▸ f.evidence) (same ▸ a.evidence)⟩
          else throw (IO.userError "argument source type")
      | _ => throw (IO.userError "source callable type")
  | _ => throw (IO.userError "independent child profile")
termination_by sizeOf s
private structure Body (i : LocalTypeInputs) (s : Syntax.Block) where
  type : Core.Ty
  evidence : ComputationReturnTreeHasType RecursiveLocalComputationHasType types owner i s type
private def body (i : LocalTypeInputs) (s : Syntax.Block) : IO (Body i s) := do
  match shape : s with
  | ⟨_,[⟨_,.returnStmt none⟩]⟩ => return ⟨.unit,by rw [shape]; exact .bare⟩
  | ⟨_,[⟨_,.returnStmt (some original)⟩]⟩ =>
      let c ← child i original; return ⟨c.type,by rw [shape]; exact .expression c.evidence⟩
  | ⟨_,[⟨span,.block statements⟩]⟩ =>
      let t ← body i ⟨span,statements⟩; return ⟨t.type,by rw [shape]; exact .block t.evidence⟩
  | ⟨span,⟨_,.letDecl name annotation (some original)⟩::rest⟩ =>
      let c ← child i original
      let t ← body (i.bindFresh owner name.value c.type) ⟨span,rest⟩
      match present : annotation with
      | none => return ⟨t.type,by rw [shape,present]; exact .inferred c.evidence t.evidence⟩
      | some annotation =>
          let m ← meaning annotation
          if same : m.type=c.type then return ⟨t.type,by rw [shape,present]; exact .binding (same ▸ m.evidence) c.evidence t.evidence⟩
          else throw (IO.userError "source let type")
  | ⟨span,⟨_,.expression original true⟩::rest⟩ =>
      let c ← child i original; let t ← body i ⟨span,rest⟩
      return ⟨t.type,by rw [shape]; exact .discard c.evidence t.evidence⟩
  | ⟨_,[⟨_,.ifThen condition yes (some no)⟩]⟩ =>
      let c ← child i condition; let t ← body i yes; let f ← body i no
      match barrier : yes with
      | ⟨_,[⟨_,.block _⟩]⟩ =>
          have protects : ComputationNamesProtected (i.names.map Prod.fst) yes := by
            intro name exposed; rw [barrier] at exposed; cases exposed with | tail impossible => cases impossible
          if same : c.type=.bool ∧ f.type=t.type then return ⟨t.type,by rw [shape]; exact .conditional (same.1 ▸ c.evidence) protects t.evidence (same.2 ▸ f.evidence)⟩
          else throw (IO.userError "original branch types")
      | _ => throw (IO.userError "explicit source scope barrier")
  | _ => throw (IO.userError "independent body profile")
termination_by sizeOf s
private def lambdaTyped (i : LocalTypeInputs) (s : Syntax.Expr) (a b : Core.Ty) :
    IO (PLift (ExpectedComputationLambdaHasType RecursiveLocalComputationHasType types owner i s (.function a b))) := do
  match shape : s with
  | ⟨span,.lambda keyword ⟨ps,[parameter]⟩ returns original⟩ =>
      check (span.contains keyword && span.contains ps && ps.contains parameter.span && span.contains original.span) "unchanged lambda header and body ranges"
      let ⟨name,parameterProof⟩ : Σ name,PLift (ExpectedLambdaParameterDeclares types owner i parameter a (i.bindFresh owner name a)) ←
        match pshape : parameter with
        | ⟨_,.inferred name⟩ => pure ⟨name.value,⟨by rw [pshape]; exact .inferred⟩⟩
        | ⟨_,.typed none name annotation⟩ => do
            let m ← meaning annotation
            if same : m.type=a then pure ⟨name.value,⟨by rw [pshape]; exact .typed (same ▸ m.evidence)⟩⟩
            else throw (IO.userError "lambda domain annotation")
        | _ => throw (IO.userError "lambda parameter shape")
      let returnProof : PLift (ExpectedLambdaReturnDenotes types returns b) ← match present : returns with
        | none => pure ⟨by rw [present]; exact .omitted⟩
        | some annotation => do
            let m ← meaning annotation
            if same : m.type=b then pure ⟨by rw [present]; exact .annotated (same ▸ m.evidence)⟩
            else throw (IO.userError "lambda codomain annotation")
      let inner := i.bindFresh owner name a
      check (decide (inner.names=(name,Resolved.freshLocalId owner i.ids)::i.names ∧
        inner.context=(Resolved.freshLocalId owner i.ids,a)::i.context)) "parameter extends only its old-scope inputs"
      let t ← body inner original
      let some aw := wellFormed a | throw (IO.userError "domain guard")
      let some bw := wellFormed b | throw (IO.userError "codomain guard")
      if same : t.type=b then return ⟨by
        rw [shape]; exact .lambda (.lambda parameterProof.down returnProof.down) aw.down bw.down (same ▸ t.evidence)⟩
      else throw (IO.userError "original lambda body type")
  | _ => throw (IO.userError "original unary lambda head")
private structure Original (i : LocalTypeInputs) (s : Syntax.Block) where
  heads : Nat
  type : Core.Ty
  evidence : ExpectedLambdaLetSpineHasType RecursiveLocalComputationHasType types owner i s type
private def original (i : LocalTypeInputs) (s : Syntax.Block) : IO (Original i s) := do
  if boundary : isExpectedLambdaLetHead s=false then
    let terminal ← body i s
    return ⟨0,terminal.type,.terminal boundary terminal.evidence⟩
  else
  have head : isExpectedLambdaLetHead s=true := by cases found : isExpectedLambdaLetHead s <;> simp_all
  match shape : s with
  | ⟨span,⟨headSpan,.letDecl name (some annotation) (some init)⟩::rest⟩ =>
      check (span.contains headSpan && headSpan.contains annotation.span && headSpan.contains init.span &&
        decide (annotation.span.endByte≤init.span.startByte) && rest.all (fun stmt => span.contains stmt.span)) "exact original typed head and tail ranges"
      let m ← meaning annotation
      match mt : m.type with
      | .function a b =>
          let initializer ← lambdaTyped i init a b
          let tailInputs := i.bindFresh owner name.value (.function a b)
          let tail ← original tailInputs ⟨span,rest⟩
          check (decide (tailInputs.names=(name.value,Resolved.freshLocalId owner i.ids)::i.names ∧
            tailInputs.context=(Resolved.freshLocalId owner i.ids,.function a b)::i.context)) "tail does not inherit the initializer parameter row"
          return ⟨tail.heads+1,tail.type,by rw [shape]; exact .binding (by simpa only [shape] using head) (mt ▸ m.evidence) initializer.down tail.evidence⟩
      | _ => throw (IO.userError "explicit expected function type")
  | _ => throw (IO.userError "original typed lambda-let head")
termination_by sizeOf s
private def oldRejected (declaration : Syntax.FunctionDecl) (i : LocalTypeInputs) : IO Unit := do
  check (elaborateComputationReturnTree? elaborateRecursiveLocalComputation? types owner i declaration.value.body).isNone "old shared checker sees the same complete original block"
  check (compileComputationFunction? elaborateRecursiveLocalComputation? types owner declaration).isNone "old function entry sees the same original declaration"
private def accepted (text : String) (self : Option Core.Ty) (expected : Core.Ty) (heads : Nat) (diagnostics : Nat := 0) : IO Unit := do
  let declaration ← parsed text (expected == functionType) diagnostics
  let i := inputs self
  let typed ← original i declaration.value.body
  check (decide (typed.type=expected ∧ typed.heads=heads)) "independent complete source type and original prefix length"
  have elaborates := (expectedLambdaLetSpineHasType_iff_elaborates recursiveLocalComputationHasType_iff_elaborates).mp typed.evidence
  have checked := (expectedLambdaLetSpineHasType_iff_checked recursiveLocalComputationHasType_iff_elaborates elaborateRecursiveLocalComputation?_iff).mp typed.evidence
  have _ := (expectedLambdaLetSpineHasType_iff_elaborates recursiveLocalComputationHasType_iff_elaborates).mpr elaborates
  have _ := (expectedLambdaLetSpineHasType_iff_checked recursiveLocalComputationHasType_iff_elaborates elaborateRecursiveLocalComputation?_iff).mpr checked
  have present : (elaborateExpectedLambdaLetSpine? elaborateRecursiveLocalComputation? types owner i declaration.value.body).isSome=true := by
    obtain ⟨core,found⟩ := checked; rw [found]; rfl
  have _ := present
  match found : elaborateExpectedLambdaLetSpine? elaborateRecursiveLocalComputation? types owner i declaration.value.body with
  | some result =>
      have evidence := (elaborateExpectedLambdaLetSpine?_iff elaborateRecursiveLocalComputation?_iff).mp found
      have _ := (elaborateExpectedLambdaLetSpine?_iff elaborateRecursiveLocalComputation?_iff).mpr evidence
      have _ := evidence.core_hasType (fun e => e.core_hasType)
      have _ := evidence.provenance
      check (decide (result.2=expected)) "checker result only after original source typing"
  | none => throw (IO.userError "source-typed body rejected")
  if heads=0 then
    check (elaborateComputationReturnTree? elaborateRecursiveLocalComputation? types owner i declaration.value.body).isSome "zero heads retains the whole shared body"
  else oldRejected declaration i
private def rejected (text : String) (self : Option Core.Ty) (head : Bool := true) (diagnostics : Nat := 0) (marked : Bool := false) : IO Unit := do
  let declaration ← parsed text false diagnostics
  check (isExpectedLambdaLetHead declaration.value.body == head) "source-only boundary ignores later statements, header validity and diagnostics"
  if marked || diagnostics>0 then
    let ⟨_,.letDecl _ _ (some ⟨_,.lambda _ ⟨_,[parameter]⟩ _ _⟩)⟩::_ := declaration.value.body.value | throw (IO.userError "actual rejected parameter shape")
    check (match parameter.value with
      | .typed (some _) _ _ => marked | .error => !marked && diagnostics>0 | _ => false)
      "explicit comptime marker versus recovered error parameter, not a spelling blacklist"
  if absent : elaborateExpectedLambdaLetSpine? elaborateRecursiveLocalComputation? types owner (inputs self) declaration.value.body=none then
    have noElab := (elaborateExpectedLambdaLetSpine?_eq_none_iff elaborateRecursiveLocalComputation?_iff).mp absent
    have _ := (elaborateExpectedLambdaLetSpine?_eq_none_iff elaborateRecursiveLocalComputation?_iff).mpr noElab
    have noTyping : ∀ type,¬ExpectedLambdaLetSpineHasType RecursiveLocalComputationHasType types owner (inputs self) declaration.value.body type := by
      intro type typed
      obtain ⟨core,evidence⟩ := (expectedLambdaLetSpineHasType_iff_elaborates recursiveLocalComputationHasType_iff_elaborates).mp typed
      exact noElab ⟨core,type,evidence⟩
    have _ := noTyping
  else throw (IO.userError "outside opt-in profile accepted")
private def scopes : IO Unit := do
  let i := inputs (some .word)
  let first := i.bindFresh owner "f" functionType
  let second := first.bindFresh owner "f" functionType
  let third := second.bindFresh owner "h" higherType
  let inner1 := i.bindFresh owner "x" .word
  let inner2 := first.bindFresh owner "x" .word
  let inner3 := second.bindFresh owner "k" functionType
  check (decide (inner1.names.lookup? "f"=some (id 7) ∧ inner2.names.lookup? "f"=some (id 32) ∧
    inner3.names.lookup? "f"=some (id 33) ∧ third.names.lookup? "h"=some (id 34) ∧
    first.ids=inner1.ids ∧ second.ids=inner2.ids ∧ third.ids=inner3.ids ∧
    third.names.lookup? "x"=some (id 20))) "successive fresh 32/33/34 are reused only in disjoint parameter/tail scopes"
  check (decide (types.lookup? ["F"]=some functionType ∧ types.lookup? ["H"]=some higherType)) "heterogeneous first-match aliases"
end ParsedExpectedLambdaLetSpines
open ParsedExpectedLambdaLetSpines
def frontendParsedExpectedLambdaLetSpineTests : IO Unit := do
  scopes
  for text in ["return x;","let y:A=x;let y=y;return y;"] do accepted text (some .word) .word 0
  for text in ["let f:F=lam(x){return f;};return f(x);",
      "let f:F=lam(x:A)->A{return f;};return f(x);",
      "let f:F=lam(f){return f;};return f(x);",
      "let f:function(A) returns(A)=lam(x:A)->A{let x:A=x;return saved;};let y:A=f(x);let y=y;if(c){{let f=y;return f;}}else{return f(y);}",
      "let f:F=lam(x){return saved;};f(x);return f(x);"] do accepted text (some .word) .word 1
  accepted "let f:F=lam(x){return f;};return f;" (some .word) functionType 1
  accepted "let f:F=lam(x){return f(x);};return f(x);" (some functionType) .word 1
  accepted "let f:F=lam(x){return x;};return f(x);" none .word 1
  accepted "let f:F=lam(x){return f;};let f:F=lam(x:A)->A{return f(x);};return f(x);" (some .word) .word 2
  accepted "let f:F=lam(f){return f;};let g:F=lam(f){return f;};return g(x);" none .word 2
  accepted "let f:F=lam(x){return f;};let f:F=lam(x:A)->A{return f(x);};let h:H=lam(k:F)->A{return k(x);};return h(f);" (some .word) .word 3
  accepted "let f:F=lam(comptime){return comptime;};return f(x);" none .word 1 1
  for self in [none,some .word,some .bool] do rejected "let f:F=lam(x){return f(x);};return f(x);" self
  rejected "let f:F=lam(x){return f;};return f(x);" none
  for text in ["let f=lam(x){return x;};return f(x);","let f:F;return x;",
      "let f:F=(lam(x){return x;});return f(x);",
      "let y:A=x;let f:F=lam(z){return z;};return f(y);"] do rejected text (some .word) false
  for text in ["let f:Missing=lam(x){return x;};return f;","let f:A=lam(x){return x;};return f;",
      "let f:F=lam(){return saved;};return f(x);","let f:F=lam(x,y){return x;};return f(x);",
      "let f:F=lam(x:B){return saved;};return f(x);","let f:F=lam(x)->B{return c;};return f(x);",
      "let f:F=lam(x){return c;};return f(x);","let f:F=lam(x){return Missing;};return f(x);",
      "let f:F=lam(x){return g(x);};let g:F=lam(y){return y;};return f(x);",
      "let f:F=lam(x){return x;};let y:A=f(x);let g:F=lam(z){return z;};return g(y);",
      "let f:F=lam(x){return x;};let g:F=(lam(z){return z;});return g(x);",
      "let f:F=lam(x){return x;};if(c){{return f(x);}}else{return Missing;}",
      "let f:F=lam(x){return x;};if(c){let f=x;return f;}else{return f(x);}"] do rejected text (some .word)
  rejected "let f:F=lam(comptime x:A){return x;};return f(x);" (some .word) true 0 true
  rejected "let f:F=lam(comptime x){return x;};return f;" (some .word) true 1
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedExpectedLambdaTyping
/-! Original source typing is constructed before either existence theorem or
checker is used. The body certificates contain no Core terms or positional indices. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedExpectedLambdaTyping
private def check (p : Bool) (label : String) : IO Unit := do unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"ExpectedLambdaTyping",by decide⟩],by decide⟩⟩,148⟩
private def id (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def foreign : Resolved.LocalId := ⟨{owner with declarationIndex:=900},700⟩
private def outer : LocalTypeInputs := ⟨[⟨"x",id 7,.bool⟩,⟨"saved",id 31,.word⟩,
  ⟨"c",foreign,.bool⟩,⟨"f",id 20,.function .word .word⟩],by decide⟩
private def types : TypeNameTable := [(["A"],.word),(["B"],.bool),(["A"],.bool),
  (["C"],.cell (.function .word .word))]
private def file (text : String) : Syntax.SourceFile := ⟨⟨.main,"expected-lambda-typing.sol"⟩,text⟩
private def parsed (text : String) (diagnostics : Nat := 0) : IO Syntax.Expr := do
  let .ok lexed := Syntax.Lexer.lex (file text) | throw (IO.userError "lexer invariant")
  match Syntax.Parser.expression (Syntax.Parser.State.initial (file text) lexed) with
  | .ok source next =>
      check (lexed.diagnostics.isEmpty && next.atEnd && decide (next.diagnostics.length=diagnostics ∧
        source.span=⟨(file text).id,0,text.utf8ByteSize⟩)) "complete original lambda and retained diagnostics"
      return source
  | .reject _ _ => throw (IO.userError "source rejected")
  | .invariant _ => throw (IO.userError "parser invariant")
private structure Meaning (source : Syntax.TypeExpr) where
  type : Core.Ty
  evidence : StructuralTypeDenotes types source type
private def meaning (source : Syntax.TypeExpr) : IO (Meaning source) := do
  match shape : source with
  | ⟨_,.named name none⟩ => match found : types.lookup? (qualifiedTypeNameKey name) with
      | some type => return ⟨type,by rw [shape]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩
      | none => throw (IO.userError "annotation name")
  | ⟨_,.tuple []⟩ => return ⟨.unit,by rw [shape]; exact .unit⟩
  | ⟨_,.tuple [child]⟩ => let a ← meaning child; return ⟨a.type,by rw [shape]; exact .single a.evidence⟩
  | ⟨_,.tuple [left,right]⟩ =>
      let a ← meaning left; let b ← meaning right
      return ⟨.product a.type b.type,by rw [shape]; exact .pair a.evidence b.evidence⟩
  | _ => throw (IO.userError "independent annotation profile")
termination_by sizeOf source
private def wellFormed : (t : Core.Ty) → Option (PLift (Core.Ty.WellFormed [] t))
  | .unit => some ⟨.unit⟩ | .bool => some ⟨.bool⟩ | .word => some ⟨.word⟩ | .integer => some ⟨.integer⟩
  | .product a b => do let p ← wellFormed a; let r ← wellFormed b; return ⟨.product p.down r.down⟩
  | .function a b => do let p ← wellFormed a; let r ← wellFormed b; return ⟨.function p.down r.down⟩
  | .sum a b => do let p ← wellFormed a; let r ← wellFormed b; return ⟨.sum p.down r.down⟩
  | .cell a => do let p ← wellFormed a; return ⟨.cell p.down⟩
  | .namedData _ => none
private structure Header (source : Syntax.Expr) (a b : Core.Ty) where
  name : String
  body : Syntax.Block
  evidence : ExpectedUnaryLambdaHeaderDeclares types owner outer source (.function a b)
    ⟨outer.bindFresh owner name a,body,a,b⟩
private def header (source : Syntax.Expr) (a b : Core.Ty) : IO (Header source a b) := do
  match shape : source with
  | ⟨span,.lambda keyword ⟨ps,[parameter]⟩ returns body⟩ =>
      check (span.contains keyword && span.contains ps && ps.contains parameter.span && span.contains body.span &&
        decide (keyword.endByte≤ps.startByte ∧ ps.endByte≤body.span.startByte)) "original header/body ranges and order"
      let ⟨name,parameterProof⟩ : Σ name,PLift (ExpectedLambdaParameterDeclares types owner outer parameter a (outer.bindFresh owner name a)) ←
        match pshape : parameter with
        | ⟨_,.inferred name⟩ => pure ⟨name.value,⟨by rw [pshape]; exact .inferred⟩⟩
        | ⟨_,.typed none name annotation⟩ => do
            let m ← meaning annotation
            if same : m.type=a then pure ⟨name.value,⟨by rw [pshape]; exact .typed (same ▸ m.evidence)⟩⟩
            else throw (IO.userError "header domain mismatch")
        | _ => throw (IO.userError "header parameter shape")
      match present : returns with
      | none => return ⟨name,body,by rw [shape,present]; exact .lambda parameterProof.down .omitted⟩
      | some annotation =>
          let m ← meaning annotation
          if same : m.type=b then return ⟨name,body,by rw [shape,present]; exact .lambda parameterProof.down (.annotated (same ▸ m.evidence))⟩
          else throw (IO.userError "header codomain mismatch")
  | _ => throw (IO.userError "header source profile")
private structure Child (inputs : LocalTypeInputs) (source : Syntax.Expr) where
  type : Core.Ty
  evidence : RecursiveLocalComputationHasType inputs.names inputs.context source type
private def child (inputs : LocalTypeInputs) (source : Syntax.Expr) : IO (Child inputs source) := do
  match shape : source with
  | ⟨_,.identifier name⟩ => match named : inputs.names.lookup? name.value with
      | some i => match typed : inputs.context.lookup? i with
          | some t => return ⟨t,by rw [shape]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp typed))⟩
          | none => throw (IO.userError "source typing row")
      | none => throw (IO.userError "source name")
  | ⟨span,.group inner⟩ =>
      check (span.contains inner.span) "original expression group"
      let c ← child inputs inner; return ⟨c.type,by rw [shape]; exact .group c.evidence⟩
  | ⟨span,.call callee ⟨args,[argument]⟩⟩ =>
      check (span.contains callee.span && span.contains args && args.contains argument.span) "original call children"
      let f ← child inputs callee; let a ← child inputs argument
      match ft : f.type with
      | .function p r =>
          if same : a.type=p then return ⟨r,by rw [shape]; exact .application (ft ▸ f.evidence) (same ▸ a.evidence)⟩
          else throw (IO.userError "source argument type")
      | _ => throw (IO.userError "source callable type")
  | _ => throw (IO.userError "independent child typing profile")
termination_by sizeOf source
private structure Pattern (source : Syntax.Pattern) where
  tag : Option Core.Word
  evidence : WordMatchPatternClassifies source tag
private def pattern (source : Syntax.Pattern) : IO (Pattern source) := do
  match shape : source with
  | ⟨_,.wildcard _⟩ => return ⟨none,by rw [shape]; exact .wildcard rfl⟩
  | ⟨_,.literal literal⟩ =>
      if zero : literal.value=.decimal "0" then
        return ⟨some Core.Word.zero,by
          rw [shape]; refine .literal ⟨literal,rfl,?_⟩
          change NumericLiteralDenotes literal.value 0; rw [zero]
          exact .decimal (by decide) (.cons (.decimal (digit:=0) (by decide) rfl) .nil)⟩
      else throw (IO.userError "original fixture literal")
  | ⟨span,.group inner⟩ =>
      check (span.contains inner.span && decide (span.startByte<inner.span.startByte ∧ inner.span.endByte<span.endByte)) "original pattern group ranges"
      let c ← pattern inner; return ⟨c.tag,by rw [shape]; exact .group c.evidence⟩
  | _ => throw (IO.userError "original pattern profile")
termination_by sizeOf source
private structure Body (inputs : LocalTypeInputs) (source : Syntax.Block) where
  type : Core.Ty
  evidence : ComputationReturnTreeHasType RecursiveLocalComputationHasType types owner inputs source type
private def body (inputs : LocalTypeInputs) (source : Syntax.Block) : IO (Body inputs source) := do
  match shape : source with
  | ⟨_,[⟨_,.returnStmt none⟩]⟩ => return ⟨.unit,by rw [shape]; exact .bare⟩
  | ⟨_,[⟨_,.returnStmt (some source)⟩]⟩ =>
      let c ← child inputs source; return ⟨c.type,by rw [shape]; exact .expression c.evidence⟩
  | ⟨_,[⟨span,.block statements⟩]⟩ =>
      let c ← body inputs ⟨span,statements⟩; return ⟨c.type,by rw [shape]; exact .block c.evidence⟩
  | ⟨span,⟨_,.letDecl name annotation (some initializer)⟩::rest⟩ =>
      let c ← child inputs initializer
      let tail ← body (inputs.bindFresh owner name.value c.type) ⟨span,rest⟩
      match present : annotation with
      | none => return ⟨tail.type,by rw [shape,present]; exact .inferred c.evidence tail.evidence⟩
      | some original =>
          let m ← meaning original
          if same : m.type=c.type then return ⟨tail.type,by rw [shape,present]; exact .binding (same ▸ m.evidence) c.evidence tail.evidence⟩
          else throw (IO.userError "source binding annotation")
  | ⟨span,⟨_,.expression expr true⟩::rest⟩ =>
      let c ← child inputs expr; let tail ← body inputs ⟨span,rest⟩
      return ⟨tail.type,by rw [shape]; exact .discard c.evidence tail.evidence⟩
  | ⟨_,[⟨_,.ifThen condition yes (some no)⟩]⟩ =>
      let c ← child inputs condition; let t ← body inputs yes; let f ← body inputs no
      match barrier : yes with
      | ⟨_,[⟨_,.block _⟩]⟩ =>
          have protects : ComputationNamesProtected (inputs.names.map Prod.fst) yes := by
            intro name exposed; rw [barrier] at exposed; cases exposed with | tail impossible => cases impossible
          if same : c.type=.bool ∧ f.type=t.type then return ⟨t.type,by rw [shape]; exact .conditional (same.1 ▸ c.evidence) protects t.evidence (same.2 ▸ f.evidence)⟩
          else throw (IO.userError "source conditional types")
      | _ => throw (IO.userError "source explicit scope barrier")
  | ⟨_,[⟨_,.matchWith ⟨_,⟨scrutinee,[]⟩⟩ ⟨_,⟨[first,last],none⟩⟩⟩]⟩ =>
      let c ← child inputs scrutinee
      let p ← pattern first.value.pattern; let q ← pattern last.value.pattern
      have firstSmaller : sizeOf first.value.body < sizeOf first := by rcases first with ⟨_,⟨_,_⟩⟩; simp; omega
      have lastSmaller : sizeOf last.value.body < sizeOf last := by rcases last with ⟨_,⟨_,_⟩⟩; simp; omega
      let t ← body inputs first.value.body; let f ← body inputs last.value.body
      if same : c.type=.word ∧ q.tag=none ∧ f.type=t.type then
        return ⟨t.type,by
          rw [shape]; refine .wordMatch c.evidence ?_ (.inl same.1) (.inr ⟨last,by simp,same.2.1 ▸ q.evidence⟩) ?_ (by simp)
          · intro arm member; simp only [List.mem_cons,List.not_mem_nil,or_false] at member
            rcases member with rfl | rfl; exact ⟨_,p.evidence⟩; exact ⟨_,q.evidence⟩
          · intro arm member; simp only [List.mem_cons,List.not_mem_nil,or_false] at member
            rcases member with rfl | rfl; exact t.evidence; exact same.2.2 ▸ f.evidence⟩
      else throw (IO.userError "source match coverage and all-arm typing")
  | ⟨_,[⟨_,.matchWith ⟨_,⟨scrutinee,[]⟩⟩ ⟨_,⟨[],some fallback⟩⟩⟩]⟩ =>
      let c ← child inputs scrutinee; let t ← body inputs fallback
      return ⟨t.type,by rw [shape]; exact .wordMatch c.evidence (by simp) (.inr (by simp)) (.inl rfl) (by simp) (by simpa using t.evidence)⟩
  | _ => throw (IO.userError "independent source body typing profile")
termination_by sizeOf source
private def accepted (text : String) (a b : Core.Ty) (diagnostics : Nat := 0) : IO Unit := do
  let source ← parsed text diagnostics; let h ← header source a b
  let inner := outer.bindFresh owner h.name a
  let original ← body inner h.body
  let some domain := wellFormed a | throw (IO.userError "source domain WF")
  let some codomain := wellFormed b | throw (IO.userError "source codomain WF")
  if same : original.type=b then
    have sourceTyped : ExpectedComputationLambdaHasType RecursiveLocalComputationHasType types owner outer source (.function a b) :=
      .lambda h.evidence domain.down codomain.down (by
        change ComputationReturnTreeHasType RecursiveLocalComputationHasType types owner inner h.body b
        exact Eq.mp (congrArg (fun t => ComputationReturnTreeHasType RecursiveLocalComputationHasType types owner inner h.body t) same) original.evidence)
    have elaborates := (expectedComputationLambdaHasType_iff_elaborates recursiveLocalComputationHasType_iff_elaborates).mp sourceTyped
    have checked := (expectedComputationLambdaHasType_iff_checked recursiveLocalComputationHasType_iff_elaborates elaborateRecursiveLocalComputation?_iff).mp sourceTyped
    have reflected := (expectedComputationLambdaHasType_iff_elaborates recursiveLocalComputationHasType_iff_elaborates).mpr elaborates
    have checkedBack := (expectedComputationLambdaHasType_iff_checked recursiveLocalComputationHasType_iff_elaborates elaborateRecursiveLocalComputation?_iff).mpr checked
    have present : (elaborateExpectedComputationLambda? elaborateRecursiveLocalComputation? types owner outer source (.function a b)).isSome=true := by
      obtain ⟨core,found⟩ := checked; rw [found]; rfl
    have _ := reflected; have _ := checkedBack; have _ := present
    check (elaborateExpectedComputationLambda? elaborateRecursiveLocalComputation? types owner outer source (.function a b)).isSome "only now consult the existing checker; no Core output was chosen"
    check (decide (inner.names=(h.name,id 32)::outer.names ∧ inner.context=(id 32,a)::outer.context)) "source identity shadowing retains all outer rows"
    check (elaborateRecursiveLocalComputation? outer.names outer.context source).isNone "old recursive lambda admission unchanged"
  else throw (IO.userError "source body and expected codomain disagree")
private def rejected (text : String) (a b : Core.Ty) (diagnostics : Nat := 0) (typedMismatch : Bool := false) : IO Unit := do
  let source ← parsed text diagnostics; let h ← header source a b
  if typedMismatch then
    let original ← body (outer.bindFresh owner h.name a) h.body
    check (decide (original.type≠b)) "independent source body typing can disagree with the valid header"
    have _ := original.evidence
  have _ := declareExpectedUnaryLambdaHeader?_iff.mpr h.evidence
  if absent : elaborateExpectedComputationLambda? elaborateRecursiveLocalComputation? types owner outer source (.function a b)=none then
    have notTyped : ¬ ExpectedComputationLambdaHasType RecursiveLocalComputationHasType types owner outer source (.function a b) := by
      intro typed
      obtain ⟨core,found⟩ := (expectedComputationLambdaHasType_iff_checked recursiveLocalComputationHasType_iff_elaborates elaborateRecursiveLocalComputation?_iff).mp typed
      rw [absent] at found; cases found
    have _ := notTyped
    check (declareExpectedUnaryLambdaHeader? types owner outer source (.function a b)).isSome "original header-only acceptance is weaker"
  else throw (IO.userError "unselected or unsupported source body was accepted")
private def wholeRejected : IO Unit := do
  let text := "function wrap() returns(function(A) returns(A)){return lam(x){return x;};}"
  let .ok lexed := Syntax.Lexer.lex (file text) | throw (IO.userError "whole lexer")
  match Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial (file text) lexed) with
  | .ok declaration next =>
      check (next.atEnd && lexed.diagnostics.isEmpty && next.diagnostics.isEmpty) "original complete function"
      check (compileComputationFunction? elaborateRecursiveLocalComputation? types owner declaration).isNone "source-only typing does not extend whole function admission"
  | .reject _ _ => throw (IO.userError "whole rejected")
  | .invariant _ => throw (IO.userError "whole parser invariant")
end ParsedExpectedLambdaTyping
open ParsedExpectedLambdaTyping
def frontendParsedExpectedLambdaTypingTests : IO Unit := do
  for text in ["lam(x){return x;}","lam(x:A)->A{return x;}","lam(x,)->A{return saved;}"] do accepted text .word .word
  accepted "lam(x:B)->A{return saved;}" .bool .word
  accepted "lam(x:A)->A{let x:A=f(x);let x=x;if(c){{let saved=x;return saved;}}else{match(x){case (0){return saved;}case ((_)){return x;}}}}" .word .word
  accepted "lam(x){let x=f(x);let x=x;if(c){{let saved=x;return saved;}}else{match(x){case (0){return saved;}case ((_)){return x;}}}}" .word .word
  accepted "lam(x){f(x);match(x){case 0{return saved;}case _{return x;}}}" .word .word
  accepted "lam(x:B)->B{match(x){default{return x;}}}" .bool .bool
  accepted "lam(x:(A,B))->(A,B){return x;}" (.product .word .bool) (.product .word .bool)
  accepted "lam(x:C)->A{return saved;}" (.cell (.function .word .word)) .word
  accepted "lam(x:A)->(){return;}" .word .unit
  accepted "lam(comptime){return comptime;}" .word .word 1
  rejected "lam(x){return x;}" .word .bool 0 true
  rejected "lam(x:A)->A{return c;}" .word .word 0 true
  for text in ["lam(x){return Missing;}","lam(x){return lam(y){return y;};}",
      "lam(x){if(c){{return x;}}else{return Missing;}}",
      "lam(x){if(c){{return x;}}else{let y:Missing=x;return x;}}",
      "lam(x){if(c){let saved=x;return saved;}else{return saved;}}",
      "lam(x){match(x){case 0{return x;}}}",
      "lam(x){match(x){case 0{return x;}case _{return c;}}}",
      "lam(x){match(x){case _{return x;}default{return Missing;}}}"] do rejected text .word .word
  rejected "lam(x){let ;}" .word .word 1
  wholeRejected
end Tests
end
