import Solcore.Frontend.Expected
import Solcore.Frontend.RecursiveComputationReturnTree
import Solcore.Frontend.RecursiveLocalComputation
import Solcore.Frontend.Computation

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
