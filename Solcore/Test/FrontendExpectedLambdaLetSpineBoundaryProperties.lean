import Solcore.Frontend.Expected

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
