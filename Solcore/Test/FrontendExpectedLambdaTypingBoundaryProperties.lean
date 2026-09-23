import Solcore.Frontend.Expected
import Solcore.Frontend.RecursiveLocalComputation

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
