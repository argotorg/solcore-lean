import Solcore.Frontend.Expected
import Solcore.Frontend.RecursiveComputationReturnTree
import Solcore.Frontend.RecursiveLocalComputation

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
