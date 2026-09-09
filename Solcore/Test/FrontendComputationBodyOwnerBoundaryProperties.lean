import Solcore.Frontend.ComputationReturnTreeOwnerProperties
import Solcore.Frontend.RecursiveComputationReturnTree
import Solcore.Frontend.RecursiveLocalComputationRenamingProperties
import Solcore.Frontend.RecursiveLocalComputationExecutionProperties

/-! Sparse same-owner indices and arbitrarily large foreign indices are not
interchangeable. Owner covariance preserves fresh allocation; arbitrary
injective changes to binder indices need not. Actual rows are never rebuilt. -/
set_option autoImplicit false
namespace Tests.FrontendComputationBodyOwnerBoundary
open Solcore Solcore.Frontend
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"BodyOwnerBoundary",by decide⟩],by decide⟩⟩,130⟩
private def foreign : Resolved.DeclarationId := { owner with declarationIndex := 131 }
private def ident (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def span : Syntax.SourceSpan := ⟨⟨.main,"body-owner-boundary.sol"⟩,31,173⟩
private def inputs (a : Core.Ty) (high : Nat) : LocalTypeInputs :=
  ⟨[⟨"x",ident 7,a⟩,⟨"x",⟨foreign,high⟩,.bool⟩,⟨"old",ident 2,.word⟩],by simp [ident,owner,foreign]⟩
private def first (a : Core.Ty) (high : Nat) := (inputs a high).bindFresh owner "x" a
private def second (a : Core.Ty) (high : Nat) := (first a high).bindFresh owner "x" a
private def names (high : Nat) : LocalNameTable := [("x",ident 7),("x",⟨foreign,high⟩),("old",ident 2)]
private def ref : Syntax.Expr := ⟨span,.identifier ⟨span,"x"⟩⟩
private def named : Syntax.TypeExpr := ⟨span,.named ⟨span,⟨⟨⟨span,"A"⟩,[]⟩⟩⟩ none⟩
private def source : Syntax.Block := ⟨span,[
  ⟨span,.letDecl ⟨span,"x"⟩ (some named) (some ref)⟩,
  ⟨span,.letDecl ⟨span,"x"⟩ none (some ref)⟩,
  ⟨span,.returnStmt (some ref)⟩]⟩
private def core : Core.Expr := .letE (.var 0) (.letE (.var 0) (.var 0))
private def types (a : Core.Ty) : TypeNameTable := [(["A"],a)]
private theorem original (a : Core.Ty) (high : Nat) :
    RecursiveComputationReturnTreeElaborates (types a) owner (inputs a high) source core a :=
  .binding (.named .head) (.pure (.identifier .head) (.var .head) (.var .head))
    (.inferred (.pure (.identifier .head) (.var .head) (.var .head))
      (.expression (.pure (.identifier .head) (.var .head) (.var .head))))
private theorem originalTyped (a : Core.Ty) (high : Nat) :
    RecursiveComputationReturnTreeHasType (types a) owner (inputs a high) source a :=
  .binding (.named .head) (.pure (.identifier .head .head))
    (.inferred (.pure (.identifier .head .head)) (.expression (.pure (.identifier .head .head))))
private def shifted (id : Resolved.DeclarationId) : Resolved.DeclarationId :=
  { id with declarationIndex := id.declarationIndex+200 }
private theorem shiftedInjective : Function.Injective shifted := by
  intro left right same
  have modules := congrArg Resolved.DeclarationId.moduleId same
  have indices := Nat.add_right_cancel (congrArg Resolved.DeclarationId.declarationIndex same)
  cases left; cases right; cases modules; cases indices; rfl
private def map := ownerLocalIdMap shifted
private theorem mapInjective : Function.Injective map := ownerLocalIdMap_injective shifted shiftedInjective

theorem fresh_owner_filter_ignores_arbitrary_foreign_indices_and_repeated_spellings
    (a : Core.Ty) (high : Nat) :
    Resolved.freshLocalId owner (inputs a high).ids=ident 8 ∧
    Resolved.freshLocalId owner (first a high).ids=ident 9 ∧
    (second a high).ids=[ident 9,ident 8,ident 7,⟨foreign,high⟩,ident 2] ∧
    (second a high).bindings.map (fun b => (b.name,b.type))=
      [("x",a),("x",a),("x",a),("x",.bool),("old",.word)] := by
  exact ⟨rfl,rfl,rfl,rfl⟩
theorem each_initializer_reads_the_old_head_before_its_own_fresh_binding
    (a : Core.Ty) (high : Nat) :
    (inputs a high).names.lookup? "x"=some (ident 7) ∧
    (first a high).names.lookup? "x"=some (ident 8) ∧
    (second a high).names.lookup? "x"=some (ident 9) ∧
    RecursiveComputationReturnTreeHasType (types a) owner (inputs a high) source a ∧
    RecursiveComputationReturnTreeElaborates (types a) owner (inputs a high) source core a :=
  ⟨rfl,rfl,rfl,originalTyped a high,original a high⟩
theorem nonsurjective_owner_shift_keeps_indices_spelling_type_and_order
    (a : Core.Ty) (high : Nat) :
    Function.Injective shifted ∧ (¬ ∃ id,shifted id={ owner with declarationIndex := 0 }) ∧
    ((inputs a high).mapIds map mapInjective).ids=
      [⟨shifted owner,7⟩,⟨shifted foreign,high⟩,⟨shifted owner,2⟩] ∧
    ((inputs a high).mapIds map mapInjective).bindings.map (fun b => (b.name,b.type))=
      [("x",a),("x",.bool),("old",.word)] := by
  refine ⟨shiftedInjective,?_,rfl,rfl⟩
  rintro ⟨id,same⟩
  have impossible := congrArg Resolved.DeclarationId.declarationIndex same
  change id.declarationIndex+200=0 at impossible
  omega
theorem repeated_fresh_binding_and_body_transport_keep_the_literal_core
    (a : Core.Ty) (high : Nat) :
    (second a high).mapIds map mapInjective=
      (((inputs a high).mapIds map mapInjective).bindFresh (shifted owner) "x" a).bindFresh (shifted owner) "x" a ∧
    RecursiveComputationReturnTreeHasType (types a) (shifted owner) ((inputs a high).mapIds map mapInjective) source a ∧
    RecursiveComputationReturnTreeElaborates (types a) (shifted owner) ((inputs a high).mapIds map mapInjective) source core a ∧
    elaborateRecursiveComputationReturnTree? (types a) (shifted owner)
      ((inputs a high).mapIds map mapInjective) source=some (core,a) := by
  refine ⟨?_,(computationReturnTreeHasType_mapOwner_iff shifted shiftedInjective
      (recursiveLocalComputationHasType_mapIds_iff map mapInjective)).mpr (originalTyped a high),
    (computationReturnTreeElaborates_mapOwner_iff shifted shiftedInjective
      (recursiveLocalComputationElaborates_mapIds_iff map mapInjective)).mpr (original a high),?_⟩
  · exact (LocalTypeInputs.bindFresh_mapOwner (first a high) owner shifted shiftedInjective "x" a).trans
      (congrArg (fun i => i.bindFresh (shifted owner) "x" a)
        (LocalTypeInputs.bindFresh_mapOwner (inputs a high) owner shifted shiftedInjective "x" a))
  · exact (elaborateComputationReturnTree?_mapOwner shifted shiftedInjective elaborateRecursiveLocalComputation?
      (elaborateRecursiveLocalComputation?_mapIds map mapInjective) _ _ _ _).trans
        ((elaborateComputationReturnTree?_iff elaborateRecursiveLocalComputation?_iff).mpr (original a high))
private def environment (high : Nat) (v other old : Core.Value) : Resolved.Environment :=
  [(ident 7,v),(⟨foreign,high⟩,other),(ident 2,old)]
theorem original_actual_rows_and_seven_step_path_are_independent_of_static_types
    (high : Nat) (v other old : Core.Value) (store : Core.Store) (k : List Core.Frame) :
    RecursiveComputationReturnTreeEvaluatesWithCost owner (names high) (environment high v other old) store source v store 7 ∧
    (Resolved.LocalScope.mapIds map (environment high v other old)).values=[v,other,old] ∧
    Core.Steps 7 ⟨.eval core [v,other,old],k,store⟩ ⟨.ret v,k,store⟩ := by
  refine ⟨?_,rfl,CostStepComposition.letE (.cons (.var rfl) .refl)
      (CostStepComposition.letE (.cons (.var rfl) .refl) (.cons (.var rfl) .refl))⟩
  refine .binding (initializerCost := 1) (tailCost := 4) (boundValue := v) (middleStore := store) ?_ ?_
  · exact .pure (.identifier .head .head)
  · refine .inferred (initializerCost := 1) (tailCost := 1) (boundValue := v) (middleStore := store) ?_ ?_
    · exact .pure (.identifier .head .head)
    · exact .expression (.pure (.identifier .head .head))

private def zero := Core.Word.ofNatModulo 0
private def one := Core.Word.ofNatModulo 1
private def returned : Syntax.Block := ⟨span,[⟨span,.returnStmt (some ref)⟩]⟩
private def literalArm : Syntax.MatchCase := ⟨span,⟨⟨span,.literal ⟨span,.decimal "1"⟩⟩,returned⟩⟩
private def wildcardArm : Syntax.MatchCase := ⟨span,⟨⟨span,.group ⟨span,.wildcard span⟩⟩,returned⟩⟩
private def matchSource : Syntax.Block := ⟨span,[⟨span,.matchWith
  ⟨span,⟨⟨span,.literal ⟨span,.decimal "0"⟩⟩,[]⟩⟩
  ⟨span,⟨[literalArm,wildcardArm],some returned⟩⟩⟩]⟩
private def matchCore : Core.Expr :=
  .letE (.word zero) (.ifE (.binary .wordEq (.var 0) (.word one)) (.var 1) (.var 1))
private theorem zeroDenotes : WordLiteralDenotes ⟨span,.decimal "0"⟩ zero :=
  .decimal (by decide) (.cons (.decimal (digit := 0) (by decide) rfl) .nil)
private theorem literalClassifies : WordMatchPatternClassifies literalArm.value.pattern (some one) :=
  .literal ⟨_,rfl,.decimal (by decide) (.cons (.decimal (digit := 1) (by decide) rfl) .nil)⟩
private theorem matchOriginal (a : Core.Ty) (high : Nat) :
    RecursiveComputationReturnTreeElaborates (types a) owner (inputs a high) matchSource matchCore a := by
  refine .wordMatch (entries := [(literalArm,some one,.var 0),(wildcardArm,none,.var 0)])
    (defaultEntry := some (returned,.var 0)) (.pure (.wordLiteral zeroDenotes) .word .word)
    rfl ?_ (.inl rfl) ?_ rfl ?_ ?_
  · intro entry member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact literalClassifies
    · exact .group (.wildcard rfl)
  · intro entry member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;>
      exact .expression (.pure (.identifier .head) (.var .head) (.var .head))
  · intro entry member
    simp only [Option.toList_some,List.mem_singleton] at member
    subst entry
    exact .expression (.pure (.identifier .head) (.var .head) (.var .head))
  · simp [Core.Expr.weakenAt]
private theorem matchType (a : Core.Ty) (high : Nat) :
    RecursiveComputationReturnTreeHasType (types a) owner (inputs a high) matchSource a := by
  refine .wordMatch (.pure (.wordLiteral zeroDenotes)) ?_ (.inl rfl) (.inl rfl) ?_ ?_
  · intro entry member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact ⟨some one,literalClassifies⟩
    · exact ⟨none,.group (.wildcard rfl)⟩
  · intro entry member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> exact .expression (.pure (.identifier .head .head))
  · intro entry member
    simp only [Option.toList_some,List.mem_singleton] at member
    subst entry
    exact .expression (.pure (.identifier .head .head))
theorem tagged_rows_keep_order_and_all_original_branches_in_both_owner_directions
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (injective : Function.Injective mapping)
    (a : Core.Ty) (high : Nat) :
    RecursiveComputationReturnTreeHasType (types a) owner (inputs a high) matchSource a ∧
    RecursiveComputationReturnTreeElaborates (types a) owner (inputs a high) matchSource matchCore a ∧
    (RecursiveComputationReturnTreeHasType (types a) (mapping owner)
      ((inputs a high).mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective)) matchSource a ↔
      RecursiveComputationReturnTreeHasType (types a) owner (inputs a high) matchSource a) ∧
    (RecursiveComputationReturnTreeElaborates (types a) (mapping owner)
      ((inputs a high).mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective)) matchSource matchCore a ↔
      RecursiveComputationReturnTreeElaborates (types a) owner (inputs a high) matchSource matchCore a) :=
  ⟨matchType a high,matchOriginal a high,
    computationReturnTreeHasType_mapOwner_iff mapping injective
      (recursiveLocalComputationHasType_mapIds_iff _ (ownerLocalIdMap_injective mapping injective)),
    computationReturnTreeElaborates_mapOwner_iff mapping injective
      (recursiveLocalComputationElaborates_mapIds_iff _ (ownerLocalIdMap_injective mapping injective))⟩
theorem the_original_miss_then_wildcard_costs_one_comparison_not_two
    (high : Nat) (v other old : Core.Value) (store : Core.Store) (k : List Core.Frame) :
    WordMatchChooses (.word zero) [literalArm,wildcardArm] (some returned) returned 1 ∧
    RecursiveComputationReturnTreeEvaluatesWithCost owner (names high) (environment high v other old) store matchSource v store 11 ∧
    Core.Steps 11 ⟨.eval matchCore [v,other,old],k,store⟩ ⟨.ret v,k,store⟩ := by
  have selection : WordMatchChooses (.word zero) [literalArm,wildcardArm] (some returned) returned 1 :=
    .miss literalClassifies (by decide) (.wildcard (.group (.wildcard rfl)))
  refine ⟨selection,?_,CostStepComposition.letE (.cons .word .refl)
    (CostStepComposition.ifFalse (CostStepComposition.binary (.cons (.var rfl) .refl) (.cons .word .refl) rfl)
      (.cons (.var rfl) .refl))⟩
  refine .wordMatch (scrutineeCost := 1) (branchCost := 1) (tests := 1)
    (.pure (.wordLiteral zeroDenotes)) selection ?_
  exact .expression (.pure (.identifier .head .head))

private def indexShift (id : Resolved.LocalId) : Resolved.LocalId := { id with binderIndex := id.binderIndex+10 }
private theorem indexInjective : Function.Injective indexShift := by
  intro left right same
  have owners := congrArg Resolved.LocalId.owner same
  have indices := Nat.add_right_cancel (congrArg Resolved.LocalId.binderIndex same)
  cases left; cases right; cases owners; cases indices; rfl
private def onlyForeign (a : Core.Ty) (high : Nat) : LocalTypeInputs :=
  ⟨[⟨"x",⟨foreign,high⟩,a⟩],by simp⟩
theorem arbitrary_injective_index_changes_do_not_commute_with_fresh_binding
    (a : Core.Ty) (high : Nat) :
    Function.Injective indexShift ∧
    (((onlyForeign a high).bindFresh owner "x" a).mapIds indexShift indexInjective).ids=
      [ident 10,⟨foreign,high+10⟩] ∧
    (((onlyForeign a high).mapIds indexShift indexInjective).bindFresh owner "x" a).ids=
      [ident 0,⟨foreign,high+10⟩] ∧
    ((onlyForeign a high).bindFresh owner "x" a).mapIds indexShift indexInjective ≠
      ((onlyForeign a high).mapIds indexShift indexInjective).bindFresh owner "x" a := by
  refine ⟨indexInjective,rfl,rfl,?_⟩
  intro same
  have ids := congrArg LocalTypeInputs.ids same
  have firstId := (List.cons.inj ids).1
  have impossible := congrArg Resolved.LocalId.binderIndex firstId
  exact (by decide : (10 : Nat)≠0) impossible
theorem the_fresh_counterexample_still_satisfies_concrete_child_covariance
    (a : Core.Ty) (high : Nat) :
    elaborateRecursiveLocalComputation? (onlyForeign a high).names (onlyForeign a high).context ref=some (.var 0,a) ∧
    elaborateRecursiveLocalComputation? ((onlyForeign a high).mapIds indexShift indexInjective).names
      ((onlyForeign a high).mapIds indexShift indexInjective).context ref=some (.var 0,a) := by
  have originalChild : RecursiveLocalComputationElaborates (onlyForeign a high).names (onlyForeign a high).context ref (.var 0) a :=
    .pure (.identifier .head) (.var .head) (.var .head)
  refine ⟨elaborateRecursiveLocalComputation?_iff.mpr originalChild,?_⟩
  exact (elaborateRecursiveLocalComputation?_mapIds indexShift indexInjective _ _ _).trans
    (elaborateRecursiveLocalComputation?_iff.mpr originalChild)
end Tests.FrontendComputationBodyOwnerBoundary
