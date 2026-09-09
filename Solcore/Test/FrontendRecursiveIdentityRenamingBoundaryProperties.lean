import Solcore.Frontend.RecursiveLocalComputationRenamingProperties
import Solcore.Frontend.RecursiveLocalComputationEvaluationRenamingProperties
import Solcore.Frontend.RecursiveLocalComputationExecutionProperties
import Solcore.Core.FuelResumptionProperties
import Solcore.Core.Safety

/-! Injectivity is distinct from positional typing, and whole checking is
distinct from selected raw success. The original source and actual captured
payload are not rewritten when names/context/environment IDs are relabeled. -/
set_option autoImplicit false
namespace Tests.FrontendRecursiveIdentityRenamingBoundary
open Solcore Solcore.Frontend
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"RecursiveIdentityBoundary",by decide⟩],by decide⟩⟩,127⟩
private def ident (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def span : Syntax.SourceSpan := ⟨⟨.main,"recursive-identity-boundary.sol"⟩,37,200⟩
private def ref (n : String) : Syntax.Expr := ⟨span,.identifier ⟨span,n⟩⟩
private def names : LocalNameTable := [("c",ident 7),("f",ident 13),("x",ident 21)]
private def context : Resolved.Context := [(ident 7,.bool),(ident 13,.function .bool .bool),(ident 21,.bool)]
private def call : Syntax.Expr := ⟨span,.call (ref "f") ⟨span,[ref "x"]⟩⟩
private def lazySource (right : Syntax.Expr) : Syntax.Expr := ⟨span,.binary (ref "c") ⟨span,.logicalAnd⟩ right⟩
private def core : Core.Expr := .ifE (.var 0) (.apply (.var 1) (.var 2)) (.bool false)
private def closure (payload : Core.Value) (captured : Core.Environment) : Core.Value :=
  .closure .bool .bool (.var 1) (payload::captured)
private def env (choice : Bool) (payload argument : Core.Value) (captured : Core.Environment) : Resolved.Environment :=
  [(ident 7,.bool choice),(ident 13,closure payload captured),(ident 21,argument)]
private theorem original : RecursiveLocalComputationElaborates names context (lazySource call) core .bool :=
  .logicalAnd (.pure (.identifier .head) (.var .head) (.var .head))
    (.application
      (.pure (.identifier (.tail (by decide) .head)) (.var (.tail (by decide) .head)) (.var (.tail (by decide) .head)))
      (.pure (.identifier (.tail (by decide) (.tail (by decide) .head)))
        (.var (.tail (by decide) (.tail (by decide) .head))) (.var (.tail (by decide) (.tail (by decide) .head)))))
private theorem callCost (payload argument : Core.Value) (captured : Core.Environment) (s : Core.Store) :
    RecursiveLocalComputationEvaluatesWithCost names (env true payload argument captured) s call payload s 6 := by
  refine .application (parameterType := .bool) (resultType := .bool) (body := .var 1) (captured := payload::captured)
    (argumentValue := argument) (argumentStore := s) (bodyStore := s) (functionCost := 1) (argumentCost := 1) (bodyCost := 1) ?_ ?_ (.cons (.var rfl) .refl)
  · exact .pure (.identifier (.tail (by decide) .head) (.tail (by decide) .head))
  · exact .pure (.identifier (.tail (by decide) (.tail (by decide) .head)) (.tail (by decide) (.tail (by decide) .head)))
private theorem raw (payload argument : Core.Value) (captured : Core.Environment) (s : Core.Store) :
    RecursiveLocalComputationEvaluatesWithCost names (env true payload argument captured) s (lazySource call) payload s 9 := by
  refine .andTrue (middleStore := s) (leftCost := 1) (rightCost := 6) ?_ (callCost payload argument captured s)
  exact .pure (.identifier .head .head)
private theorem manual (payload argument : Core.Value) (captured : Core.Environment) (s : Core.Store) (k : List Core.Frame) :
    Core.Steps 9 ⟨.eval core (env true payload argument captured).values,k,s⟩ ⟨.ret payload,k,s⟩ :=
  CostStepComposition.ifTrue (.cons (.var rfl) .refl)
    (CostStepComposition.apply (.cons (.var rfl) .refl) (.cons (.var rfl) .refl) (.cons (.var rfl) .refl))

theorem selected_rhs_keeps_arbitrary_actual_payload_despite_static_bool_tag
    (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping)
    (payload argument : Core.Value) (captured : Core.Environment) (s : Core.Store) (k : List Core.Frame) :
    elaborateRecursiveLocalComputation? (LocalNameTable.mapIds mapping names) (Resolved.LocalScope.mapIds mapping context)
      (lazySource call)=some (core,.bool) ∧
    RecursiveLocalComputationEvaluatesWithCost (LocalNameTable.mapIds mapping names)
      (Resolved.LocalScope.mapIds mapping (env true payload argument captured)) s (lazySource call) payload s 9 ∧
    Core.Steps 9 ⟨.eval core (Resolved.LocalScope.mapIds mapping (env true payload argument captured)).values,k,s⟩ ⟨.ret payload,k,s⟩ :=
  ⟨(elaborateRecursiveLocalComputation?_mapIds mapping injective names context _).trans (elaborateRecursiveLocalComputation?_iff.mpr original),
    (recursiveLocalComputationEvaluatesWithCost_mapIds_iff mapping injective).mpr (raw payload argument captured s),
    by simpa only [Resolved.LocalScope.values_mapIds] using manual payload argument captured s k⟩
theorem selected_call_exact_fuel_and_full_resumption
    (mapping : Resolved.LocalId → Resolved.LocalId) (payload argument : Core.Value) (captured : Core.Environment)
    (s : Core.Store) (fuel extra : Nat) :
    let start := Core.State.initial core (Resolved.LocalScope.mapIds mapping (env true payload argument captured)).values s
    (Core.runStateful fuel start=.done payload s ↔ 9≤fuel) ∧
    ∀ cp, Core.runStateful fuel start=.outOfFuel cp → Core.runStateful extra cp=Core.runStateful (fuel+extra) start := by
  simp only [Resolved.LocalScope.values_mapIds]
  exact ⟨(manual payload argument captured s []).runStateful_done_iff,fun _ stopped => Core.runStateful_resume stopped extra⟩
private def unsupported : Syntax.Expr := ⟨span,.literal ⟨span,.string "unsupported"⟩⟩
private def badRights : List Syntax.Expr := [ref "missing",unsupported]
private theorem badCheck (right : Syntax.Expr) (member : right∈badRights) :
    elaborateRecursiveLocalComputation? names context (lazySource right)=none := by
  simp only [badRights,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  all_goals simp [lazySource,ref,unsupported,names,elaborateRecursiveLocalComputation?,elaborateLocalExpression?,
    resolveLocalExpression?,LocalNameTable.lookup?,interpretWordLiteral?,numericLiteralValue?]
theorem unchecked_skipped_syntax_retains_raw_success_and_whole_rejection
    (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping)
    (right : Syntax.Expr) (member : right∈badRights) (payload argument : Core.Value) (captured : Core.Environment) (s : Core.Store) :
    RecursiveLocalComputationEvaluatesWithCost (LocalNameTable.mapIds mapping names)
      (Resolved.LocalScope.mapIds mapping (env false payload argument captured)) s (lazySource right) (.bool false) s 4 ∧
    elaborateRecursiveLocalComputation? names context (lazySource right)=none ∧
    elaborateRecursiveLocalComputation? (LocalNameTable.mapIds mapping names) (Resolved.LocalScope.mapIds mapping context) (lazySource right)=none :=
  ⟨(recursiveLocalComputationEvaluatesWithCost_mapIds_iff mapping injective).mpr (.andFalse (.pure (.identifier .head .head))),
    badCheck right member,(elaborateRecursiveLocalComputation?_mapIds mapping injective names context _).trans (badCheck right member)⟩
private theorem unknownAbsent (e : Resolved.Environment) (s t : Core.Store) (v : Core.Value) :
    ¬ RecursiveLocalComputationEvaluates names e s (ref "missing") v t := by
  intro evaluated
  cases evaluated with
  | pure child => cases child with
    | identifier named _ => have found := LocalNameTable.lookup?_iff.mpr named; change none=some _ at found; cases found
theorem raw_success_absence_is_reflected_without_a_typing_premise
    (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping)
    (e : Resolved.Environment) (s t : Core.Store) (v : Core.Value) :
    ¬ RecursiveLocalComputationEvaluates (LocalNameTable.mapIds mapping names) (Resolved.LocalScope.mapIds mapping e) s (ref "missing") v t :=
  fun evaluated => unknownAbsent e s t v ((recursiveLocalComputationEvaluates_mapIds_iff mapping injective).mp evaluated)

private def shifted (id : Resolved.LocalId) : Resolved.LocalId :=
  { owner := { id.owner with declarationIndex := id.owner.declarationIndex+6 },binderIndex := id.binderIndex+10 }
private theorem shiftInjective : Function.Injective shifted := by
  intro left right equal
  have modules := congrArg (fun id : Resolved.LocalId => id.owner.moduleId) equal
  have owners := Nat.add_right_cancel (congrArg (fun id : Resolved.LocalId => id.owner.declarationIndex) equal)
  have binders := Nat.add_right_cancel (congrArg Resolved.LocalId.binderIndex equal)
  cases left with | mk l i => cases l with | mk lm ld =>
    cases right with | mk r j => cases r with | mk rm rd => cases modules; cases owners; cases binders; rfl
theorem a_nonsurjective_map_changes_owners_and_indices_but_not_the_child
    (payload argument : Core.Value) (captured : Core.Environment) (s : Core.Store) :
    Function.Injective shifted ∧ (¬ ∃ id,shifted id=ident 0) ∧
    (LocalNameTable.mapIds shifted names).lookup? "f"=some ⟨{ owner with declarationIndex := 133 },23⟩ ∧
    RecursiveLocalComputationElaborates (LocalNameTable.mapIds shifted names) (Resolved.LocalScope.mapIds shifted context)
      (lazySource call) core .bool ∧
    RecursiveLocalComputationEvaluatesWithCost (LocalNameTable.mapIds shifted names)
      (Resolved.LocalScope.mapIds shifted (env true payload argument captured)) s (lazySource call) payload s 9 := by
  refine ⟨shiftInjective,?_,rfl,(recursiveLocalComputationElaborates_mapIds_iff shifted shiftInjective).mpr original,
    (recursiveLocalComputationEvaluatesWithCost_mapIds_iff shifted shiftInjective).mpr (raw payload argument captured s)⟩
  rintro ⟨id,equal⟩; have impossible := congrArg Resolved.LocalId.binderIndex equal; change id.binderIndex+10=0 at impossible; omega
private def merge (_ : Resolved.LocalId) := ident 0
private def distinctNames : LocalNameTable := [("a",ident 0),("b",ident 1)]
private def distinctContext : Resolved.Context := [(ident 0,.bool),(ident 1,.word)]
private def word : Core.Value := .word (Core.Word.ofNatModulo 17)
private def distinctValues : Resolved.Environment := [(ident 0,.bool true),(ident 1,word)]
private theorem originalB : RecursiveLocalComputationElaborates distinctNames distinctContext (ref "b") (.var 1) .word :=
  .pure (.identifier (.tail (by decide) .head)) (.var (.tail (by decide) .head)) (.var (.tail (by decide) .head))
private theorem mergedB : RecursiveLocalComputationElaborates (LocalNameTable.mapIds merge distinctNames)
    (Resolved.LocalScope.mapIds merge distinctContext) (ref "b") (.var 0) .bool :=
  .pure (.identifier (.tail (by decide) .head)) (.var .head) (.var .head)
theorem noninjective_first_identity_capture_changes_core_type_and_actual_value (s : Core.Store) :
    (¬ Function.Injective merge) ∧
    elaborateRecursiveLocalComputation? distinctNames distinctContext (ref "b")=some (.var 1,.word) ∧
    elaborateRecursiveLocalComputation? (LocalNameTable.mapIds merge distinctNames)
      (Resolved.LocalScope.mapIds merge distinctContext) (ref "b")=some (.var 0,.bool) ∧
    RecursiveLocalComputationEvaluatesWithCost distinctNames distinctValues s (ref "b") word s 1 ∧
    RecursiveLocalComputationEvaluatesWithCost (LocalNameTable.mapIds merge distinctNames)
      (Resolved.LocalScope.mapIds merge distinctValues) s (ref "b") (.bool true) s 1 ∧
    Core.runStateful 1 (.initial (.var 1) distinctValues.values s)=.done word s ∧
    Core.runStateful 1 (.initial (.var 0) (Resolved.LocalScope.mapIds merge distinctValues).values s)=.done (.bool true) s := by
  refine ⟨?_,elaborateRecursiveLocalComputation?_iff.mpr originalB,elaborateRecursiveLocalComputation?_iff.mpr mergedB,
    .pure (.identifier (.tail (by decide) .head) (.tail (by decide) .head)),
    .pure (.identifier (.tail (by decide) .head) .head),rfl,rfl⟩
  intro injective; have impossible := injective (show merge (ident 0)=merge (ident 1) from rfl); exact (by decide : ident 0≠ident 1) impossible
theorem positional_typing_alone_does_not_exclude_noninjective_capture :
    Core.EnvironmentHasTypes (Resolved.LocalScope.mapIds merge distinctValues).values
      (Resolved.LocalScope.mapIds merge distinctContext).values ∧
    ¬ RecursiveLocalComputationHasType (LocalNameTable.mapIds merge distinctNames)
      (Resolved.LocalScope.mapIds merge distinctContext) (ref "b") .word := by
  refine ⟨.cons .bool (.cons .word .nil),?_⟩
  intro typed
  obtain ⟨expression,elaborated⟩ := recursiveLocalComputationHasType_iff_elaborates.mp typed
  have conflict := (elaborateRecursiveLocalComputation?_iff.mpr elaborated).symm.trans (elaborateRecursiveLocalComputation?_iff.mpr mergedB)
  cases conflict
end Tests.FrontendRecursiveIdentityRenamingBoundary
