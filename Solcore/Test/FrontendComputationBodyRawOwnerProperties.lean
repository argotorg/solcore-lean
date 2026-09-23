import Solcore.Frontend.Computation
import Solcore.Frontend.RecursiveComputationReturnTree
import Solcore.Frontend.RecursiveLocalComputation
import Solcore.Core.FuelResumptionProperties

/-! Symbolic original blocks, not parser outputs. Arbitrary raw rows stay raw:
only the separately elaborated two-row fixture below has a positional Core
claim. Discard retains the actual closure's whole cost and store transition. -/
set_option autoImplicit false
namespace Tests.FrontendComputationBodyRawOwner
open Solcore Solcore.Frontend
private def ref (s : Syntax.SourceSpan) (name : String) : Syntax.Expr := ⟨s,.identifier ⟨s,name⟩⟩
private def zero := Core.Word.ofNatModulo 0
private def one := Core.Word.ofNatModulo 1
private def literal (s : Syntax.SourceSpan) : Syntax.Expr := ⟨s,.literal ⟨s,.decimal "0"⟩⟩
private theorem denotes (s : Syntax.SourceSpan) : WordLiteralDenotes ⟨s,.decimal "0"⟩ zero :=
  .decimal (by decide) (.cons (.decimal (digit := 0) (by decide) rfl) .nil)
private def call (s : Syntax.SourceSpan) : Syntax.Expr := ⟨s,.call (ref s "f") ⟨s,[ref s "x"]⟩⟩
private def returned (s : Syntax.SourceSpan) : Syntax.Block := ⟨s,[⟨s,.returnStmt (some (ref s "x"))⟩]⟩
private def condition (s : Syntax.SourceSpan) : Syntax.Expr := ⟨s,.binary (literal s) ⟨s,.equal⟩ (literal s)⟩
private def literalArm (s : Syntax.SourceSpan) (bad : Syntax.Block) : Syntax.MatchCase := ⟨s,⟨⟨s,.literal ⟨s,.decimal "1"⟩⟩,bad⟩⟩
private def wildArm (s : Syntax.SourceSpan) : Syntax.MatchCase := ⟨s,⟨⟨s,.group ⟨s,.wildcard s⟩⟩,returned s⟩⟩
private def arms (s : Syntax.SourceSpan) (bad : Syntax.Block) : List Syntax.MatchCase := [literalArm s bad,wildArm s]
private def matched (s : Syntax.SourceSpan) (bad : Syntax.Block) : Syntax.Block :=
  ⟨s,[⟨s,.matchWith ⟨s,⟨literal s,[]⟩⟩ ⟨s,⟨arms s bad,some bad⟩⟩⟩]⟩
private def statements (s : Syntax.SourceSpan) (annotation : Syntax.TypeExpr) (bad : Syntax.Block) : Nat → List Syntax.Statement
  | 0 => [⟨s,.expression (call s) true⟩,⟨s,.ifThen (condition s) (matched s bad) (some bad)⟩]
  | n+1 => ⟨s,.letDecl ⟨s,"x"⟩ (some annotation) (some (ref s "x"))⟩::
      ⟨s,.letDecl ⟨s,"x"⟩ none (some (ref s "x"))⟩::statements s annotation bad n
private theorem choice (s : Syntax.SourceSpan) (bad : Syntax.Block) :
    WordMatchChooses (.word zero) (arms s bad) (some bad) (returned s) 1 :=
  .miss (literal := one) (.literal ⟨_,rfl,.decimal (by decide) (.cons (.decimal (digit := 1) (by decide) rfl) .nil)⟩)
    (by decide) (.wildcard (.group (.wildcard rfl)))
private structure Rows (v f : Core.Value) where
  names : LocalNameTable
  env : Resolved.Environment
  xId : Resolved.LocalId
  fId : Resolved.LocalId
  namedX : LocalNameTable.Lookup names "x" xId
  namedF : LocalNameTable.Lookup names "f" fId
  valueX : Resolved.LocalScope.Lookup env xId v
  valueF : Resolved.LocalScope.Lookup env fId f
private def Rows.bind {v f : Core.Value} (r : Rows v f) (o : Resolved.DeclarationId) : Rows v f where
  names := ("x",Resolved.freshLocalId o (r.names.map Prod.snd))::r.names
  env := (Resolved.freshLocalId o (r.names.map Prod.snd),v)::r.env
  xId := Resolved.freshLocalId o (r.names.map Prod.snd)
  fId := r.fId
  namedX := .head
  namedF := .tail (by decide) r.namedF
  valueX := .head
  valueF := .tail (by
    intro same
    exact Resolved.freshLocalId_not_mem o (r.names.map Prod.snd)
      (same ▸ List.mem_map.mpr ⟨("f",r.fId),r.namedF.mem,rfl⟩)) r.valueF
private theorem originalRaw (s : Syntax.SourceSpan) (annotation : Syntax.TypeExpr) (bad : Syntax.Block)
    (o : Resolved.DeclarationId) (n : Nat) (a b : Core.Ty) (body : Core.Expr) (captured : Core.Environment)
    (v ignored : Core.Value) (initial final : Core.Store)
    (actual : Core.Evaluates (v::captured) initial body ignored final)
    (r : Rows v (.closure a b body captured)) :
    RecursiveComputationReturnTreeEvaluates o r.names r.env initial ⟨s,statements s annotation bad n⟩ v final := by
  induction n generalizing r with
  | zero =>
      refine .discard (.application (.pure (.identifier r.namedF r.valueF)) (.pure (.identifier r.namedX r.valueX)) actual) ?_
      exact .ifTrue (.pure (.equal (.wordLiteral (denotes s)) (.wordLiteral (denotes s))))
        (.wordMatch (.pure (.wordLiteral (denotes s))) (choice s bad) (.expression (.pure (.identifier r.namedX r.valueX))))
  | succ n ih =>
      exact .binding (.pure (.identifier r.namedX r.valueX))
        (.inferred (.pure (.identifier .head .head)) (ih ((r.bind o).bind o)))
private theorem originalCost (s : Syntax.SourceSpan) (annotation : Syntax.TypeExpr) (bad : Syntax.Block)
    (o : Resolved.DeclarationId) (n : Nat) (a b : Core.Ty) (body : Core.Expr) (captured : Core.Environment)
    (v ignored : Core.Value) (initial final : Core.Store) (bodyCost : Nat)
    (actual : Core.Steps bodyCost (.initial body (v::captured) initial) (.final ignored final))
    (r : Rows v (.closure a b body captured)) :
    RecursiveComputationReturnTreeEvaluatesWithCost o r.names r.env initial
      ⟨s,statements s annotation bad n⟩ v final (6*n+bodyCost+25) := by
  induction n generalizing r with
  | zero =>
      have count : 6*0+bodyCost+25=(1+1+bodyCost+3)+18+2 := by omega
      rw [count]
      refine .discard (expressionCost := 1+1+bodyCost+3) (tailCost := 18) (discardedValue := ignored) (middleStore := final) ?_ ?_
      · exact .application (.pure (.identifier r.namedF r.valueF)) (.pure (.identifier r.namedX r.valueX)) actual
      · exact .ifTrue (conditionCost := 5) (branchCost := 11)
          (.pure (.equal (.wordLiteral (denotes s)) (.wordLiteral (denotes s))))
          (.wordMatch (scrutineeCost := 1) (branchCost := 1) (tests := 1)
            (.pure (.wordLiteral (denotes s))) (choice s bad) (.expression (.pure (.identifier r.namedX r.valueX))))
  | succ n ih =>
      have count : 6*(n+1)+bodyCost+25=1+(1+(6*n+bodyCost+25)+2)+2 := by omega
      rw [count]
      exact .binding (.pure (.identifier r.namedX r.valueX))
        (.inferred (.pure (.identifier .head .head)) (ih ((r.bind o).bind o)))

theorem raw_and_cost_are_original_independent_derivations
    (s : Syntax.SourceSpan) (annotation : Syntax.TypeExpr) (bad : Syntax.Block) (o : Resolved.DeclarationId) (n : Nat)
    (a b : Core.Ty) (body : Core.Expr) (captured : Core.Environment) (v ignored : Core.Value)
    (initial final : Core.Store) (bodyCost : Nat)
    (actualRaw : Core.Evaluates (v::captured) initial body ignored final)
    (actualCost : Core.Steps bodyCost (.initial body (v::captured) initial) (.final ignored final))
    (r : Rows v (.closure a b body captured)) :
    RecursiveComputationReturnTreeEvaluates o r.names r.env initial ⟨s,statements s annotation bad n⟩ v final ∧
    RecursiveComputationReturnTreeEvaluatesWithCost o r.names r.env initial ⟨s,statements s annotation bad n⟩ v final (6*n+bodyCost+25) :=
  ⟨originalRaw s annotation bad o n a b body captured v ignored initial final actualRaw r,
    originalCost s annotation bad o n a b body captured v ignored initial final bodyCost actualCost r⟩
theorem owner_change_preserves_both_raw_interfaces_and_the_discarded_effects
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (injective : Function.Injective mapping)
    (s : Syntax.SourceSpan) (annotation : Syntax.TypeExpr) (bad : Syntax.Block) (o : Resolved.DeclarationId) (n : Nat)
    (a b : Core.Ty) (body : Core.Expr) (captured : Core.Environment) (v ignored : Core.Value)
    (initial final : Core.Store) (bodyCost : Nat)
    (actualRaw : Core.Evaluates (v::captured) initial body ignored final)
    (actualCost : Core.Steps bodyCost (.initial body (v::captured) initial) (.final ignored final))
    (r : Rows v (.closure a b body captured)) :
    let names := LocalNameTable.mapIds (ownerLocalIdMap mapping) r.names
    let env := Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) r.env
    RecursiveComputationReturnTreeEvaluates (mapping o) names env initial ⟨s,statements s annotation bad n⟩ v final ∧
    RecursiveComputationReturnTreeEvaluatesWithCost (mapping o) names env initial ⟨s,statements s annotation bad n⟩ v final (6*n+bodyCost+25) :=
  ⟨(computationReturnTreeEvaluates_mapOwner_iff mapping injective
      (recursiveLocalComputationEvaluates_mapIds_iff _ (ownerLocalIdMap_injective mapping injective))).mpr
      (originalRaw s annotation bad o n a b body captured v ignored initial final actualRaw r),
    (computationReturnTreeEvaluatesWithCost_mapOwner_iff mapping injective
      (recursiveLocalComputationEvaluatesWithCost_mapIds_iff _ (ownerLocalIdMap_injective mapping injective))).mpr
      (originalCost s annotation bad o n a b body captured v ignored initial final bodyCost actualCost r)⟩
theorem whole_success_absence_is_reflected_without_classifying_faults
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (injective : Function.Injective mapping)
    (o : Resolved.DeclarationId) (names : LocalNameTable) (env : Resolved.Environment) (s : Core.Store) (body : Syntax.Block) :
    (¬ ∃ v t, RecursiveComputationReturnTreeEvaluates (mapping o) (LocalNameTable.mapIds (ownerLocalIdMap mapping) names)
      (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) env) s body v t) ↔
    (¬ ∃ v t, RecursiveComputationReturnTreeEvaluates o names env s body v t) := by
  simp only [computationReturnTreeEvaluates_mapOwner_iff mapping injective
    (recursiveLocalComputationEvaluates_mapIds_iff _ (ownerLocalIdMap_injective mapping injective))]
theorem every_exact_cost_is_reflected_separately
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (injective : Function.Injective mapping)
    (o : Resolved.DeclarationId) (names : LocalNameTable) (env : Resolved.Environment)
    (s t : Core.Store) (body : Syntax.Block) (v : Core.Value) (cost : Nat) :
    RecursiveComputationReturnTreeEvaluatesWithCost (mapping o) (LocalNameTable.mapIds (ownerLocalIdMap mapping) names)
      (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) env) s body v t cost ↔
    RecursiveComputationReturnTreeEvaluatesWithCost o names env s body v t cost :=
  computationReturnTreeEvaluatesWithCost_mapOwner_iff mapping injective
    (recursiveLocalComputationEvaluatesWithCost_mapIds_iff _ (ownerLocalIdMap_injective mapping injective))
private def alignedInputs (o : Resolved.DeclarationId) (a b : Core.Ty) : LocalTypeInputs :=
  ⟨[⟨"x",⟨o,0⟩,a⟩,⟨"f",⟨o,1⟩,.function a b⟩],by simp⟩
private def alignedRows (o : Resolved.DeclarationId) (v f : Core.Value) : Rows v f :=
  ⟨[("x",⟨o,0⟩),("f",⟨o,1⟩)],[(⟨o,0⟩,v),(⟨o,1⟩,f)],⟨o,0⟩,⟨o,1⟩,
    .head,.tail (by decide) .head,.head,.tail (by simp) .head⟩
private def guardCore : Core.Expr := .binary .wordEq (.word zero) (.word zero)
private def matchCore : Core.Expr := .letE (.word zero) (.ifE (.binary .wordEq (.var 0) (.word one)) (.var 1) (.var 1))
private def beforeDiscard : Core.Expr := .ifE guardCore matchCore (.var 0)
private def literalCore : Core.Expr := .letE (.apply (.var 1) (.var 0))
  (.ifE guardCore (.letE (.word zero) (.ifE (.binary .wordEq (.var 0) (.word one)) (.var 2) (.var 2))) (.var 1))
private theorem alignedElab (s : Syntax.SourceSpan) (annotation : Syntax.TypeExpr)
    (o : Resolved.DeclarationId) (a b : Core.Ty) :
    RecursiveComputationReturnTreeElaborates [] o (alignedInputs o a b)
      ⟨s,statements s annotation (returned s) 0⟩ literalCore a := by
  have leaf : RecursiveLocalComputationElaborates (alignedInputs o a b).names (alignedInputs o a b).context (ref s "x") (.var 0) a :=
    .pure (.identifier .head) (.var .head) (.var .head)
  have branch : RecursiveComputationReturnTreeElaborates [] o (alignedInputs o a b) (matched s (returned s)) matchCore a := by
    refine .wordMatch (entries := [(literalArm s (returned s),some one,.var 0),(wildArm s,none,.var 0)])
      (defaultEntry := some (returned s,.var 0)) (.pure (.wordLiteral (denotes s)) .word .word) rfl ?_ (.inl rfl) ?_ rfl ?_ ?_
    · intro entry member
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl
      · exact .literal ⟨_,rfl,.decimal (by decide) (.cons (.decimal (digit := 1) (by decide) rfl) .nil)⟩
      · exact .group (.wildcard rfl)
    · intro entry member
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl <;> exact .expression leaf
    · intro entry member
      simp only [Option.toList_some,List.mem_singleton] at member
      subst entry; exact .expression leaf
    · simp [Core.Expr.weakenAt]
  have shifted : beforeDiscard.weakenAt 0= .ifE guardCore
      (.letE (.word zero) (.ifE (.binary .wordEq (.var 0) (.word one)) (.var 2) (.var 2))) (.var 1) := by
    simp [beforeDiscard,matchCore,guardCore,Core.Expr.weakenAt]
  change RecursiveComputationReturnTreeElaborates _ _ _ _ (.letE _ _) _
  rw [← shifted]
  exact .discard (.application (.pure (.identifier (.tail (by change ("x" : String)≠"f"; decide) .head)) (.var (.tail (by simp) .head)) (.var (.tail (by simp) .head))) leaf)
    (.conditional (.pure (.equal (.wordLiteral (denotes s)) (.wordLiteral (denotes s))) (.binary .word .word) (.binary .word .word))
      (computationBlockPreservesNames_iff.mp (by simp only [matched,computationBlockPreservesNames])) branch (.expression leaf))
private theorem literalPath (a b : Core.Ty) (body : Core.Expr) (captured : Core.Environment)
    (v ignored : Core.Value) (s t : Core.Store) (cost : Nat)
    (actual : Core.Steps cost (.initial body (v::captured) s) (.final ignored t)) (k : List Core.Frame) :
    Core.Steps (cost+25) ⟨.eval literalCore [v,.closure a b body captured],k,s⟩ ⟨.ret v,k,t⟩ := by
  have count : cost+25=(1+1+cost+3)+(5+(1+(5+1+2)+2)+2)+2 := by omega
  rw [count]
  exact CostStepComposition.letE (valueCost := 1+1+cost+3) (bodyCost := 18)
    (CostStepComposition.apply (.cons (.var rfl) .refl) (.cons (.var rfl) .refl) actual)
    (CostStepComposition.ifTrue (conditionCost := 5) (branchCost := 11) (CostStepComposition.binary (.cons .word .refl) (.cons .word .refl) rfl)
      (CostStepComposition.letE (.cons .word .refl)
        (CostStepComposition.ifFalse (CostStepComposition.binary (.cons (.var rfl) .refl) (.cons .word .refl) rfl)
          (.cons (.var rfl) .refl))))
theorem only_the_explicit_aligned_fixture_has_this_independent_literal_path
    (s : Syntax.SourceSpan) (annotation : Syntax.TypeExpr) (o : Resolved.DeclarationId)
    (a b : Core.Ty) (body : Core.Expr) (captured : Core.Environment) (v ignored : Core.Value)
    (initial final : Core.Store) (cost : Nat)
    (actual : Core.Steps cost (.initial body (v::captured) initial) (.final ignored final)) (k : List Core.Frame) :
    RecursiveComputationReturnTreeElaborates [] o (alignedInputs o a b)
      ⟨s,statements s annotation (returned s) 0⟩ literalCore a ∧
    Core.Steps (cost+25) ⟨.eval literalCore [v,.closure a b body captured],k,initial⟩ ⟨.ret v,k,final⟩ :=
  ⟨alignedElab s annotation o a b,literalPath a b body captured v ignored initial final cost actual k⟩
theorem aligned_full_fuel_and_saved_states_retain_the_complete_discarded_effect
    (a b : Core.Ty) (body : Core.Expr) (captured : Core.Environment) (v ignored : Core.Value)
    (s t : Core.Store) (cost fuel extra : Nat)
    (actual : Core.Steps cost (.initial body (v::captured) s) (.final ignored t)) :
    (Core.runStateful fuel (.initial literalCore [v,.closure a b body captured] s)=.done v t ↔ cost+25≤fuel) ∧
    ∀ cp, Core.runStateful fuel (.initial literalCore [v,.closure a b body captured] s)=.outOfFuel cp →
      Core.runStateful extra cp=Core.runStateful (fuel+extra) (.initial literalCore [v,.closure a b body captured] s) :=
  ⟨(literalPath a b body captured v ignored s t cost actual []).runStateful_done_iff,fun _ stopped => Core.runStateful_resume stopped extra⟩
theorem one_actual_allocation_survives_any_number_of_shadowing_lets
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (injective : Function.Injective mapping)
    (s : Syntax.SourceSpan) (annotation : Syntax.TypeExpr) (bad : Syntax.Block) (o : Resolved.DeclarationId)
    (n : Nat) (a : Core.Ty) (v : Core.Value) (captured : Core.Environment) (store : Core.Store) :
    let r := alignedRows o v (.closure a (.cell a) (.newCell a (.var 0)) captured)
    RecursiveComputationReturnTreeEvaluatesWithCost (mapping o) (LocalNameTable.mapIds (ownerLocalIdMap mapping) r.names)
      (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) r.env) store ⟨s,statements s annotation bad n⟩ v (store++[v]) (6*n+28) := by
  have actual : Core.Steps 3 (.initial (.newCell a (.var 0)) (v::captured) store) (.final (.cellRef a store.length) (store++[v])) :=
    .cons .enterNewCell (.cons (.var rfl) (.cons .applyNewCell .refl))
  simpa only [Nat.add_assoc] using (owner_change_preserves_both_raw_interfaces_and_the_discarded_effects mapping injective
    s annotation bad o n a (.cell a) (.newCell a (.var 0)) captured v (.cellRef a store.length) store (store++[v]) 3
    (Core.steps_from_initial_sound actual) actual (alignedRows o v (.closure a (.cell a) (.newCell a (.var 0)) captured))).2
theorem discarded_closure_completes_before_the_pending_body_resumes
    (a b : Core.Ty) (body : Core.Expr) (captured : Core.Environment) (v ignored : Core.Value)
    (s t : Core.Store) (cost : Nat) (k : List Core.Frame)
    (actual : Core.Steps cost (.initial body (v::captured) s) (.final ignored t)) :
    ∃ cp, cp.control=.ret ignored ∧ cp.store=t ∧
      Core.runStateful (cost+6) ⟨.eval literalCore [v,.closure a b body captured],k,s⟩=.outOfFuel cp ∧
      ∀ extra, Core.runStateful extra cp=Core.runStateful (cost+6+extra) ⟨.eval literalCore [v,.closure a b body captured],k,s⟩ := by
  let cp : Core.State := ⟨.ret ignored,.letBody (.ifE guardCore
    (.letE (.word zero) (.ifE (.binary .wordEq (.var 0) (.word one)) (.var 2) (.var 2))) (.var 1))
    [v,.closure a b body captured]::k,t⟩
  have beforePath : Core.Steps ((1+1+cost+3)+1) ⟨.eval literalCore [v,.closure a b body captured],k,s⟩ cp :=
    .cons .enterLet (CostStepComposition.apply (.cons (.var rfl) .refl) (.cons (.var rfl) .refl) actual)
  have path : Core.Steps (cost+6) ⟨.eval literalCore [v,.closure a b body captured],k,s⟩ cp := by
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using beforePath
  have stopped := Core.runStateful_outOfFuel_complete path (show Core.advance _=.next _ from rfl)
  exact ⟨_,rfl,rfl,stopped,Core.runStateful_resume stopped⟩
private def delayed (a : Core.Ty) : Nat → Core.Expr
  | 0 => .newCell a (.var 0)
  | m+1 => .letE (.var 0) (delayed a m)
private theorem delayedPath (a : Core.Ty) (m : Nat) (v : Core.Value) (captured : Core.Environment)
    (s : Core.Store) (k : List Core.Frame) :
    Core.Steps (3*m+3) ⟨.eval (delayed a m) (v::captured),k,s⟩ ⟨.ret (.cellRef a s.length),k,s++[v]⟩ := by
  induction m generalizing captured k with
  | zero => exact .cons .enterNewCell (.cons (.var rfl) (.cons .applyNewCell .refl))
  | succ m ih =>
      have count : 3*(m+1)+3=1+(3*m+3)+2 := by omega
      rw [count]; exact CostStepComposition.letE (.cons (.var rfl) .refl) (ih (v::captured) k)
theorem a_fixed_original_body_has_unbounded_actual_cost_and_a_retained_allocation
    (s : Syntax.SourceSpan) (annotation : Syntax.TypeExpr) (bad : Syntax.Block) (o : Resolved.DeclarationId)
    (a : Core.Ty) (v : Core.Value) (captured : Core.Environment) (store : Core.Store) (bound : Nat) :
    ∃ m, bound<3*m+28 ∧
      let r := alignedRows o v (.closure a (.cell a) (delayed a m) captured)
      RecursiveComputationReturnTreeEvaluatesWithCost o r.names r.env store
        ⟨s,statements s annotation bad 0⟩ v (store++[v]) (3*m+28) := by
  refine ⟨bound,by omega,?_⟩
  simpa only [Nat.mul_zero,Nat.zero_add,Nat.add_assoc] using originalCost s annotation bad o 0 a (.cell a)
    (delayed a bound) captured v (.cellRef a store.length) store (store++[v]) (3*bound+3)
    (delayedPath a bound v captured store []) (alignedRows o v (.closure a (.cell a) (delayed a bound) captured))
end Tests.FrontendComputationBodyRawOwner
