import Solcore.Frontend.ClosedSourceDataBodyDepthBound
import Solcore.Frontend.ClosedSourceDataDepthBoundProperties
import Solcore.Frontend.ClosedSourceDataBody

/- Direct syntax induction retains original body derivations and all mixed
lexical/store endpoints. Fresh binding changes the induction inputs literally.
Written-arm maxima bound selection, not the number of visited comparisons. -/
set_option autoImplicit false
namespace Solcore.Frontend

private theorem selected_property {actual : RuntimeValue} {cases : List Syntax.MatchCase}
    {defaultBody : Option Syntax.Block} {selected : Syntax.Block} {tests : Nat}
    (choice : RuntimeWordMatchChooses actual cases defaultBody selected tests)
    {P : Syntax.Block → Prop} (branches : ∀ arm ∈ cases, P arm.value.body)
    (fallback : ∀ source ∈ defaultBody.toList, P source) : P selected := by
  induction choice with
  | fallback => exact fallback _ (by simp)
  | wildcard _ => exact branches _ List.mem_cons_self
  | hit _ => exact branches _ List.mem_cons_self
  | miss _ _ _ ih => exact ih (fun arm member => branches arm (List.mem_cons_of_mem _ member)) fallback

private theorem selected_depth_le {actual : RuntimeValue} {cases : List Syntax.MatchCase}
    {defaultBody : Option Syntax.Block} {selected : Syntax.Block} {tests : Nat}
    (choice : RuntimeWordMatchChooses actual cases defaultBody selected tests) :
    closedSourceDataBodyDepthBound selected ≤ closedSourceDataMatchDepthBound cases defaultBody := by
  induction choice with
  | fallback => rw [closedSourceDataMatchDepthBound]; exact Nat.le_refl _
  | wildcard _ => rw [closedSourceDataMatchDepthBound]; exact Nat.le_max_left _ _
  | hit _ => rw [closedSourceDataMatchDepthBound]; exact Nat.le_max_left _ _
  | miss _ _ _ ih =>
      rw [closedSourceDataMatchDepthBound]
      exact Nat.le_trans ih (Nat.le_max_right _ _)

/-- Every original successful gated body derivation is found at its syntax-only
upper depth and every larger budget, with the complete actual result and store. -/
theorem ClosedSourceDataBody.evaluates_at_depthBound
    {body : Syntax.Block} (fragment : ClosedSourceDataBody body)
    {owner : Resolved.DeclarationId} {names : LocalNameTable}
    {captured : Resolved.LocalScope RuntimeValue}
    {initialStore finalStore : List RuntimeValue} {value : RuntimeValue}
    (evaluated : ClosedSourceBodyEvaluates owner names captured
      initialStore body value finalStore)
    {budget : Nat} (enough : closedSourceDataBodyDepthBound body ≤ budget) :
    evaluateClosedSourceBody? budget owner names captured initialStore body =
      some (value, finalStore) := by
  induction fragment generalizing owner names captured initialStore finalStore value budget with
  | bare =>
      rw [closedSourceDataBodyDepthBound] at enough
      cases budget with
      | zero => omega
      | succ n =>
          cases evaluated with
          | bare => simp only [evaluateClosedSourceBody?]
  | expression admitted =>
      rw [closedSourceDataBodyDepthBound] at enough
      cases budget with
      | zero => omega
      | succ n =>
          cases evaluated with
          | expression child =>
              simpa only [evaluateClosedSourceBody?] using
                admitted.evaluates_at_depthBound child (by omega : _ ≤ n)
  | block _ ih =>
      rw [closedSourceDataBodyDepthBound] at enough
      cases budget with
      | zero => omega
      | succ n =>
          cases evaluated with
          | block child =>
              simpa only [evaluateClosedSourceBody?] using ih child (by omega : _ ≤ n)
  | binding admitted _ ih =>
      rw [closedSourceDataBodyDepthBound] at enough
      cases budget with
      | zero => omega
      | succ n =>
          cases evaluated with
          | binding initializer tail =>
              have initialized := admitted.evaluates_at_depthBound initializer (by omega : _ ≤ n)
              simpa only [evaluateClosedSourceBody?, initialized, bind, Option.bind_some] using
                ih tail (by omega : _ ≤ n)
          | inferred initializer tail =>
              have initialized := admitted.evaluates_at_depthBound initializer (by omega : _ ≤ n)
              simpa only [evaluateClosedSourceBody?, initialized, bind, Option.bind_some] using
                ih tail (by omega : _ ≤ n)
  | discard admitted _ ih =>
      rw [closedSourceDataBodyDepthBound] at enough
      cases budget with
      | zero => omega
      | succ n =>
          cases evaluated with
          | discard child tail =>
              have discarded := admitted.evaluates_at_depthBound child (by omega : _ ≤ n)
              simpa only [evaluateClosedSourceBody?, discarded, bind, Option.bind_some] using
                ih tail (by omega : _ ≤ n)
  | conditional admitted _ _ thenIH elseIH =>
      rw [closedSourceDataBodyDepthBound] at enough
      cases budget with
      | zero => omega
      | succ n =>
          cases evaluated with
          | ifTrue condition branch =>
              have tested := admitted.evaluates_at_depthBound condition (by omega : _ ≤ n)
              simpa only [evaluateClosedSourceBody?, tested, bind, Option.bind_some, ↓reduceIte] using
                thenIH branch (by omega : _ ≤ n)
          | ifFalse condition branch =>
              have tested := admitted.evaluates_at_depthBound condition (by omega : _ ≤ n)
              simpa only [evaluateClosedSourceBody?, tested, bind, Option.bind_some,
                Bool.false_eq_true, ↓reduceIte] using elseIH branch (by omega : _ ≤ n)
  | wordMatch admitted _ _ branchesIH fallbackIH =>
      rw [closedSourceDataBodyDepthBound] at enough
      cases budget with
      | zero => omega
      | succ n =>
          cases evaluated with
          | wordMatch scrutinee choice branch =>
              have tested := admitted.evaluates_at_depthBound scrutinee (by omega : _ ≤ n)
              have selectedBound := selected_depth_le choice
              have returned := selected_property choice
                (P := fun body => ∀ {scopeOwner : Resolved.DeclarationId} {scopeNames : LocalNameTable}
                  {scopeCaptured : Resolved.LocalScope RuntimeValue}
                  {initial final : List RuntimeValue} {actual : RuntimeValue},
                  ClosedSourceBodyEvaluates scopeOwner scopeNames scopeCaptured initial body actual final →
                  ∀ {depth : Nat}, closedSourceDataBodyDepthBound body ≤ depth →
                  evaluateClosedSourceBody? depth scopeOwner scopeNames scopeCaptured initial body =
                    some (actual, final))
                (fun arm member => @branchesIH arm member)
                (fun source member => @fallbackIH source member) branch (by omega : _ ≤ n)
              simpa only [evaluateClosedSourceBody?, tested, chooseRuntimeWordMatch?_iff.mpr choice,
                bind, Option.bind_some] using returned

end Solcore.Frontend
