import Solcore.Synthesis.Core.RevertData

/-! The plan size of a revert data plan and its reductions. A call weighs 20,
more than any site step, at most 19, so replacing a call by the site it
reaches is smaller; a reduction is kept only when strictly smaller. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.RevertData

open Solcore.Synthesis.Core.MemoryValues (Operand Index Ref Width Fold Part Build Action)

def operandSize : Operand → Nat
  | .input => 0
  | .acc | .counter => 1
  | .add constant | .mul constant | .xor constant => 1 + (if constant = 1 then 0 else 1)

def constantSize (constant : Nat) : Nat := if constant = 0 then 0 else if constant ≤ 3 then 1 else 2

def Test.size : Test → Nat
  | .eq constant => constantSize constant
  | .ne constant | .lt constant | .gt constant => 1 + constantSize constant
  | .bits mask value => 1 + constantSize mask + constantSize value

def Make.size : Make → Nat
  | .empty => 1
  | .selector word => 2 + operandSize word
  | .message _ => 3

def Source.size : Source → Nat
  | .make made => made.size
  | .named _ | .param => 2

def Payload.size : Payload → Nat
  | .none => 0
  | .literal text => 1 + text
  | .error origin => 1 + origin.size

def Site.size (site : Site) : Nat :=
  1 + (if site.form == .require then 1 else 0) + operandSize site.cond.word + site.cond.test.size + site.payload.size

def foldSize (fold : Fold) (constant : Nat) : Nat := (if fold == .xor then 1 else 0) + (if constant = 3 then 0 else 1)

def actionSize : Action → Nat
  | .bytes (.toBytes _) => 2
  | .bytes (.concat ..) => 3
  | .alias _ => 2
  | .write .. => 3
  | .observe .. => 3
  | _ => 3

def Helper.size : Helper → Nat
  | .raise site fold constant => 4 + site.size + foldSize fold constant
  | .make constant => 2 + constantSize constant
  | .message => 2
  | .pick test => 3 + test.size
  | .call _ constant => 3 + constantSize constant

def Decl.size : Decl → Nat
  | .make made => made.size
  | .helper _ word => 4 + operandSize word
  | .message .. => 4
  | .pick _ word first second => 5 + operandSize word + first.size + second.size

def Datum.size : Datum → Nat
  | .pair origin word | .first origin word => 3 + origin.size + operandSize word
  | .inl origin => 2 + origin.size
  | .inr word | .second word => 2 + operandSize word

def Item.size : Item → Nat
  | .action single => actionSize single
  | .site single => single.size

def Step.size : Step → Nat
  | .action single => actionSize single
  | .error decl => 2 + decl.size
  | .data datum => datum.size
  | .site single => 2 + single.size
  | .call _ origin word direct fold constant =>
      20 + origin.size + operandSize word + (if direct then 0 else 2) + foldSize fold constant
  | .take _ inner fold constant => 4 + inner.size + foldSize fold constant
  | .closure inner fold constant => 4 + inner.size + foldSize fold constant
  | .apply _ word fold constant => 3 + operandSize word + foldSize fold constant
  | .loop mask body => 4 + mask + (body.map Item.size).sum

def Plan.size (plan : Plan) : Nat := (plan.helpers.map Helper.size).sum + (plan.steps.map Step.size).sum

/-! Reductions. -/

def removeAt {α : Type} (list : List α) (index : Nat) : List α := list.take index ++ list.drop (index + 1)

/-- Simpler tests: equality with zero, then smaller constants. -/
def Test.reductions : Test → List Test
  | .eq constant => if constant = 0 then [] else [.eq 0]
  | .ne constant | .lt constant | .gt constant => [.eq 0, .eq constant]
  | .bits _ value => [.eq 0, .eq value]

def Operand.reductions (word : Operand) : List Operand :=
  if word == .input then [] else [.input]

def Make.reductions : Make → List Make
  | .empty => []
  | .selector word => [.empty] ++ (Operand.reductions word).map Make.selector
  | .message _ => [.empty]

def Source.reductions : Source → List Source
  | .make made => made.reductions.map Source.make
  | .named _ | .param => [.make .empty]

def Payload.reductions (form : Form) : Payload → List Payload
  | .none => []
  | .literal text => (if text = 0 then [] else [.literal 0]) ++ (if form == .when then [.none] else [])
  | .error origin => origin.reductions.map Payload.error ++ (if form == .when then [.none] else [])

def Site.reductions (site : Site) : List Site :=
  (site.payload.reductions site.form).map (fun payload => {site with payload}) ++
  site.cond.test.reductions.map (fun test => {site with cond := {site.cond with test}}) ++
  (Operand.reductions site.cond.word).map (fun word => {site with cond := {site.cond with word}}) ++
  (if site.form == .require then
    match site.payload with
    | .error _ => [{site with form := .when}]
    | .literal text => [{site with form := .when, payload := .literal (if literalLength text ≤ 32 then text else 0)}]
    | .none => []
  else [])

def foldReductions (fold : Fold) (constant : Nat) : List (Fold × Nat) :=
  (if fold == .xor then [(.add, constant)] else []) ++ (if constant = 3 then [] else [(fold, 3)])

def Helper.reductions : Helper → List Helper
  | .raise site fold constant =>
      site.reductions.map (fun site => .raise site fold constant) ++
      (foldReductions fold constant).map fun (fold, constant) => .raise site fold constant
  | .make constant => if constant = 1 then [] else [.make 1]
  | .message => []
  | .pick test => test.reductions.map Helper.pick
  | .call callee constant => if constant = 1 then [] else [.call callee 1]

def Decl.reductions : Decl → List Decl
  | .make made => made.reductions.map Decl.make
  | .helper _ _ | .message .. | .pick .. => [.make .empty]

def Datum.reductions : Datum → List Datum
  | .pair origin word => origin.reductions.map (fun origin => .pair origin word) ++
      (Operand.reductions word).map (Datum.pair origin)
  | .inl origin => origin.reductions.map Datum.inl
  | .inr word => (Operand.reductions word).map Datum.inr
  | .first origin word => [Datum.second word] ++ origin.reductions.map (fun origin => .first origin word)
  | .second word => (Operand.reductions word).map Datum.second

/-- The site a call reaches, with its parameter replaced by the call's
argument and its Word by the input, as a site of `run`. -/
def callSite (helpers : List Helper) (helper : Nat) (origin : Source) : Option Site := do
  let (site, _, _, _) ← resolve helpers (maximumHelpers + 1) helper
  let payload := match site.payload with
    | .error .param => .error origin
    | .error (.make (.selector _)) => .error (.make (.selector .input))
    | payload => payload
  return {site with payload, cond := {site.cond with word := .input}}

def Step.reductions (helpers : List Helper) : Step → List Step
  | .action _ => []
  | .error decl => decl.reductions.map Step.error
  | .data datum => datum.reductions.map Step.data
  | .site single => single.reductions.map Step.site
  | .call helper origin word direct fold constant =>
      ((callSite helpers helper origin).map Step.site).toList ++
      (if direct then [] else [.call helper origin word true fold constant]) ++
      origin.reductions.map (fun origin => .call helper origin word direct fold constant) ++
      (Operand.reductions word).map (fun word => .call helper origin word direct fold constant) ++
      (foldReductions fold constant).map fun (fold, constant) => .call helper origin word direct fold constant
  | .take held inner fold constant =>
      inner.reductions.map (fun reduced => .take held reduced fold constant) ++
      (foldReductions fold constant).map fun (fold, constant) => .take held inner fold constant
  | .closure inner fold constant =>
      inner.reductions.map (fun reduced => .closure reduced fold constant) ++
      (foldReductions fold constant).map fun (fold, constant) => .closure inner fold constant
  | .apply number word fold constant =>
      (Operand.reductions word).map (fun word => .apply number word fold constant) ++
      (foldReductions fold constant).map fun (fold, constant) => .apply number word fold constant
  | .loop mask body =>
      (if mask = 1 then [] else [.loop (if mask = 7 then 3 else 1) body]) ++
      ((List.range body.length).filterMap fun index =>
        if body.length > 1 then some (.loop mask (removeAt body index)) else none) ++
      (List.range body.length).flatMap fun index => match (body[index]? : Option Item) with
        | some (Item.site inner) => inner.reductions.map fun reduced => .loop mask (body.set index (Item.site reduced))
        | _ => []

/-- References to helpers after one is removed: later ones move down. -/
def shiftHelper (removed index : Nat) : Nat := if index > removed then index - 1 else index

def Step.usesHelper (helper : Nat) : Step → Bool
  | .error (.helper target _) | .error (.message target _) | .error (.pick target ..) => target == helper
  | .call target .. => target == helper
  | _ => false

def Step.shiftHelpers (removed : Nat) : Step → Step
  | .error (.helper target word) => .error (.helper (shiftHelper removed target) word)
  | .error (.message target value) => .error (.message (shiftHelper removed target) value)
  | .error (.pick target word first second) => .error (.pick (shiftHelper removed target) word first second)
  | .call target origin word direct fold constant => .call (shiftHelper removed target) origin word direct fold constant
  | step => step

def Helper.shift (removed : Nat) : Helper → Helper
  | .call callee constant => .call (shiftHelper removed callee) constant
  | helper => helper

def Helper.calls (helper : Nat) : Helper → Bool
  | .call callee _ => callee == helper
  | _ => false

/-- The plan's reductions: remove a step, remove a helper nothing calls, then
each step's and helper's own. Admission is checked when a reduction is
sealed. -/
def planReductions (plan : Plan) : List Plan :=
  ((List.range plan.steps.length).map fun index => {plan with steps := removeAt plan.steps index}) ++
  ((List.range plan.helpers.length).filterMap fun index =>
    if plan.steps.any (·.usesHelper index) || plan.helpers.any (·.calls index) then none
    else some {helpers := (removeAt plan.helpers index).map (Helper.shift index),
               steps := plan.steps.map (Step.shiftHelpers index)}) ++
  ((List.range plan.steps.length).flatMap fun index =>
    ((plan.steps.getD index default).reductions plan.helpers).map fun step => {plan with steps := plan.steps.set index step}) ++
  ((List.range plan.helpers.length).flatMap fun index =>
    (plan.helpers.getD index default).reductions.map fun helper => {plan with helpers := plan.helpers.set index helper})

end Solcore.Synthesis.Core.RevertData
