import Solcore.Synthesis.Core.MemoryCalls
import Solcore.Synthesis.Core.MemoryValuesShrink

/-! Reductions of memory call plans. A candidate is kept only when the plan
is admitted and strictly smaller: in its structure first, then in the sum of
its numeric literals. A call weighs more than the actions it amounts to, so
inlining one is a reduction. Removing a declaration or a helper renumbers what
comes after it; a candidate that would still refer to it is not formed. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.MemoryCalls

open Solcore.Synthesis.Core.MemoryValues (Operand Index Ref Fold Width)

private def plus (left right : Nat × Nat) : Nat × Nat := (left.1 + right.1, left.2 + right.2)

private def observed (obs : Obs) (fold : Fold) : Nat :=
  (if obs == .length then 1 else 2) + (if fold == .xor then 1 else 0)

def Kind.size : Kind → Nat × Nat
  | .read obs fold => (observed obs fold, 0)
  | .write width => (if width == .byte then 2 else 1, 0)
  | .view start => (1, start)
  | .copy => (1, 0)
  | .call callee constant => (2, callee + constant)
  | .pack constant => (1, constant)
  | .take obs fold written => (observed obs fold + (if written then 1 else 0), 0)

def Param.size : Param → Nat
  | .generic => 2
  | _ => 1

def Helper.size (helper : Helper) : Nat × Nat := plus (1 + helper.param.size, 0) helper.kind.size

def Datum.size : Datum → Nat × Nat
  | .pair _ word | .first _ word => plus (4, 0) word.size
  | .inl _ => (4, 0)
  | .inr word | .second word => plus (2, 0) word.size

def Step.size : Step → Nat × Nat
  | .action single => plus (1, 0) single.size
  | .call helper _ index word form fold constant =>
      plus (6 + (if form == .value then 1 else 0) + (if fold == .xor then 1 else 0), helper + constant)
        (plus index.size word.size)
  | .data datum => datum.size
  | .closure _ obs => (if obs == .length then 2 else 3, 0)
  | .apply number index fold constant => plus (2 + (if fold == .xor then 1 else 0), number + constant) index.size

/-- Structure first, then literals; literals stay far below `2 ^ 16`. -/
def Plan.size (plan : Plan) : Nat :=
  let total := (plan.helpers.map Helper.size ++ plan.steps.map Step.size).foldl plus (0, 0)
  total.1 * 2 ^ 16 + total.2

/-! Renumbering and substitution. -/

/-- What a step declares, by kind: `bytes`, `slice`, `array`, `pair`, `sum`,
`enum` or `closure`. A function value is named by its position alone. -/
def Step.declares (helpers : List Helper) : Step → Option String
  | .action single => single.declares {}
  | .call helper arg .. => match resultAt helpers helper arg.kinded with
      | some .bytes => some "bytes"
      | some .slice => some "slice"
      | some .array => some "array"
      | some .pair => some "pair"
      | _ => none
  | .data (.pair ..) => some "pair"
  | .data (.inl _) | .data (.inr _) => some "sum"
  | .data (.first ..) | .data (.second _) => some "enum"
  | .closure .. => some "closure"
  | .apply .. => none

private def renumberNumber (removed number : Nat) : Option Nat :=
  if number < removed then some number else if number == removed then none else some (number - 1)

def Arg.renumber (kind : String) (removed : Nat) : Arg → Option Arg
  | .value ref => (ref.renumber kind removed 1).map .value
  | .pair number => if kind == "pair" then (renumberNumber removed number).map .pair else some (.pair number)
  | .sum number => if kind == "sum" then (renumberNumber removed number).map .sum else some (.sum number)
  | .enum number => if kind == "enum" then (renumberNumber removed number).map .enum else some (.enum number)

def Step.renumber (kind : String) (removed : Nat) : Step → Option Step
  | .action single => (single.renumber kind removed 1).map .action
  | .call helper arg index word form fold constant => do
      return .call helper (← arg.renumber kind removed) index word form fold constant
  | .data (.pair ref word) => do return .data (.pair (← ref.renumber kind removed 1) word)
  | .data (.inl ref) => do return .data (.inl (← ref.renumber kind removed 1))
  | .data (.first ref word) => do return .data (.first (← ref.renumber kind removed 1) word)
  | .data datum => some (.data datum)
  | .closure ref obs => do return .closure (← ref.renumber kind removed 1) obs
  | .apply number index fold constant =>
      if kind == "closure" then do return .apply (← renumberNumber removed number) index fold constant
      else some (.apply number index fold constant)

private def mapPart (f : Ref → Ref) : MemoryValues.Part → MemoryValues.Part
  | .value ref => .value (f ref)
  | part => part

private def mapAction (f : Ref → Ref) : MemoryValues.Action → MemoryValues.Action
  | .bytes (.toBytes part) => .bytes (.toBytes (mapPart f part))
  | .bytes (.concat left right) => .bytes (.concat (mapPart f left) (mapPart f right))
  | .slice source cut => .slice (f source) cut
  | .alias source => .alias (f source)
  | .write target index value width form => .write (f target) index value width form
  | .observe fold constant value access => .observe fold constant (f value) access
  | action => action

/-- Every memory variable a step names, mapped. -/
def Step.mapRefs (f : Ref → Ref) : Step → Step
  | .action single => .action (mapAction f single)
  | .call helper (.value ref) index word form fold constant => .call helper (.value (f ref)) index word form fold constant
  | .data (.pair ref word) => .data (.pair (f ref) word)
  | .data (.inl ref) => .data (.inl (f ref))
  | .data (.first ref word) => .data (.first (f ref) word)
  | .closure ref obs => .closure (f ref) obs
  | step => step

/-- The number a step's declaration gets: its kind's declarations before it. -/
def Plan.declaredBefore (plan : Plan) (index : Nat) (kind : String) : Nat :=
  ((plan.steps.take index).filter fun step => step.declares plan.helpers == some kind).length

/-! Plan reductions. -/

/-- Drop a step, a call among them. -/
def Plan.removeStep (plan : Plan) (index : Nat) : Option Plan := do
  let step ← plan.steps[index]?
  let rest := plan.steps.drop (index + 1)
  let rest ← match step.declares plan.helpers with
    | some kind => rest.mapM (·.renumber kind (plan.declaredBefore index kind))
    | none => some rest
  return {plan with steps := plan.steps.take index ++ rest}

/-- Replace the value a writing call returns by its argument: the write stays
as the action it amounts to, and every later use of the result names the
argument. -/
def Plan.passThrough (plan : Plan) (index : Nat) : Option Plan := do
  let step ← plan.steps[index]?
  let .call helper (.value ref) indexValue word .. := step | none
  let (base, _) ← resolve plan.helpers (maximumHelpers + 1) helper
  let .write width := base.kind | none
  let kind ← step.declares plan.helpers
  let result := plan.declaredBefore index kind
  let substitute := fun (target : Ref) => if target.kind == kind && target.number == result then ref else target
  let rest ← (plan.steps.drop (index + 1)).mapM fun later => (later.mapRefs substitute).renumber kind result
  return {plan with steps := plan.steps.take index ++ [.action (.write ref indexValue word width .inline)] ++ rest}

/-- A call written as the `runtime-memory-values` actions its base kind
amounts to, when its argument is a memory variable; a value result keeps its
declaration. -/
def Plan.inlineCall (plan : Plan) (index : Nat) : Option Plan := do
  let .call helper (.value ref) indexValue word _ fold constant ← plan.steps[index]? | none
  let (base, _) ← resolve plan.helpers (maximumHelpers + 1) helper
  let replacement : List Step ← match base.kind with
    | .read obs _ => some [.action (.observe fold constant ref (Compiler.obsAccess obs indexValue))]
    | .view start => some [.action (.slice ref (.drop start))]
    | .copy => some [.action (.bytes (.concat (.value ref) (.word word)))]
    | .write width =>
        let declare : MemoryValues.Action := if ref.isSlice then .slice ref (.drop 0) else .alias ref
        some [.action (.write ref indexValue word width .inline), .action declare]
    | .pack _ => some [.data (.pair ref word)]
    | _ => none
  return {plan with steps := plan.steps.take index ++ replacement ++ plan.steps.drop (index + 1)}

/-- Call a `call` helper's callee directly. -/
def Plan.bypass (plan : Plan) (index : Nat) : Option Plan := do
  let .call helper arg indexValue word form fold constant ← plan.steps[index]? | none
  let target ← plan.helpers[helper]?
  let .call callee _ := target.kind | none
  return {plan with steps := plan.steps.set index (.call callee arg indexValue word form fold constant)}

/-- Remove a helper no step and no other helper calls, renumbering the rest. -/
def Plan.removeHelper (plan : Plan) (index : Nat) : Option Plan := do
  let called := plan.steps.any fun step => match step with
    | .call helper .. => helper == index
    | _ => false
  let chained := plan.helpers.any fun helper => match helper.kind with
    | .call callee _ => callee == index
    | _ => false
  if called || chained || index ≥ plan.helpers.length then none
  let shift := fun (number : Nat) => if number > index then number - 1 else number
  let helpers := (plan.helpers.eraseIdx index).map fun helper => match helper.kind with
    | .call callee constant => {helper with kind := .call (shift callee) constant}
    | _ => helper
  let steps := plan.steps.map fun step => match step with
    | .call helper arg indexValue word form fold constant => .call (shift helper) arg indexValue word form fold constant
    | other => other
  return {helpers, steps}

/-! Local reductions of helpers and steps. -/

def Kind.reductions : Kind → List Kind
  | .read obs fold =>
      (if fold == .xor then [.read obs .add] else []) ++
        (if obs != .length && obs != .element then [.read .length fold] else [])
  | .write .byte => [.write .word]
  | .write .word => []
  | .view start => if start = 0 then [] else [.view 0]
  | .copy => []
  | .call callee constant => if constant > 1 then [.call callee 1] else []
  | .pack constant => if constant > 1 then [.pack 1] else []
  | .take obs fold written =>
      (if written then [.take obs fold false] else []) ++ (if fold == .xor then [.take obs .add written] else []) ++
        (if obs != .length then [.take .length fold written] else [])

def Helper.reductions (helper : Helper) : List Helper :=
  (if helper.param == .generic then [{helper with param := .bytes}, {helper with param := .slice}] else []) ++
    helper.kind.reductions.map fun kind => {helper with kind}

def Step.reductions : Step → List Step
  | .action single => single.reductions.map .action
  | .call helper arg index word form fold constant =>
      (if form == .value then [.call helper arg index word .direct fold constant] else []) ++
      (if fold == .xor then [.call helper arg index word form .add constant] else []) ++
      (if constant > 3 then [.call helper arg index word form fold 3] else []) ++
      index.reductions.map (fun reduced => .call helper arg reduced word form fold constant) ++
      word.reductions.map (fun reduced => .call helper arg index reduced form fold constant)
  | .data (.pair ref word) => word.reductions.map fun reduced => .data (.pair ref reduced)
  | .data (.inl _) => [.data (.inr .input)]
  | .data (.inr word) => word.reductions.map fun reduced => .data (.inr reduced)
  | .data (.first ref word) => .data (.second word) :: word.reductions.map fun reduced => .data (.first ref reduced)
  | .data (.second word) => word.reductions.map fun reduced => .data (.second reduced)
  | .closure ref obs => if obs == .length || obs == .element then [] else [.closure ref .length]
  | .apply number index fold constant =>
      (if fold == .xor then [.apply number index .add constant] else []) ++
      (if constant > 3 then [.apply number index fold 3] else []) ++
      index.reductions.map fun reduced => .apply number reduced fold constant

def planReductions (plan : Plan) : List Plan := Id.run do
  let mut result : List Plan := []
  for index in List.range plan.steps.length do
    for candidate in [plan.removeStep index, plan.passThrough index, plan.inlineCall index, plan.bypass index] do
      if let some reduced := candidate then result := result ++ [reduced]
  for index in List.range plan.helpers.length do
    if let some reduced := plan.removeHelper index then result := result ++ [reduced]
  for (helper, index) in plan.helpers.zipIdx do
    result := result ++ helper.reductions.map fun reduced => {plan with helpers := plan.helpers.set index reduced}
  for (step, index) in plan.steps.zipIdx do
    result := result ++ step.reductions.map fun reduced => {plan with steps := plan.steps.set index reduced}
  return result.filter fun candidate => candidate.admitted && candidate.size < plan.size

end Solcore.Synthesis.Core.MemoryCalls
