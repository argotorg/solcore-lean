import Solcore.Synthesis.Core.Integers

/-! Plan size and reductions of the integer plans. Every candidate is strictly
smaller in `Plan.size` and must still be admitted by its profile and pass the
full Core checker; that sealing is the cases module's. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.Integers

def Op.weight (op : Op) : Nat := if op == Op.add then 0 else 1

namespace Operand

/-- `sc_a0` weighs nothing, another input or a variable 1, a literal 1 and a
literal other than zero 2. -/
def weight (type : IntType) : Operand → Nat
  | .input 0 => 0
  | .input _ | .var _ => 1
  | .literal index => if type.literals.getD index 0 == 0 then 1 else 2

/-- The variable `removed` no longer exists: a reference to it reads `sc_a0`,
a later one the variable before it. -/
def without (removed : Nat) : Operand → Operand
  | .var index => if index = removed then .input 0 else if index > removed then .var (index - 1) else .var index
  | other => other

end Operand

def Amount.weight : Amount → Nat
  | .input _ => 1
  | .literal index => if index = 0 then 0 else 1

namespace Form

def weight (type : IntType) : Form → Nat
  | .binary op left right => 3 + op.weight + left.weight type + right.weight type
  | .neg operand => 3 + operand.weight type
  | .compound op left right => 4 + op.weight + left.weight type + right.weight type
  | .call _ left right => 6 + left.weight type + right.weight type
  | .apply op body left right => 6 + op.weight + (if body then 1 else 0) + left.weight type + right.weight type

def map (operand : Operand → Operand) : Form → Form
  | .binary op left right => .binary op (operand left) (operand right)
  | .neg value => .neg (operand value)
  | .compound op left right => .compound op (operand left) (operand right)
  | .call helper left right => .call helper (operand left) (operand right)
  | .apply op body left right => .apply op body (operand left) (operand right)

end Form

def Default.weight (made : Default) : Nat := 5 + made.op.weight

def Shift.weight (type : IntType) (shift : Shift) : Nat :=
  3 + (if shift.compound then 1 else 0) + shift.value.weight type + shift.amount.weight

namespace Step

def weight (type : IntType) : Step → Nat
  | .assign form => form.weight type
  | .default made => made.weight
  | .shift value => value.weight type

def isVar : Step → Bool
  | .default _ => false
  | _ => true

def map (operand : Operand → Operand) : Step → Step
  | .assign form => .assign (form.map operand)
  | .default made => .default made
  | .shift value => .shift {value with value := operand value.value}

end Step

namespace Plan

/-- The plan size: every step's weight, one more for each step in a block,
each input after the first, amount and helper, an unchecked helper, `run(T)`
and a `T` result. -/
def size (plan : Plan) : Nat :=
  let type := plan.type
  (plan.steps.map fun (unchecked, step) => step.weight type + (if unchecked then 1 else 0)).foldl (· + ·) 0 +
    (plan.inputs.length - 1) + plan.amounts.length +
    (plan.helpers.map fun helper => 1 + helper.op.weight + (if helper.unchecked then 1 else 0)).foldl (· + ·) 0 +
    (if plan.abi then 1 else 0) + (if plan.raw then 1 else 0)

/-- The step at `index` removed, later references to its variable reading
`sc_a0`. -/
def removeStep (plan : Plan) (index : Nat) : Plan :=
  let steps := plan.steps
  match steps[index]? with
  | none => plan
  | some (_, step) =>
      let removedVar := (steps.take index).countP fun (_, earlier) => earlier.isVar
      let kept := (steps.take index) ++ (steps.drop (index + 1)).map fun (unchecked, later) =>
        (unchecked, if step.isVar then later.map (Operand.without removedVar) else later)
      plan.withSteps kept

def replaceStep (plan : Plan) (index : Nat) (step : Bool × Step) : Plan :=
  plan.withSteps (plan.steps.set index step)

/-- The simpler forms of one step: `add` for its operation, an inline
operation for a compound assignment, a call or a lambda, a checked lambda body,
`sc_a0` or a zero literal for an operand, an inline shift, a zero amount, and
the checked context. -/
def stepReductions (plan : Plan) (unchecked : Bool) (step : Step) : List (Bool × Step) :=
  let operands (operand : Operand) : List Operand := match operand with
    | .input 0 => []
    | .literal index =>
        let zeroIndex := (plan.type.literals.idxOf? 0).getD 0
        [.input 0] ++ (if index == zeroIndex then [] else [.literal zeroIndex])
    | _ => [.input 0]
  let forms : List Step := match step with
    | .assign form => (match form with
        | .binary op left right =>
            (if op == Op.add then [] else [Form.binary Op.add left right]) ++
              (operands left).map (Form.binary op · right) ++ (operands right).map (Form.binary op left ·)
        | .neg operand => (operands operand).filterMap fun lowered =>
            if lowered matches Operand.literal _ then none else some (Form.neg lowered)
        | .compound op left right => [Form.binary op left right]
        | .call helper left right => [Form.binary (plan.helpers.getD helper default).op left right]
        | .apply op body left right =>
            [Form.binary op left right] ++ (if body then [Form.apply op false left right] else []) ++
              (if op == Op.add then [] else [Form.apply Op.add body left right])).map Step.assign
    | .default made => if made.op == Op.add then [] else [.default {made with op := Op.add}]
    | .shift shift =>
        (if shift.compound then [Step.shift {shift with compound := false}] else []) ++
          (operands shift.value).map (fun value => Step.shift {shift with value}) ++
          (if shift.amount == Amount.literal 0 then [] else [Step.shift {shift with amount := .literal 0}])
  (if unchecked then [(false, step)] else []) ++ forms.map (unchecked, ·)

/-- An input other than the first removed, its references reading `sc_a0`
and later inputs renumbered. -/
def removeInput (plan : Plan) (index : Nat) : Plan :=
  let operand : Operand → Operand
    | .input other => if other = index then .input 0 else if other > index then .input (other - 1) else .input other
    | other => other
  Plan.withSteps {plan with inputs := plan.inputs.eraseIdx index}
    (plan.steps.map fun (unchecked, step) => (unchecked, step.map operand))

/-- An amount removed, its shifts by a zero literal. -/
def removeAmount (plan : Plan) (index : Nat) : Plan :=
  let amount : Amount → Amount
    | .input other => if other = index then .literal 0 else if other > index then .input (other - 1) else .input other
    | other => other
  let step : Step → Step
    | .shift shift => .shift {shift with amount := amount shift.amount}
    | other => other
  Plan.withSteps {plan with amounts := plan.amounts.eraseIdx index}
    (plan.steps.map fun (unchecked, s) => (unchecked, step s))

/-- Every reduction kind: remove a step; lower a step; remove an input or an
amount; a checked helper, `add` for a helper; `run(uint256)` and a `uint256`
result. -/
def reductions (plan : Plan) : List Plan :=
  let steps := plan.steps
  (List.range steps.length).map plan.removeStep ++
    (steps.zipIdx.flatMap fun ((unchecked, step), index) =>
      (plan.stepReductions unchecked step).map (plan.replaceStep index ·)) ++
    ((List.range plan.inputs.length).drop 1).map plan.removeInput ++
    (List.range plan.amounts.length).map plan.removeAmount ++
    (plan.helpers.zipIdx.flatMap fun (helper, index) =>
      (if helper.unchecked then [{plan with helpers := plan.helpers.set index {helper with unchecked := false}}] else []) ++
        (if helper.op == Op.add then [] else [{plan with helpers := plan.helpers.set index {helper with op := Op.add}}])) ++
    (if plan.abi then [{plan with abi := false}] else []) ++ (if plan.raw then [{plan with raw := false}] else [])

end Plan

end Solcore.Synthesis.Core.Integers
