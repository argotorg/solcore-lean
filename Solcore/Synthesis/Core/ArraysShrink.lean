import Solcore.Synthesis.Core.Arrays

/-! Plan size and reductions of the array plans. Every candidate is strictly
smaller in `Plan.size` and must still be admitted by its profile and pass the
full Core checker; that sealing is the cases module's. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.Arrays

open Solcore.Synthesis.Core.Integers (IntType Op)

/-! Weights: a literal 0 index, `sc_v0` and a literal 0 length weigh
nothing. -/

def Index.weight : Index → Nat
  | .literal value => value
  | .input index => 8 + index
  | .counter => 8

def Value.weight : Value → Nat
  | .input index => index
  | .literal index => 3 + index

def Length.weight : Length → Nat
  | .literal value => value
  | .input index => 5 + index

def Name.weight : Name → Nat
  | .var index | .param index => index

def Coll.weight : Coll → Nat
  | .array name => 1 + name.weight
  | .slice index => 2 + index
  | .storage => 2
  | .row grid index => 3 + grid + index.weight
  | .calldata index => 1 + index

def Target.weight : Target → Nat
  | .array name => 1 + name.weight
  | .storage => 2
  | .row grid index => 3 + grid + index.weight

def opWeight : Op → Nat
  | .add => 0
  | .sub => 1
  | .mul => 2
  | .div => 3
  | .mod => 4

def Form.weight : Form → Nat
  | .plain => 0
  | .put => 1
  | .compound op unchecked => 2 + opWeight op + (if unchecked then 1 else 0)
  | .inc => 2

def Cut.weight : Cut → Nat
  | .all => 0
  | .start first => 1 + first.weight
  | .stop last => 1 + last.weight
  | .range first last => 2 + first.weight + last.weight

def Observation.weight : Observation → Nat
  | .length coll => 1 + coll.weight
  | .element coll index => 2 + coll.weight + index.weight
  | .gridLength grid => 1 + grid
  | .sum name => 3 + name.weight
  | .get coll index => 3 + coll.weight + index.weight
  | .len coll => 2 + coll.weight

def Action.weight : Action → Nat
  | .write target index value form => 2 + target.weight + index.weight + value.weight + form.weight
  | .observe observation => 1 + observation.weight

def Step.weight : Step → Nat
  | .alloc length => 2 + length.weight
  | .literal values => 1 + (values.map (1 + ·.weight)).foldl (· + ·) 0
  | .alias source => 2 + source.weight
  | .copy number => 3 + number
  | .made left right => 4 + left.weight + right.weight
  | .slice base cut => 3 + base.weight + cut.weight
  | .tail source start => 5 + source.weight + start.weight
  | .grid length => 3 + length.weight
  | .gridOf sources => 3 + (sources.map (1 + ·.weight)).foldl (· + ·) 0
  | .gridLiteral rows => 4 + (rows.map fun row => 1 + (row.map (1 + ·.weight)).foldl (· + ·) 0).foldl (· + ·) 0
  | .setRow which index source => 3 + which + index.weight + source.weight
  | .act action => action.weight
  | .fill target value => 3 + target.weight + value.weight
  | .push value => 2 + value.weight
  | .pop => 2
  | .setLength length => 2 + length.weight
  | .loop over body => 4 + over.weight + (body.map (1 + ·.weight)).foldl (· + ·) 0

def ParamLength.weight : ParamLength → Nat
  | .literal value => value
  | .input .. => 5

namespace Plan

def offsetWeight (plan : Plan) (offset : Nat) : Nat := (plan.element.offsets.idxOf? offset).getD 0

def resultWeight : Result → Nat
  | .word => 0
  | .array name => 1 + name.weight
  | .copy slice => 2 + slice

/-- The plan size: every step's weight, each value, index and parameter, and
the result. -/
def size (plan : Plan) : Nat :=
  (plan.steps.map (·.weight)).foldl (· + ·) 0 +
    (plan.values.map fun value => 1 + plan.offsetWeight value.offset + (if value.raw then 1 else 0)).foldl (· + ·) 0 +
    (plan.indices.map fun index => 1 + (indexShifts.idxOf? index.shift).getD 0 + (indexMasks.idxOf? index.mask).getD 0 +
      (if index.flagged then 2 else 0)).foldl (· + ·) 0 +
    (plan.params.map fun param => 1 + (if param.calldata then 1 else 0) + param.length.weight +
      plan.offsetWeight param.offset + (if param.raw then 1 else 0)).foldl (· + ·) 0 +
    resultWeight plan.result

end Plan

/-! Removing a declaration renumbers the later names of its kind. -/

/-- What a step declares: an array, a slice or a grid. -/
inductive Declared where
  | array
  | slice
  | grid
  | none
  deriving BEq

def Step.declared : Step → Declared
  | .alloc _ | .literal _ | .alias _ | .copy _ | .made .. => .array
  | .slice .. | .tail .. => .slice
  | .grid _ | .gridOf _ | .gridLiteral _ => .grid
  | _ => .none

/-- The names a step reads. -/
structure Uses where
  arrays : List Nat := []
  slices : List Nat := []
  grids : List Nat := []

def Name.uses : Name → Uses
  | .var index => {arrays := [index]}
  | .param _ => {}

def Uses.join (left right : Uses) : Uses :=
  {arrays := left.arrays ++ right.arrays, slices := left.slices ++ right.slices, grids := left.grids ++ right.grids}

def Coll.uses : Coll → Uses
  | .array name => name.uses
  | .slice index => {slices := [index]}
  | .row grid _ => {grids := [grid]}
  | _ => {}

def Target.uses : Target → Uses
  | .array name => name.uses
  | .row grid _ => {grids := [grid]}
  | .storage => {}

def Observation.uses : Observation → Uses
  | .length coll | .element coll _ | .get coll _ | .len coll => coll.uses
  | .gridLength grid => {grids := [grid]}
  | .sum name => name.uses

def Action.uses : Action → Uses
  | .write target _ _ _ => target.uses
  | .observe observation => observation.uses

def Step.uses : Step → Uses
  | .alias source | .tail source _ | .fill source _ => source.uses
  | .copy number => {slices := [number]}
  | .slice base _ => base.uses
  | .gridOf sources => sources.foldl (fun uses source => uses.join source.uses) {}
  | .setRow which _ source => ({grids := [which]} : Uses).join source.uses
  | .act action => action.uses
  | .loop over body => body.foldl (fun uses action => uses.join action.uses) over.uses
  | _ => {}

/-- Renumber a name of each kind after the removed ones. -/
structure Renumber where
  arrays : List Nat
  slices : List Nat
  grids : List Nat

def Renumber.shift (removed : List Nat) (index : Nat) : Nat := index - (removed.filter (· < index)).length

namespace Renumber

def name (renumber : Renumber) : Name → Name
  | .var index => .var (shift renumber.arrays index)
  | other => other

def coll (renumber : Renumber) : Coll → Coll
  | .array name => .array (renumber.name name)
  | .slice index => .slice (shift renumber.slices index)
  | .row grid index => .row (shift renumber.grids grid) index
  | other => other

def target (renumber : Renumber) : Target → Target
  | .array name => .array (renumber.name name)
  | .row grid index => .row (shift renumber.grids grid) index
  | .storage => .storage

def observation (renumber : Renumber) : Observation → Observation
  | .length coll => .length (renumber.coll coll)
  | .element coll index => .element (renumber.coll coll) index
  | .gridLength grid => .gridLength (shift renumber.grids grid)
  | .sum name => .sum (renumber.name name)
  | .get coll index => .get (renumber.coll coll) index
  | .len coll => .len (renumber.coll coll)

def action (renumber : Renumber) : Action → Action
  | .write target index value form => .write (renumber.target target) index value form
  | .observe observation => .observe (renumber.observation observation)

def step (renumber : Renumber) : Step → Step
  | .alias source => .alias (renumber.name source)
  | .copy slice => .copy (shift renumber.slices slice)
  | .slice base cut => .slice (renumber.coll base) cut
  | .tail source start => .tail (renumber.name source) start
  | .gridOf sources => .gridOf (sources.map renumber.name)
  | .setRow grid index source => .setRow (shift renumber.grids grid) index (renumber.name source)
  | .act action => .act (renumber.action action)
  | .fill target value => .fill (renumber.name target) value
  | .loop over body => .loop (renumber.coll over) (body.map renumber.action)
  | other => other

end Renumber

namespace Plan

/-- The step at `index` removed with every later step that reads what a
removed step declared; the later names renumbered, and a result naming a
removed array or slice becomes the fold. -/
def removeStep (plan : Plan) (index : Nat) : Plan := Id.run do
  let mut arrays := 0
  let mut slices := 0
  let mut grids := 0
  let mut removed : Renumber := {arrays := [], slices := [], grids := []}
  let mut kept : List Step := []
  for (step, position) in plan.steps.zipIdx do
    let uses := step.uses
    let drop := position = index || uses.arrays.any removed.arrays.contains ||
      uses.slices.any removed.slices.contains || uses.grids.any removed.grids.contains
    match step.declared with
    | .array => if drop then removed := {removed with arrays := removed.arrays ++ [arrays]}
                arrays := arrays + 1
    | .slice => if drop then removed := {removed with slices := removed.slices ++ [slices]}
                slices := slices + 1
    | .grid => if drop then removed := {removed with grids := removed.grids ++ [grids]}
               grids := grids + 1
    | .none => pure ()
    if !drop then kept := kept ++ [removed.step step]
  let result := match plan.result with
    | .array (.var array) => if removed.arrays.contains array then .word else .array (.var (Renumber.shift removed.arrays array))
    | .copy slice => if removed.slices.contains slice then .word else .copy (Renumber.shift removed.slices slice)
    | other => other
  let values := if result == .word then plan.values.map ({· with raw := false}) else plan.values
  return {plan with steps := kept, result, values}

def replaceStep (plan : Plan) (index : Nat) (step : Step) : Plan := {plan with steps := plan.steps.set index step}

end Plan

/-! Lowered operands and forms. -/

def Index.lowered : Index → List Index
  | .literal 0 => []
  | _ => [.literal 0]

def Value.lowered : Value → List Value
  | .input 0 => []
  | _ => [.input 0]

def Length.lowered : Length → List Length
  | .literal 0 => []
  | _ => [.literal 0]

def Form.lowered : Form → List Form
  | .plain => []
  | .put | .inc => [.plain]
  | .compound op unchecked =>
      [.plain] ++ (if unchecked then [.compound op false] else []) ++ (if op == .add then [] else [.compound .add unchecked])

def Coll.lowered : Coll → List Coll
  | .row grid index => index.lowered.map (.row grid ·)
  | _ => []

def Target.lowered : Target → List Target
  | .row grid index => index.lowered.map (.row grid ·)
  | _ => []

def Observation.lowered : Observation → List Observation
  | .length coll => coll.lowered.map .length
  | .element coll index => [.length coll] ++ coll.lowered.map (.element · index) ++ index.lowered.map (.element coll ·)
  | .gridLength _ => []
  | .sum name => [.length (.array name)]
  | .get coll index => [.element coll index] ++ index.lowered.map (.get coll ·)
  | .len coll => [.length coll]

/-- The loop's counter read as the literal 0, for its body run once. -/
def Index.once : Index → Index
  | .counter => .literal 0
  | other => other

def Coll.once : Coll → Coll
  | .row grid index => .row grid index.once
  | other => other

def Target.once : Target → Target
  | .row grid index => .row grid index.once
  | other => other

def Observation.once : Observation → Observation
  | .length coll => .length coll.once
  | .element coll index => .element coll.once index.once
  | .get coll index => .get coll.once index.once
  | .len coll => .len coll.once
  | other => other

def Action.once : Action → Action
  | .write target index value form => .write target.once index.once value form
  | .observe observation => .observe observation.once

def Action.lowered : Action → List Action
  | .write target index value form =>
      (form.lowered.map (.write target index value ·)) ++ (target.lowered.map (.write · index value form)) ++
        (index.lowered.map (.write target · value form)) ++ (value.lowered.map (.write target index · form))
  | .observe observation => observation.lowered.map .observe

def Cut.lowered : Cut → List Cut
  | .all => []
  | .range first last => [.all] ++ first.lowered.map (.range · last) ++ last.lowered.map (.range first ·)
  | .start first => [.all] ++ first.lowered.map .start
  | .stop last => [.all] ++ last.lowered.map .stop

def dropLast {α : Type} (items : List α) : List (List α) := if items.length ≥ 2 then [items.dropLast] else []

/-- The simpler forms of one step. -/
def Step.lowered : Step → List Step
  | .alloc length => length.lowered.map .alloc
  | .literal values => (dropLast values).map .literal ++
      (List.range values.length).flatMap fun position =>
        ((values.getD position default).lowered.map fun value => .literal (values.set position value))
  | .made left right => [.literal [left, right]] ++ left.lowered.map (.made · right) ++ right.lowered.map (.made left ·)
  | .slice base cut => cut.lowered.map (.slice base ·) ++ base.lowered.map (.slice · cut)
  | .tail source start => [.slice (.array source) (.start start)] ++ start.lowered.map (.tail source ·)
  | .grid length => length.lowered.map .grid
  | .gridOf sources => [.grid (.literal 0)] ++ (dropLast sources).map .gridOf
  | .gridLiteral rows => [.grid (.literal 0)] ++ (dropLast rows).map .gridLiteral ++
      (List.range rows.length).flatMap fun position => (dropLast (rows.getD position [])).map fun row =>
        .gridLiteral (rows.set position row)
  | .setRow which index source => index.lowered.map (.setRow which · source)
  | .act action => action.lowered.map .act
  | .fill target value => value.lowered.map (.fill target ·)
  | .push value => value.lowered.map .push
  | .setLength length => length.lowered.map .setLength
  | .loop over body => (dropLast body).map (.loop over ·) ++
      (List.range body.length).flatMap fun position =>
        (body.getD position default).lowered.map fun action => .loop over (body.set position action)
  | _ => []

namespace Plan

/-- The loop at `index` replaced by its body run once, at counter 0. -/
def unrollLoop (plan : Plan) (index : Nat) : Option Plan :=
  match plan.steps[index]? with
  | some (.loop _ body) =>
      some {plan with steps := (plan.steps.take index) ++ body.map (Step.act ∘ Action.once) ++ plan.steps.drop (index + 1)}
  | _ => none

def stepReductions (plan : Plan) : List Plan :=
  (List.range plan.steps.length).flatMap fun index =>
    [plan.removeStep index] ++ (plan.unrollLoop index).toList ++
      ((plan.steps.getD index default).lowered.map (plan.replaceStep index ·))

/-- The last value or index input removed, its references reading `sc_v0`
or the literal 0; a flagged index masked; the second parameter removed with
the steps that read it; a parameter's length a literal 0 and its elements
clean; an array result the fold. -/
def inputReductions (plan : Plan) : List Plan :=
  let lastValue := plan.values.length - 1
  let valueRef : Value → Value
    | .input index => if index = lastValue then .input 0 else .input index
    | other => other
  let lastIndex := plan.indices.length - 1
  let indexRef : Index → Index
    | .input index => if index = lastIndex then .literal 0 else .input index
    | other => other
  let lengthRef : Length → Length
    | .input index => if index = lastIndex then .literal 0 else .input index
    | other => other
  let mapStep (index : Index → Index) (value : Value → Value) (length : Length → Length) : Step → Step :=
    let coll : Coll → Coll
      | .row grid row => .row grid (index row)
      | other => other
    let target : Target → Target
      | .row grid row => .row grid (index row)
      | other => other
    let observation : Observation → Observation
      | .length c => .length (coll c)
      | .element c i => .element (coll c) (index i)
      | .get c i => .get (coll c) (index i)
      | .len c => .len (coll c)
      | other => other
    let action : Action → Action
      | .write t i v f => .write (target t) (index i) (value v) f
      | .observe o => .observe (observation o)
    let cut : Cut → Cut
      | .range s e => .range (index s) (index e)
      | .start s => .start (index s)
      | .stop e => .stop (index e)
      | .all => .all
    fun
      | .alloc l => .alloc (length l)
      | .literal values => .literal (values.map value)
      | .made l r => .made (value l) (value r)
      | .slice base c => .slice (coll base) (cut c)
      | .tail source start => .tail source (index start)
      | .grid l => .grid (length l)
      | .gridLiteral rows => .gridLiteral (rows.map (·.map value))
      | .setRow grid i source => .setRow grid (index i) source
      | .act a => .act (action a)
      | .fill t v => .fill t (value v)
      | .push v => .push (value v)
      | .setLength l => .setLength (length l)
      | .loop over body => .loop (coll over) (body.map action)
      | other => other
  let removeValue := if plan.values.length ≥ 2 then
      [{plan with values := plan.values.dropLast, steps := plan.steps.map (mapStep id valueRef id)}] else []
  let removeIndex := if plan.indices.isEmpty then [] else
      [{plan with indices := plan.indices.dropLast, steps := plan.steps.map (mapStep indexRef id lengthRef)}]
  let unflag := (List.range plan.indices.length).filterMap fun position =>
    let input := plan.indices.getD position default
    if input.flagged then some {plan with indices := plan.indices.set position {input with flagged := false}} else none
  let clean := (List.range plan.values.length).filterMap fun position =>
    let input := plan.values.getD position default
    if input.raw then some {plan with values := plan.values.set position {input with raw := false}} else none
  let second := if plan.params.length = 2 then
      let uses (step : Step) : Bool := match step with
        | .slice (.calldata 1) _ | .slice (.array (.param 1)) _ | .loop (.calldata 1) _ | .loop (.array (.param 1)) _ => true
        | .alias (.param 1) | .tail (.param 1) _ | .fill (.param 1) _ | .setRow _ _ (.param 1) => true
        | .gridOf sources => sources.contains (.param 1)
        | _ => step.actions.any fun action => match action with
            | .write (.array (.param 1)) _ _ _ => true
            | .observe (.sum (.param 1)) => true
            | .observe observation => (observation.coll?.map fun coll => coll == .calldata 1 || coll == .array (.param 1)).getD false
            | _ => false
      let kept := {plan with params := plan.params.take 1, steps := plan.steps.filter (!uses ·)}
      [if plan.result == .array (.param 1) then {kept with result := .word, values := kept.values.map ({· with raw := false})}
        else kept]
    else []
  let params := (List.range plan.params.length).flatMap fun position =>
    let param := plan.params.getD position default
    (if param.length matches .literal 0 then [] else [{plan with params := plan.params.set position {param with length := .literal 0}}]) ++
      (if param.raw then [{plan with params := plan.params.set position {param with raw := false}}] else [])
  let result := if plan.result == .word then [] else [{plan with result := .word, values := plan.values.map ({· with raw := false})}]
  removeValue ++ removeIndex ++ unflag ++ clean ++ second ++ params ++ result

/-- Every reduction of the plan. -/
def reductions (plan : Plan) : List Plan := plan.stepReductions ++ plan.inputReductions

end Plan

end Solcore.Synthesis.Core.Arrays
