import Solcore.Synthesis.Core.MemoryValues

/-! Reductions of memory value plans. A candidate is kept only when the plan
is admitted and strictly smaller: in its structure first, then in the sum of
its numeric literals. Removing a declaration renumbers the later variables of
its kind; a candidate that would still refer to it is not formed. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.MemoryValues

def Operand.size : Operand → Nat × Nat
  | .input => (1, 0)
  | .add constant | .mul constant | .xor constant => (2, constant)
  | .acc | .counter => (2, 0)

def Index.size : Index → Nat × Nat
  | .literal value => (1, value)
  | .input shift modulus => (2, shift + modulus)
  | .counter scale offset => (2, scale + offset)

private def plus (left right : Nat × Nat) : Nat × Nat := (left.1 + right.1, left.2 + right.2)

private def sumOf {α : Type} (size : α → Nat × Nat) (values : List α) : Nat × Nat :=
  values.foldl (fun total value => plus total (size value)) (0, 0)

def Part.size : Part → Nat × Nat
  | .word operand => plus (1, 0) operand.size
  | .zeros count => (1, count)
  | .value _ => (1, 0)

def Build.size : Build → Nat × Nat
  | .toBytes part => plus (1, 0) part.size
  | .concat left right => plus (2, 0) (plus left.size right.size)

def Cut.size : Cut → Nat × Nat
  | .drop start => (1, start)
  | .take kept => (1, kept)
  | .window start kept => (2, start + kept)

def Access.size : Access → Nat × Nat
  | .length => (1, 0)
  | .word index | .byte index => plus (2, 0) index.size
  | .hash => (2, 0)
  | .element index get => plus (if get then 3 else 2, 0) index.size

def Action.size : Action → Nat × Nat
  | .bytes build => plus (1, 0) build.size
  | .slice _ cut => plus (1, 0) cut.size
  | .alias _ => (1, 0)
  | .array allocated elements => plus (if allocated then 2 else 1, 0) (sumOf Operand.size elements)
  | .write _ index value _ form => plus (if form == .helper then 2 else 1, 0) (plus index.size value.size)
  | .observe fold constant _ access => plus (if fold == .xor then 2 else 1, constant) access.size

def Loop.size : Loop → Nat × Nat
  | .single mask => (1, mask)
  | .nested outer _ inner => (3, outer + inner)

def Step.size : Step → Nat × Nat
  | .action single => plus (1, 0) single.size
  | .loop shape body => plus (1, 0) (plus shape.size (sumOf (fun single => plus (1, 0) single.size) body))

/-- Structure first, then literals; literals stay far below `2 ^ 16`. -/
def Plan.size (plan : Plan) : Nat :=
  let (shape, literals) := sumOf Step.size plan.steps
  shape * 2 ^ 16 + literals

/-! Renumbering after a removed declaration. -/

/-- The declarations an action makes, by kind. -/
def Action.declares (scope : Scope) : Action → Option String
  | .bytes _ => some "bytes"
  | .slice .. => some "slice"
  | .alias source => if source.isArray then some "array" else some "bytes"
  | .array .. => some "array"
  | _ => let _ := scope; none

/-- Map a variable after the declarations `[first, first + count)` of a kind
are removed; `none` when it is one of them. -/
def Ref.renumber (kind : String) (first count : Nat) (ref : Ref) : Option Ref :=
  if ref.kind != kind || ref.number < first then some ref
  else if ref.number < first + count then none
  else some (match ref with
    | .bytes number => .bytes (number - count)
    | .slice number => .slice (number - count)
    | .array number => .array (number - count))

def Part.renumber (kind : String) (first count : Nat) : Part → Option Part
  | .value ref => (ref.renumber kind first count).map .value
  | part => some part

def Action.renumber (kind : String) (first count : Nat) : Action → Option Action
  | .bytes (.toBytes part) => do return .bytes (.toBytes (← part.renumber kind first count))
  | .bytes (.concat left right) => do
      return .bytes (.concat (← left.renumber kind first count) (← right.renumber kind first count))
  | .slice source cut => do return .slice (← source.renumber kind first count) cut
  | .alias source => do return .alias (← source.renumber kind first count)
  | .write target index value width form => do
      return .write (← target.renumber kind first count) index value width form
  | .observe fold constant value access => do
      return .observe fold constant (← value.renumber kind first count) access
  | action => some action

def Step.renumber (kind : String) (first count : Nat) : Step → Option Step
  | .action single => (single.renumber kind first count).map .action
  | .loop shape body => do return .loop shape (← body.mapM (·.renumber kind first count))

/-- How many declarations of each kind the actions make. -/
def declarationCounts (actions : List Action) : List (String × Nat) :=
  ["bytes", "slice", "array"].map fun kind =>
    (kind, (actions.filter fun action => action.declares {} == some kind).length)

def Plan.declarationsBefore (plan : Plan) (index : Nat) : List (String × Nat) :=
  declarationCounts ((plan.steps.take index).flatMap (·.actions))

/-- Remove the actions `removed` from the plan at step `index`, renumbering
every later step, `rest` being the steps after them. -/
private def renumberRest (before : List (String × Nat)) (removed : List Action) (rest : List Step) : Option (List Step) :=
  (declarationCounts removed).foldlM (fun steps (kind, count) =>
    if count = 0 then some steps
    else steps.mapM (·.renumber kind ((before.lookup kind).getD 0) count)) rest

def Plan.removeStep (plan : Plan) (index : Nat) : Option Plan := do
  let step ← plan.steps[index]?
  let rest ← renumberRest (plan.declarationsBefore index) step.actions (plan.steps.drop (index + 1))
  return {steps := plan.steps.take index ++ rest}

/-- Remove action `position` of the loop at step `index`. -/
def Plan.removeBodyAction (plan : Plan) (index position : Nat) : Option Plan := do
  let .loop shape body ← plan.steps[index]? | none
  let action ← body[position]?
  let before := declarationCounts ((plan.steps.take index).flatMap (·.actions) ++ body.take position)
  let following ← renumberRest before [action] ((body.drop (position + 1)).map Step.action)
  let later ← renumberRest before [action] (plan.steps.drop (index + 1))
  let kept := body.take position ++ following.filterMap fun step => match step with
    | .action single => some single
    | .loop .. => none
  return {steps := plan.steps.take index ++ [.loop shape kept] ++ later}

/-! Local reductions of operands, indices, builds, cuts, arrays,
observations, writes and loops. -/

def Operand.reductions : Operand → List Operand
  | .input => []
  | _ => [.input]

def Index.reductions : Index → List Index
  | .literal 0 => []
  | _ => [.literal 0]

def Part.reductions : Part → List Part
  | .word operand => operand.reductions.map .word
  | .zeros count => if count = 0 then [] else [.zeros 0]
  | .value _ => []

def Build.reductions : Build → List Build
  | .toBytes part => part.reductions.map .toBytes
  | .concat left right =>
      [.toBytes left, .toBytes right] ++ left.reductions.map (.concat · right) ++
        right.reductions.map (.concat left ·)

def Cut.reductions : Cut → List Cut
  | .drop start => if start = 0 then [] else [.drop 0]
  | .take kept => if kept = 0 then [] else [.take 0]
  | .window start kept => [.drop start, .take kept]

def Access.reductions : Access → List Access
  | .length => []
  | .word index => .length :: index.reductions.map .word
  | .byte index => .length :: index.reductions.map .byte
  | .hash => [.length]
  | .element index get => (if get then [.element index false] else []) ++ index.reductions.map (.element · get)

private def replaceAt {α : Type} (values : List α) (index : Nat) (value : α) : List α :=
  values.set index value

def Action.reductions : Action → List Action
  | .bytes build => build.reductions.map .bytes
  | .slice source cut => cut.reductions.map (.slice source ·)
  | .alias _ => []
  | .array allocated elements =>
      (if allocated then [.array false elements] else []) ++
      (if elements.length > 1 then [.array allocated elements.dropLast] else []) ++
      elements.zipIdx.flatMap fun (element, index) =>
        element.reductions.map fun reduced => .array allocated (replaceAt elements index reduced)
  | .write target index value width form =>
      (if form == .helper then [.write target index value width .inline] else []) ++
      index.reductions.map (fun reduced => .write target reduced value width form) ++
      value.reductions.map (fun reduced => .write target index reduced width form)
  | .observe fold constant value access =>
      (if fold == .xor then [.observe .add constant value access] else []) ++
      (if constant > 3 then [.observe fold 3 value access] else []) ++
      access.reductions.map (.observe fold constant value ·)

def Loop.reductions : Loop → List Loop
  | .single 7 => [.single 3]
  | .single 3 => [.single 1]
  | .single _ => []
  | .nested outer bound inner =>
      [.single 1] ++ (if outer = 3 then [.nested 1 bound inner] else []) ++
        (if inner = 3 then [.nested outer bound 1] else []) ++
        (if bound == .counter then [.nested outer .input inner] else [])

def planReductions (plan : Plan) : List Plan := Id.run do
  let mut result : List Plan := []
  for index in List.range plan.steps.length do
    if let some reduced := plan.removeStep index then result := result ++ [reduced]
  for (step, index) in plan.steps.zipIdx do
    let replace := fun (step : Step) => ({steps := replaceAt plan.steps index step} : Plan)
    match step with
    | .action action =>
        result := result ++ action.reductions.map fun reduced => replace (.action reduced)
    | .loop shape body =>
        for position in List.range body.length do
          if body.length > 1 then
            if let some reduced := plan.removeBodyAction index position then result := result ++ [reduced]
        result := result ++ shape.reductions.map fun reduced => replace (.loop reduced body)
        for (action, position) in body.zipIdx do
          result := result ++ action.reductions.map fun reduced =>
            replace (.loop shape (replaceAt body position reduced))
  return result.filter fun candidate => candidate.admitted && candidate.size < plan.size

end Solcore.Synthesis.Core.MemoryValues
