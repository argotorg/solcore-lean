import Solcore.Synthesis.Core.EnumMatch

/-! One trait with a unary and a binary method, its impls at Words, tuples,
std sums and the declarations of `EnumData`, and the plans of the
`runtime-traits` profile. The original Core reference has one closure per
instance type and method reachable from the uses, built bottom-up from the
impl at that instance. A std sum is lowered as a plain declaration of two
one-field constructors after the plan's, so every impl's `match` is compiled
by `EnumMatch`. Nothing here reads source text. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.Traits

open Solcore.Core (Word)
open Solcore.Core.Wire
open Solcore.Synthesis.Core.Enums (Decl LeafOp Form Gen Stream draw drawBits drawWeighted drawConstant typeLimit
  typeFuel valueFuel)

def traitVersion : String := "core-trait-instances-v1"

abbrev FieldTy := Solcore.Synthesis.Core.Enums.Ty
abbrev Op := Solcore.Synthesis.Core.Enums.Op
abbrev Pat := Solcore.Synthesis.Core.Enums.Pat

/-- Instance types: Words, tuples, std sums, plain declarations, and generic
declarations at an instance. -/
inductive Inst where
  | word
  | tuple (left right : Inst)
  | sum (left right : Inst)
  | enum (index : Nat)
  | applied (index : Nat) (argument : Inst)
  deriving Repr, BEq, DecidableEq, Inhabited

namespace Inst

def nodes : Inst → Nat
  | .word | .enum _ => 1
  | .tuple left right | .sum left right => 1 + left.nodes + right.nodes
  | .applied _ argument => 1 + argument.nodes

/-- A Word 0, a tuple or sum one more than its deepest component, a plain
declaration 1 and a generic one one more than its argument. -/
def depth : Inst → Nat
  | .word => 0
  | .enum _ => 1
  | .tuple left right | .sum left right => 1 + max left.depth right.depth
  | .applied _ argument => 1 + argument.depth

def kind : Inst → String
  | .word => "word"
  | .tuple _ _ => "tuple"
  | .sum _ _ => "sum"
  | .enum _ => "plain"
  | .applied _ _ => "generic"

/-- A declaration's field type at an instance argument. -/
def ofField (argument : Inst) : FieldTy → Inst
  | .word => .word
  | .param => argument
  | .tuple left right => .tuple (ofField argument left) (ofField argument right)
  | .enum index => .enum index
  | .applied index inner => .applied index (ofField argument inner)

/-- Every declaration reference names a declaration of its kind. -/
def valid (decls : List Decl) : Inst → Bool
  | .word => true
  | .tuple left right | .sum left right => valid decls left && valid decls right
  | .enum index => (decls[index]?.map (!·.generic)).getD false
  | .applied index argument => (decls[index]?.map (·.generic)).getD false && valid decls argument

end Inst

/-- The field types of an instance's constructors: a tuple is one
constructor of two fields, a sum two of one, a declaration its own at the
argument; none for a Word or an invalid reference. -/
def constructorsOf (decls : List Decl) : Inst → Option (List (List Inst))
  | .word => none
  | .tuple left right => some [[left, right]]
  | .sum left right => some [[left], [right]]
  | .enum index => match decls[index]? with
      | some decl => if decl.generic then none else some (decl.constructors.map (·.map (Inst.ofField .word)))
      | none => none
  | .applied index argument => match decls[index]? with
      | some decl => if decl.generic then some (decl.constructors.map (·.map (Inst.ofField argument))) else none
      | none => none

/-! Values. -/

inductive Val where
  | leaf (op : LeafOp) (constant : Nat)
  | tuple (left right : Val)
  | inl (value : Val)
  | inr (value : Val)
  | ctor0 (index : Nat) (form : Form)
  | ctor1 (index : Nat) (field : Val) (form : Form)
  | ctor2 (index : Nat) (first second : Val) (form : Form)
  deriving Repr, BEq, DecidableEq, Inhabited

namespace Val

def nodes : Val → Nat
  | .leaf _ _ | .ctor0 _ _ => 1
  | .tuple left right | .ctor2 _ left right _ => 1 + left.nodes + right.nodes
  | .inl value | .inr value | .ctor1 _ value _ => 1 + value.nodes

def constructor? : Val → Option (Nat × List Val × Form)
  | .ctor0 index form => some (index, [], form)
  | .ctor1 index field form => some (index, [field], form)
  | .ctor2 index first second form => some (index, [first, second], form)
  | _ => none

/-- The top constructor: a sum's side or a declaration's constructor. -/
def top : Val → Nat
  | .inr _ => 1
  | .ctor0 index _ | .ctor1 index _ _ | .ctor2 index _ _ _ => index
  | _ => 0

/-- The value as an `EnumData` value: `inl` and `inr` are the two
constructors of a lowered sum. -/
def lower : Val → Enums.Value
  | .leaf op constant => .leaf op constant
  | .tuple left right => .tuple left.lower right.lower
  | .inl value => .ctor1 0 value.lower .qualified
  | .inr value => .ctor1 1 value.lower .qualified
  | .ctor0 index form => .ctor0 index form
  | .ctor1 index field form => .ctor1 index field.lower form
  | .ctor2 index first second form => .ctor2 index first.lower second.lower form

end Val

private def declIndex : Inst → Option Nat
  | .enum index | .applied index _ => some index
  | _ => none

/-- `T.C` always, `.C` in a returned value, `T` for a same-name constructor. -/
def formAdmitted (decls : List Decl) (type : Inst) (index : Nat) (top : Bool) : Form → Bool
  | .qualified => true
  | .dot => top
  | .sameName => index = 0 && (((declIndex type).bind (decls[·]?)).map (·.sameName)).getD false

/-- Values are typed structurally; leaves are canonical, with no constant
for the input itself. -/
def valTyped (decls : List Decl) : Nat → Bool → Inst → Val → Bool
  | 0, _, _, _ => false
  | _ + 1, _, .word, .leaf op constant => constant < 2 ^ 256 && (op != .input || constant = 0)
  | fuel + 1, _, .tuple left right, .tuple first second =>
      valTyped decls fuel false left first && valTyped decls fuel false right second
  | fuel + 1, _, .sum left _, .inl value => valTyped decls fuel false left value
  | fuel + 1, _, .sum _ right, .inr value => valTyped decls fuel false right value
  | fuel + 1, top, type, value => match type, constructorsOf decls type, value.constructor? with
      | .enum _, some constructors, some (index, fields, form)
      | .applied _ _, some constructors, some (index, fields, form) => match constructors[index]? with
          | some types => types.length = fields.length && formAdmitted decls type index top form &&
              (types.zip fields).all fun (fieldType, field) => valTyped decls fuel false fieldType field
          | none => false
      | _, _, _ => false

/-- One to four values selected by the residue `(x + offset) & 3`, as in
`EnumData`. -/
structure Builder where
  offset : Nat
  trees : List Val
  deriving Repr, BEq, DecidableEq, Inhabited

def maximumTrees : Nat := 4

def Builder.admitted (decls : List Decl) (type : Inst) (builder : Builder) : Bool :=
  builder.offset < 4 && 0 < builder.trees.length && builder.trees.length ≤ maximumTrees &&
    builder.trees.all (valTyped decls valueFuel true type)

def Builder.lower (builder : Builder) : Enums.Builder := {offset := builder.offset, trees := builder.trees.map Val.lower}

/-! The trait, its impls and its uses. -/

inductive Method where
  | unary
  | binary
  deriving Repr, BEq, DecidableEq, Inhabited

def Method.name : Method → String
  | .unary => "unary"
  | .binary => "binary"

def Method.ofString? : String → Option Method
  | "unary" => some .unary
  | "binary" => some .binary
  | _ => none

/-- A direct call, a call through a constrained generic function at its
parameter, or through one at the tuple `(t, t)` of its parameter. -/
inductive Call where
  | direct
  | generic
  | lifted
  deriving Repr, BEq, DecidableEq, Inhabited

def Call.name : Call → String
  | .direct => "direct"
  | .generic => "generic"
  | .lifted => "lifted"

def Call.ofString? : String → Option Call
  | "direct" => some .direct
  | "generic" => some .generic
  | "lifted" => some .lifted
  | _ => none

/-- An arm's arithmetic: the operator folding its operands, then the
operator with its constant. An arm with one operand has no fold and one with
none returns its constant; unused operators are `add`. -/
structure Step where
  combine : Op
  op : Op
  constant : Nat
  deriving Repr, BEq, DecidableEq, Inhabited

def Step.admitted (operands : Nat) (step : Step) : Bool :=
  step.constant < 2 ^ 256 && (operands ≥ 2 || step.combine == .add) && (operands ≥ 1 || step.op == .add)

/-- A binary method matches its second argument inside each arm, or both
arguments as two columns. -/
inductive MatchForm where
  | nested
  | columns
  deriving Repr, BEq, DecidableEq, Inhabited

def MatchForm.name : MatchForm → String
  | .nested => "nested"
  | .columns => "columns"

def MatchForm.ofString? : String → Option MatchForm
  | "nested" => some .nested
  | "columns" => some .columns
  | _ => none

inductive Head where
  | word
  | tuple
  | sum
  | decl (index : Nat)
  deriving Repr, BEq, DecidableEq, Inhabited

def Head.rank : Head → Nat
  | .word => 0
  | .tuple => 1
  | .sum => 2
  | .decl index => 3 + index

/-- An impl: per method one step per constructor, the binary match form and
the binary mismatch constants (two for a sum, one for a declaration). -/
structure Impl where
  head : Head
  unary : List Step
  binary : List Step
  form : MatchForm
  mismatch : List Nat
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A constrained generic function: `generic` or `lifted`, for one method. -/
structure Helper where
  call : Call
  method : Method
  op : Op
  constant : Nat
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A call of one method at a closed instance type, on the builder's value of
the input and, for the binary method, of the input plus a shift. -/
structure Use where
  method : Method
  call : Call
  type : Inst
  shift : Nat
  builder : Builder
  deriving Repr, BEq, DecidableEq, Inhabited

structure Plan where
  decls : List Decl
  unary : Bool
  binary : Bool
  impls : List Impl
  helpers : List Helper
  uses : List Use
  deriving Repr, BEq, DecidableEq, Inhabited

def maximumUses : Nat := 6
def maximumDepth : Nat := 3

/-! Admission. -/

/-- Each arm's operands per method: a Word's own value or both values, two
components for a tuple, one side for a sum, a constructor's fields. -/
def operandCounts (decls : List Decl) (method : Method) : Head → Option (List Nat)
  | .word => some [if method == .unary then 1 else 2]
  | .tuple => some [2]
  | .sum => some [1, 1]
  | .decl index => decls[index]?.map (·.constructors.map List.length)

def mismatchCount : Head → Nat
  | .word | .tuple => 0
  | .sum => 2
  | .decl _ => 1

def stepsAdmitted (counts : List Nat) (steps : List Step) : Bool :=
  counts.length = steps.length && (counts.zip steps).all fun (operands, step) => step.admitted operands

def Impl.admitted (decls : List Decl) (unary binary : Bool) (impl : Impl) : Bool :=
  match operandCounts decls .unary impl.head, operandCounts decls .binary impl.head with
  | some unaryCounts, some binaryCounts =>
      (if unary then stepsAdmitted unaryCounts impl.unary else impl.unary.isEmpty) &&
      (if binary then stepsAdmitted binaryCounts impl.binary && impl.mismatch.length = mismatchCount impl.head &&
          impl.mismatch.all (· < 2 ^ 256) &&
          (impl.form == .nested || (match impl.head with
            | .tuple | .decl _ => true
            | _ => false))
       else impl.binary.isEmpty && impl.mismatch.isEmpty && impl.form == .nested)
  | _, _ => false

/-- The impls a declaration field's type resolves to; a parameter resolves
through the impl's constraint. -/
def fieldHeads : FieldTy → List Head
  | .word => [.word]
  | .param => []
  | .tuple left right => .tuple :: fieldHeads left ++ fieldHeads right
  | .enum index => [.decl index]
  | .applied index argument => .decl index :: fieldHeads argument

def instHeads : Inst → List Head
  | .word => [.word]
  | .tuple left right => .tuple :: instHeads left ++ instHeads right
  | .sum left right => .sum :: instHeads left ++ instHeads right
  | .enum index => [.decl index]
  | .applied index argument => .decl index :: instHeads argument

def Plan.present (plan : Plan) (head : Head) : Bool := plan.impls.any (·.head == head)

def Plan.implOf? (plan : Plan) (head : Head) : Option Impl := plan.impls.find? (·.head == head)

/-- The helpers the uses need, in the order generic unary, generic binary,
lifted unary, lifted binary. -/
def helperKeys : List (Call × Method) :=
  [(.generic, .unary), (.generic, .binary), (.lifted, .unary), (.lifted, .binary)]

def neededHelpers (uses : List Use) : List (Call × Method) :=
  helperKeys.filter fun (call, method) => uses.any fun use => use.call == call && use.method == method

/-! Std sums lowered as plain declarations after the plan's. -/

abbrev Sums := List (FieldTy × FieldTy)

def lowerM (base : Nat) : Inst → StateM Sums FieldTy
  | .word => pure .word
  | .tuple left right => do
      let left ← lowerM base left
      let right ← lowerM base right
      return .tuple left right
  | .sum left right => do
      let left ← lowerM base left
      let right ← lowerM base right
      let sums ← get
      match sums.idxOf? (left, right) with
      | some index => return .enum (base + index)
      | none =>
          set (sums ++ [(left, right)])
          return .enum (base + sums.length)
  | .enum index => pure (.enum index)
  | .applied index argument => do return .applied index (← lowerM base argument)

def sumDecl (sum : FieldTy × FieldTy) : Decl := {generic := false, sameName := false, constructors := [[sum.1], [sum.2]]}

/-- The use types lowered in order with one table of sums: the plan's
declarations then the sums', and each use's lowered type. -/
def Plan.lowered (plan : Plan) : List Decl × List FieldTy :=
  let (types, sums) := (plan.uses.mapM fun use => lowerM plan.decls.length use.type).run []
  (plan.decls ++ sums.map sumDecl, types)

/-- The type a use calls its method at: `(t, t)` through a lifted helper. -/
def rootType (use : Use) (type : FieldTy) : FieldTy :=
  if use.call == .lifted then .tuple type type else type

/-- A lowered type's Core type, with fuel exhaustion visible: one more level
of fuel changes an exhausted type, since no closed type's Core type is Unit. -/
def wireChecked (decls : List Decl) (type : FieldTy) : Option Enums.WireTy :=
  let wire := Enums.coreTy decls typeFuel type
  if wire == Enums.coreTy decls (typeFuel + 1) type then some wire else none

def typeAdmitted (decls : List Decl) (type : FieldTy) : Bool :=
  match wireChecked decls type with
  | some wire => Enums.wireTypeNodes wire ≤ typeLimit
  | none => false

def Use.admitted (plan : Plan) (decls : List Decl) (lowered : FieldTy) (use : Use) : Bool :=
  (if use.method == .unary then plan.unary && use.shift = 0 else plan.binary && 1 ≤ use.shift && use.shift ≤ 4) &&
    use.type.valid plan.decls && use.type.depth ≤ maximumDepth && use.builder.admitted plan.decls use.type &&
    (instHeads use.type).all plan.present && (use.call != .lifted || plan.present .tuple) &&
    typeAdmitted decls (rootType use lowered)

def Plan.admitted (plan : Plan) : Bool :=
  let (decls, types) := plan.lowered
  0 < plan.decls.length && plan.decls.length ≤ Enums.maximumDecls &&
    plan.decls.zipIdx.all (fun (decl, index) => decl.admitted plan.decls index) &&
    (plan.unary || plan.binary) &&
    plan.impls.all (Impl.admitted plan.decls plan.unary plan.binary) &&
    (plan.impls.zip plan.impls.tail).all (fun (first, second) => first.head.rank < second.head.rank) &&
    plan.impls.all (fun impl => match impl.head with
      | .decl index => match plan.decls[index]? with
          | some decl => decl.constructors.all (·.all fun field => (fieldHeads field).all plan.present)
          | none => false
      | _ => true) &&
    plan.helpers.map (fun helper => (helper.call, helper.method)) == neededHelpers plan.uses &&
    plan.helpers.all (·.constant < 2 ^ 256) &&
    0 < plan.uses.length && plan.uses.length ≤ maximumUses &&
    types.length = plan.uses.length &&
    (plan.uses.zip types).all fun (use, type) => use.admitted plan decls type

/-! The instances the uses reach. -/

private def dedup {α : Type} [BEq α] (values : List α) : List α :=
  values.foldl (fun kept value => if kept.contains value then kept else kept ++ [value]) []

/-- The instance types an impl's arms call the method at: tuple and sum
components, a declaration's fields at its instance. -/
def children (decls : List Decl) (type : FieldTy) : List FieldTy :=
  dedup ((Enums.constructorsOf decls type).getD []).flatten

def visit (decls : List Decl) : Nat → FieldTy × Method → List (FieldTy × Method) → List (FieldTy × Method)
  | 0, _, seen => seen
  | fuel + 1, (type, method), seen =>
      if seen.contains (type, method) then seen
      else (children decls type).foldl (fun seen child => visit decls fuel (child, method) seen) seen ++
        [(type, method)]

/-- Every instance and method reachable from the uses, components first, in
the order first reached. -/
def Plan.instances (plan : Plan) : List (FieldTy × Method) :=
  let (decls, types) := plan.lowered
  (plan.uses.zip types).foldl (fun seen (use, type) => visit decls (typeFuel + 1) (rootType use type, use.method) seen) []

/-- A lowered type's impl: sums follow the plan's declarations. -/
def headOf (base : Nat) : FieldTy → Option Head
  | .word => some .word
  | .tuple _ _ => some .tuple
  | .enum index => some (if index < base then .decl index else .sum)
  | .applied index _ => some (.decl index)
  | .param => none

/-! The Core reference. Variables are compiled from absolute levels: at depth
`d`, level `l` is de Bruijn index `d - 1 - l`. -/

private def word (value : Nat) : Expr := .word (Word.ofNatModulo value)

private def varAt (depth level : Nat) : Expr := .var (depth - 1 - level)

def stepExpr (step : Step) : List Expr → Expr
  | [] => word step.constant
  | first :: rest =>
      .binary step.op.binary (rest.foldl (fun folded operand => .binary step.combine.binary folded operand) first)
        (word step.constant)

/-- An arm's result: the method at its bound values' types, or a constant. -/
inductive Leaf where
  | unary (names : List Nat) (step : Step)
  | binary (pairs : List (Nat × Nat)) (step : Step)
  | constant (value : Nat)
  deriving Repr, BEq, Inhabited

def closureLevel (instances : List (FieldTy × Method)) (type : FieldTy) (method : Method) : Option Nat :=
  instances.idxOf? (type, method)

def leafExpr (instances : List (FieldTy × Method)) (depth : Nat) (scope : Enums.Scope) : Leaf → Expr
  | .unary names step => stepExpr step (names.map fun name => match Enums.lookupLevel scope name with
      | some (type, level) => match closureLevel instances type .unary with
          | some callee => .apply (varAt depth callee) (varAt depth level)
          | none => .unit
      | none => .unit)
  | .binary pairs step => stepExpr step (pairs.map fun (first, second) =>
      match Enums.lookupLevel scope first, Enums.lookupLevel scope second with
      | some (type, level), some (_, other) => match closureLevel instances type .binary with
          | some callee => .apply (.apply (varAt depth callee) (varAt depth level)) (varAt depth other)
          | none => .unit
      | _, _ => .unit)
  | .constant value => word value

/-- The pattern of a constructor binding its fields to two names in order. -/
def ctorPat (head : Head) (ctor fields first : Nat) : Pat :=
  match head, fields with
  | .tuple, _ => .tuple (.var first) (.var (first + 1))
  | _, 0 => .ctor0 ctor .qualified
  | _, 1 => .ctor1 ctor (.var first) .qualified
  | _, _ => .ctor2 ctor (.var first) (.var (first + 1)) .qualified

def fieldNames (fields first : Nat) : List Nat := (List.range fields).map (first + ·)

def fieldPairs (fields : Nat) : List (Nat × Nat) := (List.range fields).map fun index => (index, index + 2)

/-- An arm of an outer match: a result, or a match of the second argument. -/
abbrev Outer := Leaf ⊕ List (List Pat × Leaf)

/-- The unary match: one arm per constructor. -/
def unaryRows (head : Head) (counts : List Nat) (steps : List Step) : List (List Pat × Leaf) :=
  (counts.zip steps).zipIdx.map fun ((fields, step), ctor) =>
    ([ctorPat head ctor fields 0], .unary (fieldNames fields 0) step)

/-- The binary match of a sum: each side matches the second argument, its own
side recursing and the other returning a mismatch constant. -/
def sumRows (steps : List Step) (mismatch : List Nat) : List (List Pat × Outer) :=
  [([.ctor1 0 (.var 0) .qualified], .inr [
      ([.ctor1 0 (.var 2) .qualified], .binary [(0, 2)] (steps.getD 0 default)),
      ([.ctor1 1 .wild .qualified], .constant (mismatch.getD 0 0))]),
   ([.ctor1 1 (.var 0) .qualified], .inr [
      ([.ctor1 0 .wild .qualified], .constant (mismatch.getD 1 0)),
      ([.ctor1 1 (.var 2) .qualified], .binary [(0, 2)] (steps.getD 1 default))])]

/-- The nested binary match of a tuple or declaration: the same constructor
recurses on each pair of fields, any other returns the mismatch constant. -/
def nestedRows (head : Head) (counts : List Nat) (steps : List Step) (mismatch : List Nat) :
    List (List Pat × Outer) :=
  (counts.zip steps).zipIdx.map fun ((fields, step), ctor) =>
    let same : List Pat × Leaf := ([ctorPat head ctor fields 2], .binary (fieldPairs fields) step)
    ([ctorPat head ctor fields 0], .inr (match head with
      | .tuple => [same]
      | _ => [same, ([], .constant (mismatch.getD 0 0))]))

/-- The two-column binary match: a row per constructor, then `default` for a
declaration. -/
def columnRows (head : Head) (counts : List Nat) (steps : List Step) (mismatch : List Nat) :
    List (List Pat × Leaf) :=
  (counts.zip steps).zipIdx.map (fun ((fields, step), ctor) =>
    ([ctorPat head ctor fields 0, ctorPat head ctor fields 2], .binary (fieldPairs fields) step)) ++
    (match head with
      | .tuple => []
      | _ => [([], .constant (mismatch.getD 0 0))])

/-- The closure of an instance's method at `level`: its parameters follow the
earlier closures. -/
def instanceExpr (plan : Plan) (decls : List Decl) (instances : List (FieldTy × Method)) (level : Nat)
    (type : FieldTy) (method : Method) : Expr :=
  let wire := Enums.wireTy decls type
  let leaf := leafExpr instances
  match headOf plan.decls.length type with
  | none => .unit
  | some head => match plan.implOf? head, operandCounts plan.decls method head with
    | some impl, some counts => match method with
      | .unary =>
          let body := match head with
            | .word => stepExpr (impl.unary.headD default) [varAt (level + 1) level]
            | _ => Enums.armsExpr decls leaf [] [(type, level)] (level + 1) (unaryRows head counts impl.unary)
          .lambda wire .word body
      | .binary =>
          let depth := level + 2
          let outer := fun (depth : Nat) (scope : Enums.Scope) (body : Outer) => match body with
            | .inl result => leaf depth scope result
            | .inr rows => Enums.armsExpr decls leaf scope [(type, level + 1)] depth rows
          let body := match head, impl.form with
            | .word, _ => stepExpr (impl.binary.headD default) [varAt depth level, varAt depth (level + 1)]
            | .sum, _ => Enums.armsExpr decls outer [] [(type, level)] depth (sumRows impl.binary impl.mismatch)
            | _, .nested => Enums.armsExpr decls outer [] [(type, level)] depth
                (nestedRows head counts impl.binary impl.mismatch)
            | _, .columns => Enums.armsExpr decls leaf [] [(type, level), (type, level + 1)] depth
                (columnRows head counts impl.binary impl.mismatch)
          .lambda wire (.function wire .word) (.lambda wire .word body)
    | _, _ => .unit

/-- A helper's closure at one instance: the method at the parameter, or at
`(x, x)` and `((x, y), (y, x))` when lifted. -/
def helperExpr (decls : List Decl) (instances : List (FieldTy × Method)) (level : Nat) (helper : Helper)
    (type : FieldTy) : Expr :=
  let wire := Enums.wireTy decls type
  let step : Step := {combine := .add, op := helper.op, constant := helper.constant}
  let target := if helper.call == .lifted then Enums.Ty.tuple type type else type
  let callee := (closureLevel instances target helper.method).getD 0
  match helper.method with
  | .unary =>
      let depth := level + 1
      let argument := if helper.call == .lifted then Expr.pair (varAt depth level) (varAt depth level)
        else varAt depth level
      .lambda wire .word (stepExpr step [.apply (varAt depth callee) argument])
  | .binary =>
      let depth := level + 2
      let (first, second) := if helper.call == .lifted then
          (Expr.pair (varAt depth level) (varAt depth (level + 1)), Expr.pair (varAt depth (level + 1)) (varAt depth level))
        else (varAt depth level, varAt depth (level + 1))
      .lambda wire (.function wire .word) (.lambda wire .word
        (stepExpr step [.apply (.apply (varAt depth callee) first) second]))

/-- The helper closures the uses call, by helper and instance, first use first. -/
def Plan.helperInstances (plan : Plan) : List (Helper × FieldTy) :=
  let (_, types) := plan.lowered
  dedup ((plan.uses.zip types).filterMap fun (use, type) =>
    (plan.helpers.find? fun helper => helper.call == use.call && helper.method == use.method).map (·, type))

/-- The program: instance closures, helper closures and builders let-bound in
order, then the entry over the input, binding each use's Word in order and
combining them as `r_0 + 3 r_1 + 5 r_2 + …`. -/
def Plan.expression (plan : Plan) : Expr :=
  let (decls, types) := plan.lowered
  let instances := plan.instances
  let helpers := plan.helperInstances
  let instanceClosures := instances.zipIdx.map fun ((type, method), level) =>
    instanceExpr plan decls instances level type method
  let helperClosures := helpers.zipIdx.map fun ((helper, type), index) =>
    helperExpr decls instances (instances.length + index) helper type
  let builderBase := instances.length + helpers.length
  let builderClosures := (plan.uses.zip types).map fun (use, type) => Enums.builderExpr decls type use.builder.lower
  let input := builderBase + plan.uses.length
  let callExpr := fun (depth : Nat) (((use, type), index) : (Use × FieldTy) × Nat) =>
    let callee := match plan.helpers.find? (fun helper => helper.call == use.call && helper.method == use.method) with
      | some helper => instances.length + (helpers.idxOf? (helper, type)).getD 0
      | none => (closureLevel instances type use.method).getD 0
    let builder := builderBase + index
    let first := Expr.apply (varAt depth builder) (varAt depth input)
    match use.method with
    | .unary => Expr.apply (varAt depth callee) first
    | .binary => Expr.apply (.apply (varAt depth callee) first)
        (.apply (varAt depth builder) (.binary .wordAdd (varAt depth input) (word use.shift)))
  let entry := (plan.uses.zip types).zipIdx.foldr
    (fun call inner => fun depth => Expr.letE (callExpr depth call) (inner (depth + 1)))
    (fun depth => Enums.combine depth (input + 1) plan.uses.length)
  (instanceClosures ++ helperClosures ++ builderClosures).foldr (fun closure inner => .letE closure inner)
    (.lambda .word .word (entry (input + 1)))

def Plan.program (plan : Plan) : Program := {
  resultType := .function .word .word, dataDefinitions := [], body := plan.expression}

def Plan.applied (plan : Plan) (input : Word) : Program := {
  resultType := .word, dataDefinitions := [], body := .apply plan.expression (.word input)}

def Plan.nodes (plan : Plan) : Nat := programNodes (plan.applied Word.zero)

/-! Specified shapes, from the plan. -/

def loweredKind (base : Nat) : FieldTy → String
  | .word => "word"
  | .tuple _ _ => "tuple"
  | .enum index => if index < base then "plain" else "sum"
  | .applied _ _ => "generic"
  | .param => "param"

def Plan.shapes (plan : Plan) : List (String × List String) :=
  let (decls, _) := plan.lowered
  let base := plan.decls.length
  let instances := plan.instances
  let binaryForm := fun (head : Head) (label : String) =>
    (plan.implOf? head).map fun impl => label ++ ":" ++ impl.form.name
  let sorted := fun (values : List String) => values.eraseDups.mergeSort (· ≤ ·)
  let sumOfProduct := instances.any fun (type, method) => method == .binary && (match type with
    | .enum index => base ≤ index && (match Enums.constructorsOf decls type with
        | some [[left], [right]] => (match left, right with
            | .tuple _ _, .tuple _ _ => false
            | .tuple _ _, _ | _, .tuple _ _ => true
            | _, _ => false)
        | _ => false)
    | _ => false)
  [("instances", sorted (instances.map fun (type, method) => loweredKind base type ++ ":" ++ method.name)),
   ("calls", sorted (plan.uses.map fun use => use.method.name ++ ":" ++ use.call.name)),
   ("depths", sorted (plan.uses.map fun use => toString use.type.depth)),
   ("arguments", sorted (instances.filterMap fun (type, _) => match type with
      | .applied _ argument => some (loweredKind base argument)
      | _ => none)),
   ("forms", sorted (instances.filterMap fun (type, method) =>
      if method != .binary then none
      else match headOf base type with
        | some .tuple => binaryForm .tuple "tuple"
        | some (.decl index) => binaryForm (.decl index) "enum"
        | _ => none)),
   ("shapes", if sumOfProduct then ["sum-of-product"] else [])]

/-! Generation: a SplitMix64 stream with this profile's domain. -/

def domain : UInt64 := 0x7472616974730001

def drawOp : Gen Op := return Enums.opOf (← draw 4)

def drawStep (operands : Nat) : Gen Step := do
  let combine ← if operands ≥ 2 then drawOp else pure .add
  let op ← if operands ≥ 1 then drawOp else pure .add
  return {combine, op, constant := ← drawConstant}

def drawImpl (decls : List Decl) (head : Head) : Gen Impl := do
  let unary ← ((operandCounts decls .unary head).getD []).mapM drawStep
  let binary ← ((operandCounts decls .binary head).getD []).mapM drawStep
  let form ← match head with
    | .tuple | .decl _ => do
        let bit ← draw 2
        pure (if bit = 0 then MatchForm.nested else .columns)
    | _ => pure .nested
  let mut mismatch : List Nat := []
  for _ in List.range (mismatchCount head) do
    mismatch := mismatch ++ [← drawConstant]
  return {head, unary, binary, form, mismatch}

/-- An instance type of exactly this depth; fuel bounds the depth. -/
def drawExact (decls : List Decl) : Nat → Nat → Gen Inst
  | 0, _ | _ + 1, 0 => return .word
  | fuel + 1, depth + 1 => do
      let plain := (List.range decls.length).filter fun index => (decls[index]?.map (!·.generic)).getD false
      let generic := (List.range decls.length).filter fun index => (decls[index]?.map (·.generic)).getD false
      match ← drawWeighted [2, 2, if depth = 0 && !plain.isEmpty then 2 else 0, if generic.isEmpty then 0 else 3] with
      | 0 | 1 =>
          let deep ← drawExact decls fuel depth
          let other ← drawExact decls fuel (← draw (depth + 1))
          let (left, right) := if (← draw 2) = 0 then (deep, other) else (other, deep)
          return if (← draw 2) = 0 then .tuple left right else .sum left right
      | 2 => return .enum (plain.getD (← draw plain.length) 0)
      | _ =>
          let index := generic.getD (← draw generic.length) 0
          return .applied index (← drawExact decls fuel depth)

/-- A random leaf, drawn as `EnumData` draws it. -/
def drawLeafVal : Gen Val := do
  match ← Enums.drawLeaf with
  | .leaf op constant => return .leaf op constant
  | _ => return .leaf .input 0

/-- A random value of a closed type; `top` admits the dot form. -/
def drawVal (decls : List Decl) : Nat → Bool → Inst → Gen Val
  | 0, _, _ => return .leaf .input 0
  | _ + 1, _, .word => drawLeafVal
  | fuel + 1, _, .tuple left right =>
      return .tuple (← drawVal decls fuel false left) (← drawVal decls fuel false right)
  | fuel + 1, _, .sum left right => do
      if (← draw 2) = 0 then return .inl (← drawVal decls fuel false left)
      else return .inr (← drawVal decls fuel false right)
  | fuel + 1, top, type => do
      match constructorsOf decls type with
      | some constructors =>
          let index ← draw constructors.length
          let sameName := formAdmitted decls type index top .sameName
          let form := match ← drawWeighted [3, if top then 1 else 0, if sameName then 2 else 0] with
            | 0 => Form.qualified
            | 1 => .dot
            | _ => .sameName
          match constructors.getD index [] with
          | [] => return .ctor0 index form
          | [field] => return .ctor1 index (← drawVal decls fuel false field) form
          | [first, second] =>
              return .ctor2 index (← drawVal decls fuel false first) (← drawVal decls fuel false second) form
          | _ => return .ctor0 index form
      | none => return .leaf .input 0

/-- Each value is the first of four candidates whose top constructor no
earlier value has, or the first candidate. -/
def drawBuilder (decls : List Decl) (type : Inst) : Gen Builder := do
  let offset ← draw 4
  let count := 1 + (← draw maximumTrees)
  let mut trees : List Val := []
  for _ in List.range count do
    let mut first : Option Val := none
    let mut chosen : Option Val := none
    for _ in List.range 4 do
      let candidate ← drawVal decls valueFuel true type
      if first.isNone then first := some candidate
      if chosen.isNone && !(trees.any (·.top == candidate.top)) then chosen := some candidate
    trees := trees ++ [(chosen.orElse fun _ => first).getD (.leaf .input 0)]
  return {offset, trees}

/-- A use type is the first of four candidates of the drawn depth whose
called type fits the type limit, or a Word. -/
def drawUse (decls : List Decl) : Gen Use := do
  let method := if (← draw 2) = 0 then Method.unary else .binary
  let call := match ← drawWeighted [2, 1, 1] with
    | 0 => Call.direct
    | 1 => .generic
    | _ => .lifted
  let depth ← drawWeighted [1, 3, 3, 3]
  let mut found : Option Inst := none
  for _ in List.range 4 do
    let candidate ← drawExact decls (maximumDepth + 1) depth
    let (lowered, sums) := (lowerM decls.length candidate).run []
    let root := if call == .lifted then Enums.Ty.tuple lowered lowered else lowered
    if found.isNone && typeAdmitted (decls ++ sums.map sumDecl) root then found := some candidate
  let type := found.getD .word
  let shift ← if method == .binary then (do let bits ← draw 4; pure (1 + bits)) else pure 0
  return {method, call, type, shift, builder := ← drawBuilder decls type}

def heads (decls : List Decl) : List Head := [.word, .tuple, .sum] ++ (List.range decls.length).map .decl

/-- Draws in plan order: declarations, impls, helpers, then the uses. -/
def drawPlan : Gen Plan := do
  let decls ← Enums.drawDecls
  let impls ← (heads decls).mapM (drawImpl decls)
  let mut helpers : List Helper := []
  for (call, method) in helperKeys do
    helpers := helpers ++ [{call, method, op := ← drawOp, constant := ← drawConstant}]
  let count := 1 + (← draw maximumUses)
  let mut uses : List Use := []
  for _ in List.range count do
    uses := uses ++ [← drawUse decls]
  let needed := neededHelpers uses
  return {decls, unary := true, binary := true, impls,
          helpers := helpers.filter fun helper => needed.contains (helper.call, helper.method), uses}

def generate (seed : UInt64) : Plan :=
  (drawPlan.run {seed, domain, index := 0}).1

/-- Uses are dropped from the end while the reference exceeds the budget and
more than one remains; helpers no use needs go with them. -/
def Plan.fit (nodes : Nat) (plan : Plan) : Plan := Id.run do
  let mut plan := plan
  for _ in List.range plan.uses.length do
    if plan.nodes > nodes && plan.uses.length > 1 then
      let uses := plan.uses.dropLast
      let needed := neededHelpers uses
      plan := {plan with uses, helpers := plan.helpers.filter fun helper => needed.contains (helper.call, helper.method)}
  return plan

end Solcore.Synthesis.Core.Traits
