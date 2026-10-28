import Solcore.Synthesis.Core.EnumData

/-! Views that `match` enum values, and the plans of the `runtime-enums`
profile. The original Core reference compiles each match itself: a
constructor pattern unwraps the sum chain with nested `caseE`, a tuple pattern
projects, a variable names the matched value, and an arm that fails calls the
let-bound thunk of the remaining arms. Arms are checked useful and matches
exhaustive by the pattern-matrix algorithm, with no reference to the source
or its compiler. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.Enums

open Solcore.Core (Word)
open Solcore.Core.Wire

def matchVersion : String := "core-enum-match-v1"

/-- Pattern variables are `sc_a` to `sc_d`, or `sc_w`, which shadows the
view's Word parameter. -/
def names : List String := ["sc_a", "sc_b", "sc_c", "sc_d", "sc_w"]
def parameterName : Nat := 4

inductive Pat where
  | wild
  | var (name : Nat)
  | tuple (left right : Pat)
  | ctor0 (index : Nat) (form : Form)
  | ctor1 (index : Nat) (field : Pat) (form : Form)
  | ctor2 (index : Nat) (first second : Pat) (form : Form)
  deriving Repr, BEq, DecidableEq, Inhabited

namespace Pat

/-- A constructor or tuple pattern's constructor and subpatterns. -/
def head : Pat → Option (Nat × List Pat)
  | .tuple left right => some (0, [left, right])
  | .ctor0 index _ => some (index, [])
  | .ctor1 index field _ => some (index, [field])
  | .ctor2 index first second _ => some (index, [first, second])
  | .wild | .var _ => none

def nodes : Pat → Nat
  | .wild | .var _ | .ctor0 _ _ => 1
  | .tuple left right | .ctor2 _ left right _ => 1 + left.nodes + right.nodes
  | .ctor1 _ field _ => 1 + field.nodes

/-- Nesting depth of constructor and tuple patterns. -/
def depth : Pat → Nat
  | .wild | .var _ => 0
  | .ctor0 _ _ => 1
  | .tuple left right | .ctor2 _ left right _ => 1 + max left.depth right.depth
  | .ctor1 _ field _ => 1 + field.depth

def variables : Pat → List Nat
  | .wild | .ctor0 _ _ => []
  | .var name => [name]
  | .tuple left right | .ctor2 _ left right _ => left.variables ++ right.variables
  | .ctor1 _ field _ => field.variables

/-- Matching a value's constructors; variables and wildcards match anything. -/
def accepts : Pat → Value → Bool
  | .wild, _ | .var _, _ => true
  | .tuple left right, .tuple first second => left.accepts first && right.accepts second
  | .ctor0 index _, .ctor0 other _ => index = other
  | .ctor1 index field _, .ctor1 other value _ => index = other && field.accepts value
  | .ctor2 index left right _, .ctor2 other first second _ =>
      index = other && left.accepts first && right.accepts second
  | _, _ => false

end Pat

def Pat.form? : Pat → Option Form
  | .ctor0 _ form | .ctor1 _ _ form | .ctor2 _ _ _ form => some form
  | _ => none

/-- Patterns are typed structurally; any constructor form is admitted in a
pattern, the same-name form only for a same-name constructor. -/
def patTyped (decls : List Decl) : Nat → Ty → Pat → Bool
  | 0, _, _ => false
  | _ + 1, _, .wild => true
  | _ + 1, _, .var _ => true
  | fuel + 1, .tuple left right, .tuple first second =>
      patTyped decls fuel left first && patTyped decls fuel right second
  | _ + 1, .tuple _ _, _ => false
  | fuel + 1, type, pattern => match constructorsOf decls type, pattern.head, pattern.form? with
      | some constructors, some (index, fields), some form => match constructors[index]? with
          | some types => types.length = fields.length && formAdmitted decls type index true form &&
              (types.zip fields).all fun (fieldType, field) => patTyped decls fuel fieldType field
          | none => false
      | _, _, _ => false

/-- The variables a pattern binds at a type, in order. -/
def patBindings (decls : List Decl) : Nat → Ty → Pat → List (Nat × Ty)
  | 0, _, _ => []
  | _ + 1, _, .wild => []
  | _ + 1, type, .var name => [(name, type)]
  | fuel + 1, type, pattern => match constructorsOf decls type, pattern.head with
      | some constructors, some (index, fields) =>
          ((constructors.getD index []).zip fields).flatMap fun (fieldType, field) =>
            patBindings decls fuel fieldType field
      | _, _ => []

def patFuel : Nat := 4 * typeFuel

/-! The pattern-matrix algorithm: is a vector useful after these rows? -/

private def specialize (index arity : Nat) (rows : List (List Pat)) : List (List Pat) :=
  rows.filterMap fun
    | first :: rest => match first.head with
        | none => some (List.replicate arity .wild ++ rest)
        | some (other, fields) => if other = index then some (fields ++ rest) else none
    | [] => none

private def defaultRows (rows : List (List Pat)) : List (List Pat) :=
  rows.filterMap fun
    | first :: rest => if first.head.isNone then some rest else none
    | [] => none

private def anyUseful (results : List (Option Bool)) : Option Bool :=
  if results.contains (some true) then some true
  else if results.contains none then none else some false

/-- `none` when fuel runs out. A Word or parameter column admits only
variables and wildcards. -/
def useful (decls : List Decl) : Nat → List Ty → List (List Pat) → List Pat → Option Bool
  | 0, _, _, _ => none
  | _ + 1, _, [], _ => some true
  | _ + 1, [], _ :: _, _ => some false
  | _ + 1, _ :: _, _ :: _, [] => some false
  | fuel + 1, type :: types, rows, first :: rest =>
      match constructorsOf decls type with
      | none => useful decls fuel types (rows.map List.tail) rest
      | some constructors =>
          match first.head with
          | some (index, fields) =>
              let fieldTypes := constructors.getD index []
              useful decls fuel (fieldTypes ++ types) (specialize index fieldTypes.length rows) (fields ++ rest)
          | none =>
              let heads := rows.filterMap fun row => (row.headD .wild).head.map Prod.fst
              if (List.range constructors.length).all heads.contains then
                anyUseful ((List.range constructors.length).map fun index =>
                  let fieldTypes := constructors.getD index []
                  useful decls fuel (fieldTypes ++ types) (specialize index fieldTypes.length rows)
                    (fieldTypes.map (fun _ => Pat.wild) ++ rest))
              else useful decls fuel types (defaultRows rows) rest

def usefulFuel : Nat := 512

def usefulRow (decls : List Decl) (types : List Ty) (rows : List (List Pat)) (row : List Pat) : Option Bool :=
  useful decls usefulFuel types rows row

def exhaustive (decls : List Decl) (types : List Ty) (rows : List (List Pat)) : Option Bool :=
  (usefulRow decls types rows (types.map fun _ => .wild)).map (!·)

/-! Arm bodies: a left fold of terms, then the arm's constant. -/

inductive Op where
  | add
  | sub
  | xor
  | mul
  deriving Repr, BEq, DecidableEq, Inhabited

namespace Op

def name : Op → String
  | .add => "add"
  | .sub => "sub"
  | .xor => "xor"
  | .mul => "mul"

def ofString? : String → Option Op
  | "add" => some .add
  | "sub" => some .sub
  | "xor" => some .xor
  | "mul" => some .mul
  | _ => none

def binary : Op → BinaryOp
  | .add => .wordAdd
  | .sub => .wordSub
  | .xor => .wordXor
  | .mul => .wordMul

def token : Op → String
  | .add => "+"
  | .sub => "-"
  | .xor => "^"
  | .mul => "*"

end Op

inductive Term where
  | name (name : Nat)
  | constant (value : Nat)
  deriving Repr, BEq, DecidableEq, Inhabited

structure Body where
  first : Term
  rest : List (Op × Term)
  constant : Nat
  deriving Repr, BEq, DecidableEq, Inhabited

def maximumTerms : Nat := 4

/-- An arm of a nested match: one pattern, or none for `default`. -/
structure InnerArm where
  patterns : List Pat
  body : Body
  deriving Repr, BEq, DecidableEq, Inhabited

inductive ArmBody where
  | expr (body : Body)
  | nested (scrutinee : Nat) (arms : List InnerArm)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- One pattern per column, or none for `default`. -/
structure Arm where
  patterns : List Pat
  body : ArmBody
  deriving Repr, BEq, DecidableEq, Inhabited

def maximumArms : Nat := 8
def maximumInnerArms : Nat := 6

inductive Kind where
  | single
  | pair
  | generic
  deriving Repr, BEq, DecidableEq, Inhabited

namespace Kind

def name : Kind → String
  | .single => "single"
  | .pair => "pair"
  | .generic => "generic"

def ofString? : String → Option Kind
  | "single" => some .single
  | "pair" => some .pair
  | "generic" => some .generic
  | _ => none

end Kind

/-- A view matches one value (`single`), two (`pair`), or one value of a
generic declaration at its parameter (`generic`), called at two instances.
Builders: one per scrutinee, or one per instance. -/
structure View where
  kind : Kind
  scrutinees : List Ty
  instances : List Ty
  arms : List Arm
  builders : List Builder
  wordOffset : Nat
  deriving Repr, BEq, DecidableEq, Inhabited

def maximumViews : Nat := 3

structure Plan where
  decls : List Decl
  views : List View
  deriving Repr, BEq, DecidableEq, Inhabited

/-! Admission. -/

abbrev Names := List (Nat × Ty)

def lookupType (scope : Names) (name : Nat) : Option Ty :=
  (scope.find? (·.1 = name)).map Prod.snd

def termAdmitted (scope : Names) : Term → Bool
  | .name name => lookupType scope name == some .word
  | .constant value => value < 2 ^ 256

def bodyAdmitted (scope : Names) (body : Body) : Bool :=
  body.rest.length < maximumTerms && termAdmitted scope body.first &&
    body.rest.all (fun (_, term) => termAdmitted scope term) && body.constant < 2 ^ 256

/-- The rows' patterns are typed, each row's names distinct, `default` only
last, every arm useful and the match exhaustive. -/
def rowsAdmitted (decls : List Decl) (types : List Ty) (rows : List (List Pat)) : Bool := Id.run do
  let mut previous : List (List Pat) := []
  for (row, index) in rows.zipIdx do
    if row.isEmpty then
      unless index + 1 = rows.length do return false
      unless usefulRow decls types previous (types.map fun _ => .wild) == some true do return false
      return true
    unless row.length = types.length do return false
    unless (types.zip row).all (fun (type, pattern) => patTyped decls patFuel type pattern) do return false
    let variables := row.flatMap Pat.variables
    unless variables.length = variables.eraseDups.length && variables.all (· ≤ parameterName) do return false
    unless usefulRow decls types previous row == some true do return false
    previous := previous ++ [row]
  return exhaustive decls types previous == some true

def rowBindings (decls : List Decl) (types : List Ty) (row : List Pat) : Names :=
  (types.zip row).flatMap fun (type, pattern) => patBindings decls patFuel type pattern

/-- A nested match is on a variable of an enum or tuple type. -/
def innerAdmitted (decls : List Decl) (scope : Names) (scrutinee : Nat) (arms : List InnerArm) : Bool :=
  match lookupType scope scrutinee with
  | some type => (constructorsOf decls type).isSome && 0 < arms.length && arms.length ≤ maximumInnerArms &&
      rowsAdmitted decls [type] (arms.map (·.patterns)) &&
      arms.all fun arm => bodyAdmitted (rowBindings decls [type] arm.patterns ++ scope) arm.body
  | none => false

def armsAdmitted (decls : List Decl) (types : List Ty) (arms : List Arm) : Bool :=
  0 < arms.length && arms.length ≤ maximumArms && rowsAdmitted decls types (arms.map (·.patterns)) &&
    arms.all fun arm =>
      let scope := rowBindings decls types arm.patterns ++ [(parameterName, .word)]
      match arm.body with
      | .expr body => bodyAdmitted scope body
      | .nested scrutinee inner => innerAdmitted decls scope scrutinee inner

def typeAdmitted (decls : List Decl) (type : Ty) : Bool :=
  validUse decls false type && wireTypeNodes (wireTy decls type) ≤ typeLimit

/-- A scrutinee is an enum or an instance of a generic one. -/
def scrutineeAdmitted (decls : List Decl) (type : Ty) : Bool :=
  typeAdmitted decls type && (match type with
    | .enum _ | .applied _ _ => true
    | _ => false)

def View.instanceTypes (view : View) : List Ty :=
  match view.kind, view.scrutinees with
  | .generic, [scrutinee] => view.instances.map fun argument => Ty.subst argument scrutinee
  | _, scrutinees => scrutinees

def View.admitted (decls : List Decl) (view : View) : Bool :=
  view.wordOffset < 2 ^ 256 && armsAdmitted decls view.scrutinees view.arms &&
    view.builders.length = view.instanceTypes.length &&
    (view.instanceTypes.zip view.builders).all (fun (type, builder) => builder.admitted decls type) &&
    match view.kind, view.scrutinees, view.instances with
    | .single, [type], [] => scrutineeAdmitted decls type
    | .pair, [first, second], [] => scrutineeAdmitted decls first && scrutineeAdmitted decls second
    | .generic, [.applied index .param], [first, second] =>
        (decls[index]?.map (·.generic)).getD false && first != second &&
        typeAdmitted decls first && typeAdmitted decls second &&
        validUse decls true (.applied index .param) &&
        view.instanceTypes.all (scrutineeAdmitted decls)
    | _, _, _ => false

def Decl.admitted (decls : List Decl) (index : Nat) (decl : Decl) : Bool :=
  2 ≤ decl.constructors.length && decl.constructors.length ≤ maximumConstructors &&
    decl.constructors.all (fun fields => fields.length ≤ maximumFields &&
      fields.all (validIn decls index decl.generic)) &&
    (!decl.sameName || (decl.constructors.headD []).length > 0) &&
    declNodes decls decl ≤ typeLimit

def Plan.admitted (plan : Plan) : Bool :=
  0 < plan.decls.length && plan.decls.length ≤ maximumDecls &&
    plan.decls.zipIdx.all (fun (decl, index) => decl.admitted plan.decls index) &&
    0 < plan.views.length && plan.views.length ≤ maximumViews &&
    plan.views.all (View.admitted plan.decls)

/-! The Core reference. Variables are compiled from absolute levels: at depth
`d`, level `l` is de Bruijn index `d - 1 - l`. -/

abbrev Scope := List (Nat × Ty × Nat)

private def word (value : Nat) : Expr := .word (Word.ofNatModulo value)

private def varAt (depth level : Nat) : Expr := .var (depth - 1 - level)

def lookupLevel (scope : Scope) (name : Nat) : Option (Ty × Nat) :=
  (scope.find? (·.1 = name)).map Prod.snd

def termExpr (depth : Nat) (scope : Scope) : Term → Expr
  | .name name => match lookupLevel scope name with
      | some (_, level) => varAt depth level
      | none => .unit
  | .constant value => word value

def bodyExpr (depth : Nat) (scope : Scope) (body : Body) : Expr :=
  let folded := body.rest.foldl
    (fun accumulated (op, term) => .binary op.binary accumulated (termExpr depth scope term))
    (termExpr depth scope body.first)
  .binary .wordAdd folded (word body.constant)

/-- The `caseE` chain to constructor `target` of a value at `level` whose type
is the sum chain of `payloads`. `inner` receives the depth and the payload's
level. -/
def chainCases (failure : Nat → Expr) (inner : Nat → Nat → Expr) : Nat → Nat → List WireTy → Nat → Expr
  | depth, level, [_], _ => inner depth level
  | depth, level, _ :: _, 0 => .caseE (varAt depth level) (inner (depth + 1) depth) (failure (depth + 1))
  | depth, level, _ :: rest, target + 1 =>
      .caseE (varAt depth level) (failure (depth + 1)) (chainCases failure inner (depth + 1) depth rest target)
  | _, _, [], _ => .unit

/-- Match a pattern against the value at `level`. `success` continues at a
depth with the extended scope; `failure` falls back at a depth. Components
are projected and let-bound unless their pattern is a wildcard. -/
def patExpr (decls : List Decl) : Nat → Nat → Scope → Ty → Nat → Pat →
    (Nat → Scope → Expr) → (Nat → Expr) → Expr
  | 0, _, _, _, _, _, _, _ => .unit
  | fuel + 1, depth, scope, type, level, pattern, success, failure =>
      let pair := fun (depth level : Nat) (left right : Ty) (first second : Pat)
          (success : Nat → Scope → Expr) =>
        let continueSecond := fun (depth : Nat) (scope : Scope) =>
          if second == .wild then success depth scope
          else .letE (.second (varAt depth level))
            (patExpr decls fuel (depth + 1) scope right depth second success failure)
        if first == .wild then continueSecond depth scope
        else .letE (.first (varAt depth level))
          (patExpr decls fuel (depth + 1) scope left depth first continueSecond failure)
      match pattern with
      | .wild => success depth scope
      | .var name => success depth ((name, type, level) :: scope)
      | _ => match type, constructorsOf decls type, pattern.head with
          | .tuple left right, _, some (_, [first, second]) => pair depth level left right first second success
          | _, some constructors, some (index, fields) =>
              let types := constructors.getD index []
              let inner := fun (depth payload : Nat) => match types, fields with
                | [], [] => success depth scope
                | [fieldType], [field] => patExpr decls fuel depth scope fieldType payload field success failure
                | [left, right], [first, second] => pair depth payload left right first second success
                | _, _ => .unit
              chainCases failure inner depth level (payloadWires decls constructors) index
          | _, _, _ => .unit

def columnsExpr (decls : List Decl) (depth : Nat) (scope : Scope) :
    List ((Ty × Nat) × Pat) → (Nat → Scope → Expr) → (Nat → Expr) → Expr
  | [], success, _ => success depth scope
  | ((type, level), pattern) :: rest, success, failure =>
      patExpr decls patFuel depth scope type level pattern
        (fun depth scope => columnsExpr decls depth scope rest success failure) failure

/-- Arms in order: each but the last is tried with the thunk of the remaining
arms as its failure; the last is reached only when exhaustiveness says it
matches. -/
def armsExpr {α : Type} (decls : List Decl) (bodyOf : Nat → Scope → α → Expr) (scope : Scope)
    (columns : List (Ty × Nat)) : Nat → List (List Pat × α) → Expr
  | _, [] => word 0
  | depth, [(patterns, body)] =>
      columnsExpr decls depth scope (columns.zip patterns) (fun depth scope => bodyOf depth scope body)
        (fun _ => word 0)
  | depth, (patterns, body) :: rest =>
      .letE (.lambda .unit .word (armsExpr decls bodyOf scope columns (depth + 1) rest))
        (columnsExpr decls (depth + 1) scope (columns.zip patterns) (fun depth scope => bodyOf depth scope body)
          (fun later => .apply (varAt later depth) .unit))

def armBodyExpr (decls : List Decl) (depth : Nat) (scope : Scope) : ArmBody → Expr
  | .expr body => bodyExpr depth scope body
  | .nested scrutinee arms => match lookupLevel scope scrutinee with
      | some (type, level) =>
          armsExpr decls (fun depth scope body => bodyExpr depth scope body) scope [(type, level)] depth
            (arms.map fun arm => (arm.patterns, arm.body))
      | none => .unit

/-- A view's closure at its instance types: scrutinees, then the Word. -/
def viewExpr (decls : List Decl) (arms : List Arm) (types : List Ty) : Expr :=
  let count := types.length
  let body := armsExpr decls (armBodyExpr decls) [(parameterName, .word, count)]
    (types.zipIdx.map fun (type, index) => (type, index)) (count + 1)
    (arms.map fun arm => (arm.patterns, arm.body))
  let wires := types.map (wireTy decls)
  let final := Expr.lambda .word .word body
  (wires.zipIdx.reverse.foldl (fun (inner, innerType) (wire, _) =>
      (Expr.lambda wire innerType inner, Solcore.Core.Wire.Ty.function wire innerType))
    (final, Solcore.Core.Wire.Ty.function .word .word)).1

/-- The closures of a view and its calls: each call applies a view closure to
the builders' values and to `input + wordOffset`. -/
structure Closures where
  closures : List Expr
  calls : List (Nat × List Nat × Nat)

def View.closures (decls : List Decl) (view : View) (base : Nat) : Closures :=
  match view.kind with
  | .generic =>
      let types := view.instanceTypes
      let views := types.map fun type => viewExpr decls view.arms [type]
      let builders := (types.zip view.builders).map fun (type, builder) => builderExpr decls type builder
      ⟨views ++ builders, types.zipIdx.map fun (_, index) =>
        (base + index, [base + types.length + index], view.wordOffset)⟩
  | _ =>
      let types := view.scrutinees
      let builders := (types.zip view.builders).map fun (type, builder) => builderExpr decls type builder
      ⟨viewExpr decls view.arms types :: builders,
        [(base, (List.range types.length).map (base + 1 + ·), view.wordOffset)]⟩

/-- The calls' results combined as `r_0 + 3 r_1 + 5 r_2 + …`. -/
def combine (depth first count : Nat) : Expr :=
  (List.range count).foldl (fun accumulated index =>
      if index = 0 then varAt depth first
      else .binary .wordAdd accumulated (.binary .wordMul (varAt depth (first + index)) (word (2 * index + 1))))
    (word 0)

def Plan.closures (plan : Plan) : Closures :=
  plan.views.foldl (fun accumulated view =>
      let next := view.closures plan.decls accumulated.closures.length
      ⟨accumulated.closures ++ next.closures, accumulated.calls ++ next.calls⟩) ⟨[], []⟩

/-- The program: the closures let-bound in order, then the entry over the
input, binding each call's Word in order and combining them. -/
def Plan.expression (plan : Plan) : Expr :=
  let closures := plan.closures
  let input := closures.closures.length
  let callExpr := fun (depth : Nat) (call : Nat × List Nat × Nat) =>
    let (viewLevel, builders, offset) := call
    let applied := builders.foldl
      (fun function builder => Expr.apply function (.apply (varAt depth builder) (varAt depth input)))
      (varAt depth viewLevel)
    Expr.apply applied (.binary .wordAdd (varAt depth input) (word offset))
  let entry := closures.calls.foldr
    (fun call inner => fun depth => Expr.letE (callExpr depth call) (inner (depth + 1)))
    (fun depth => combine depth (input + 1) closures.calls.length)
  closures.closures.foldr (fun closure inner => .letE closure inner) (.lambda .word .word (entry (input + 1)))

def Plan.program (plan : Plan) : Program := {
  resultType := .function .word .word, dataDefinitions := [], body := plan.expression}

def Plan.applied (plan : Plan) (input : Word) : Program := {
  resultType := .word, dataDefinitions := [], body := .apply plan.expression (.word input)}

def Plan.nodes (plan : Plan) : Nat := programNodes (plan.applied Word.zero)

/-! Specified shapes, from the plan, never measured. -/

def fieldKind : Ty → String
  | .word => "word"
  | .param => "param"
  | .tuple _ _ => "tuple"
  | .enum _ => "enum"
  | .applied _ _ => "applied"

def argumentKind : Ty → String
  | .word => "word"
  | .param => "param"
  | .tuple _ _ => "tuple"
  | _ => "enum"

/-- The arguments of every generic instance inside a type. -/
def Ty.arguments : Ty → List Ty
  | .tuple left right => left.arguments ++ right.arguments
  | .applied _ argument => argument :: argument.arguments
  | _ => []

/-- Constructor forms, nullary, tuple, variable and wildcard patterns, and
wildcard positions: `field`, `component`, `deep` (below two layers). -/
def Pat.forms : Nat → Pat → List String
  | _, .wild => ["wildcard"]
  | _, .var _ => ["variable"]
  | level, .tuple left right =>
      "tuple" :: (inside level left "component" ++ inside level right "component")
  | _, .ctor0 _ form => ["nullary", form.name]
  | level, .ctor1 _ field form => form.name :: inside level field "field"
  | level, .ctor2 _ first second form => form.name :: (inside level first "field" ++ inside level second "field")
where
  inside (level : Nat) (pattern : Pat) (position : String) : List String :=
    (if pattern == .wild then ["wildcard:" ++ position] ++ (if level ≥ 1 then ["wildcard:deep"] else []) else []) ++
      pattern.forms (level + 1)

def rowForms (rows : List (List Pat)) : List String :=
  let catchAll := fun (row : List Pat) => row.all fun pattern => pattern.head.isNone
  let rowNames := rows.map fun row => (row.flatMap Pat.variables).eraseDups
  (rows.flatMap fun row => match row with
    | [] => ["default"]
    | [.wild] => ["wildcard:arm"] ++ ["wildcard"]
    | patterns =>
        (if patterns.length > 1 && !catchAll patterns && patterns.contains .wild then ["wildcard:column"] else []) ++
        (if patterns.length > 1 && patterns.all (· == .wild) then ["wildcard:arm"] else []) ++
        patterns.flatMap (Pat.forms 0) ++
        (if (row.flatMap Pat.variables).contains parameterName then ["shadow"] else [])) ++
  (if !rows.any catchAll then ["exhaustive"] else []) ++
  (if (rowNames.flatMap id).length != (rowNames.flatMap id).eraseDups.length then ["repeated"] else [])

def rowDepths (rows : List (List Pat)) : List String :=
  rows.flatMap fun row => row.filterMap fun pattern =>
    if pattern.depth = 0 then none else some (toString (min pattern.depth 3))

def Arm.innerRows : Arm → List (List Pat)
  | {body := .nested _ inner, ..} => inner.map (·.patterns)
  | _ => []

def Plan.shapes (plan : Plan) : List (String × List String) :=
  let decls := plan.decls
  let fieldTypes := decls.flatMap fun decl => decl.constructors.flatMap id
  let useTypes := plan.views.flatMap fun view => view.scrutinees ++ view.instanceTypes
  let arguments := (fieldTypes ++ useTypes).flatMap Ty.arguments
  let tables := plan.views.flatMap fun view =>
    (view.arms.map (·.patterns)) :: view.arms.filterMap fun arm =>
      if arm.innerRows.isEmpty then none else some arm.innerRows
  let rebound := plan.views.any fun view => view.arms.any fun arm => match arm.body with
    | .nested _ inner => inner.any fun innerArm =>
        (innerArm.patterns.flatMap Pat.variables).any (arm.patterns.flatMap Pat.variables).contains
    | .expr _ => false
  let nested := plan.views.any fun view => view.arms.any fun arm => !arm.innerRows.isEmpty
  let patterns := (tables.flatMap rowForms) ++ (if nested then ["nested"] else []) ++
    (if rebound then ["rebound"] else [])
  let sorted := fun (values : List String) => values.eraseDups.mergeSort (· ≤ ·)
  [("constructors", sorted (decls.map fun decl => toString decl.constructors.length)),
   ("fields", sorted (decls.flatMap (fun decl => decl.constructors.map fun fields => "count:" ++ toString fields.length) ++
      fieldTypes.map fun type => "type:" ++ fieldKind type)),
   ("declarations", sorted (decls.flatMap (fun decl =>
      [if decl.generic then "generic" else "plain"] ++ (if decl.sameName then ["same-name"] else [])) ++
      arguments.map fun argument => "argument:" ++ argumentKind argument)),
   ("views", sorted (plan.views.map (·.kind.name))),
   ("patterns", sorted (patterns.filter fun shape => !shape.startsWith "wildcard:")),
   ("wildcards", sorted ((patterns.filter (·.startsWith "wildcard:")).map (·.drop 9 |>.toString))),
   ("depths", sorted (tables.flatMap rowDepths))]

/-! Generation from the case seed's stream. -/

/-- Separates the plan stream from other uses of a case seed. -/
def domain : UInt64 := 0x656e756d6d617401

/-- A variable (one of the five names, unless the row already binds it) or a
wildcard; always two draws. -/
def drawLeafPat (used : List Nat) : Gen (Pat × List Nat) := do
  let choice ← draw 2
  let name ← draw names.length
  if choice = 0 || used.contains name then return (.wild, used) else return (.var name, name :: used)

def drawPatForm (decls : List Decl) (type : Ty) (index : Nat) : Gen Form := do
  match ← drawWeighted [3, 1, if formAdmitted decls type index true .sameName then 2 else 0] with
  | 0 => return .qualified
  | 1 => return .dot
  | _ => return .sameName

/-- Refinement weights out of 12 by nesting level: 3/4, 1/2, 1/3, then none. -/
def refineWeight : Nat → Nat
  | 0 => 9
  | 1 => 6
  | 2 => 4
  | _ => 0

/-- A random pattern at a type: a constructor or tuple pattern with random
subpatterns, or a leaf. -/
def drawPat (decls : List Decl) : Nat → Nat → Ty → List Nat → Gen (Pat × List Nat)
  | 0, _, _, used => pure (.wild, used)
  | fuel + 1, level, type, used => do
      let choice ← draw 12
      match constructorsOf decls type with
      | none => drawLeafPat used
      | some constructors =>
          if choice ≥ refineWeight level then drawLeafPat used
          else match type with
            | .tuple left right => do
                let (first, used) ← drawPat decls fuel (level + 1) left used
                let (second, used) ← drawPat decls fuel (level + 1) right used
                return (.tuple first second, used)
            | _ => do
                let index ← draw constructors.length
                let form ← drawPatForm decls type index
                match constructors.getD index [] with
                | [field] => do
                    let (pattern, used) ← drawPat decls fuel (level + 1) field used
                    return (.ctor1 index pattern form, used)
                | [first, second] => do
                    let (left, used) ← drawPat decls fuel (level + 1) first used
                    let (right, used) ← drawPat decls fuel (level + 1) second used
                    return (.ctor2 index left right form, used)
                | _ => return (.ctor0 index form, used)

def drawRow (decls : List Decl) (types : List Ty) : Gen (List Pat) := do
  let mut used : List Nat := []
  let mut row : List Pat := []
  for type in types do
    let (pattern, next) ← drawPat decls patFuel 0 type used
    used := next
    row := row ++ [pattern]
  return row

/-- A first-column constructor with leaf subpatterns, other columns leaves. -/
def completionRow (decls : List Decl) (types : List Ty) (index : Nat) : Gen (List Pat) := do
  let mut used : List Nat := []
  let mut row : List Pat := []
  for (type, column) in types.zipIdx do
    let fieldTypes := if column = 0 then ((constructorsOf decls type).getD []).getD index [] else []
    let mut fields : List Pat := []
    for _ in fieldTypes do
      let (pattern, next) ← drawLeafPat used
      used := next
      fields := fields ++ [pattern]
    if column = 0 then
      let form ← drawPatForm decls type index
      let pattern := match type, fields with
        | .tuple _ _, [first, second] => Pat.tuple first second
        | _, [] => .ctor0 index form
        | _, [field] => .ctor1 index field form
        | _, [first, second] => .ctor2 index first second form
        | _, _ => .wild
      row := row ++ [pattern]
    else
      let (pattern, next) ← drawLeafPat used
      used := next
      row := row ++ [pattern]
  return row

/-- Up to `target` useful random rows, three candidates each; then, at random,
each useful first-column constructor with leaf subpatterns; then, if not
exhaustive, a catch-all: `default`, wildcards, or a variable first. At most
`limit` rows. -/
def drawRows (decls : List Decl) (types : List Ty) (target limit : Nat) : Gen (List (List Pat)) := do
  let mut rows : List (List Pat) := []
  for _ in List.range (min target (limit - 1)) do
    let mut added := false
    for _ in List.range 3 do
      let row ← drawRow decls types
      if !added && usefulRow decls types rows row == some true then
        rows := rows ++ [row]
        added := true
  let complete ← draw 2
  if complete = 0 && exhaustive decls types rows != some true then
    let count := ((types.headD .word |> constructorsOf decls).getD []).length
    for index in List.range count do
      let row ← completionRow decls types index
      if rows.length + 1 < limit && usefulRow decls types rows row == some true then
        rows := rows ++ [row]
  if exhaustive decls types rows != some true then
    match ← draw 3 with
    | 0 => rows := rows ++ [[]]
    | 1 => rows := rows ++ [types.map fun _ => Pat.wild]
    | _ => do
        let name ← draw parameterName
        rows := rows ++ [(Pat.var name) :: (types.drop 1).map fun _ => Pat.wild]
  return rows

def visibleWords (scope : Names) : List Nat :=
  (List.range names.length).filter fun name => lookupType scope name == some .word

def drawTerm (words : List Nat) : Gen Term := do
  if words.isEmpty || (← draw 4) = 0 then return .constant (← drawConstant)
  return .name (words.getD (← draw words.length) 0)

def opOf : Nat → Op
  | 0 => .add
  | 1 => .sub
  | 2 => .xor
  | _ => .mul

/-- The Words the row binds, visible in its scope, in binding order. -/
def boundWords (bindings scope : Names) : List Nat :=
  (bindings.filter fun (name, type) => type == .word && lookupType scope name == some .word).map Prod.fst

/-- Every bound Word up to the term limit, then one drawn term if room is
left, combined by drawn operations. -/
def drawBody (scope : Names) (bound : List Nat) : Gen Body := do
  let words := visibleWords scope
  let required := (bound.take maximumTerms).map Term.name
  let extra ← draw 2
  let mut terms := required
  if terms.isEmpty || (extra = 0 && terms.length < maximumTerms) then
    terms := terms ++ [← drawTerm words]
  let mut rest : List (Op × Term) := []
  for term in terms.drop 1 do
    rest := rest ++ [(opOf (← draw 4), term)]
  return {first := terms.headD (.constant 0), rest, constant := ← drawBits}

/-- A quarter of the arms that bind an enum or tuple value match it again. -/
def drawArmBody (decls : List Decl) (types : List Ty) (row : List Pat) : Gen ArmBody := do
  let bindings := rowBindings decls types row
  let scope := bindings ++ [(parameterName, .word)]
  let candidates := bindings.filter fun (_, type) => (constructorsOf decls type).isSome
  if (← draw 4) = 0 && !candidates.isEmpty then
    let (name, type) := candidates.getD (← draw candidates.length) (0, .word)
    let rows ← drawRows decls [type] (2 + (← draw 3)) maximumInnerArms
    let mut arms : List InnerArm := []
    for row in rows do
      let inner := rowBindings decls [type] row
      arms := arms ++ [{patterns := row, body := ← drawBody (inner ++ scope) (boundWords inner (inner ++ scope))}]
    return .nested name arms
  return .expr (← drawBody scope (boundWords bindings scope))

def drawArms (decls : List Decl) (types : List Ty) : Gen (List Arm) := do
  let rows ← drawRows decls types (2 + (← draw 5)) maximumArms
  let mut arms : List Arm := []
  for row in rows do
    arms := arms ++ [{patterns := row, body := ← drawArmBody decls types row}]
  return arms

/-- The first arm a single-column match selects for a value. -/
def firstArm (arms : List Arm) (value : Value) : Nat :=
  (arms.findIdx? fun arm => match arm.patterns with
    | [] => true
    | [pattern] => pattern.accepts value
    | _ => false).getD arms.length

/-- Each tree is the first of four candidates whose arm no earlier tree
selects, or the first candidate. Without arms, a candidate's top-level
constructor stands for its arm. -/
def drawBuilder (decls : List Decl) (type : Ty) (arms : Option (List Arm)) : Gen Builder := do
  let offset ← draw 4
  let count := 1 + (← draw maximumTrees)
  let mut trees : List Value := []
  let mut hit : List Nat := []
  for _ in List.range count do
    let mut chosen : Option Value := none
    for _ in List.range 4 do
      let value ← drawValue decls valueFuel true type
      let arm := match arms, value.constructor? with
        | some arms, _ => firstArm arms value
        | none, some (index, _, _) => index
        | none, none => 0
      if chosen.isNone && !hit.contains arm then
        chosen := some value
        hit := arm :: hit
    let fallback ← drawValue decls valueFuel true type
    trees := trees ++ [chosen.getD fallback]
  return {offset, trees}

def drawArgument (decls : List Decl) : Gen Ty := do
  let plain := (List.range decls.length).filter fun index => !(decls.getD index default).generic
  match ← drawWeighted [2, 1, if plain.isEmpty then 0 else 1] with
  | 0 => return .word
  | 1 => return .tuple .word .word
  | _ => return .enum (plain.getD (← draw plain.length) 0)

def drawScrutinee (decls : List Decl) : Gen Ty := do
  let index ← draw decls.length
  if (decls.getD index default).generic then
    let type := Ty.applied index (← drawArgument decls)
    return if scrutineeAdmitted decls type then type else .applied index .word
  return .enum index

def drawView (decls : List Decl) : Gen View := do
  let generics := (List.range decls.length).filter fun index => (decls.getD index default).generic
  let kind ← drawWeighted [3, 2, if generics.isEmpty then 0 else 2]
  let wordOffset ← drawConstant
  match kind with
  | 0 => do
      let type ← drawScrutinee decls
      let arms ← drawArms decls [type]
      let builder ← drawBuilder decls type (some arms)
      return {kind := .single, scrutinees := [type], instances := [], arms, builders := [builder], wordOffset}
  | 1 => do
      let first ← drawScrutinee decls
      let second ← drawScrutinee decls
      let arms ← drawArms decls [first, second]
      let left ← drawBuilder decls first none
      let right ← drawBuilder decls second none
      return {kind := .pair, scrutinees := [first, second], instances := [], arms, builders := [left, right],
              wordOffset}
  | _ => do
      let index := generics.getD (← draw generics.length) 0
      let admit := fun (argument : Ty) => if scrutineeAdmitted decls (.applied index argument) then argument else .word
      let first := admit (← drawArgument decls)
      let drawn := admit (← drawArgument decls)
      let second := if drawn == first then (if first == .word then .tuple .word .word else .word) else drawn
      let arms ← drawArms decls [.applied index .param]
      let left ← drawBuilder decls (.applied index first) (some arms)
      let right ← drawBuilder decls (.applied index second) (some arms)
      return {kind := .generic, scrutinees := [.applied index .param], instances := [first, second], arms,
              builders := [left, right], wordOffset}

def drawPlan : Gen Plan := do
  let decls ← drawDecls
  let count := 1 + (← draw maximumViews)
  let mut views : List View := []
  for _ in List.range count do
    views := views ++ [← drawView decls]
  return {decls, views}

def generate (seed : UInt64) : Plan :=
  Id.run (drawPlan.run' {seed, domain, index := 0})

/-- Views are dropped from the end while the reference exceeds the budget and
more than one remains. -/
def Plan.fit (nodes : Nat) (plan : Plan) : Plan := Id.run do
  let mut fitted := plan
  for _ in List.range maximumViews do
    if fitted.nodes > nodes && fitted.views.length > 1 then
      fitted := {fitted with views := fitted.views.dropLast}
  return fitted

end Solcore.Synthesis.Core.Enums
