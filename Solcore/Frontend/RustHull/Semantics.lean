import Solcore.Frontend.RustHull.Syntax
import Solcore.Core.Primitive

/-! Independent evaluation rules for Hull. Source values, names and locations
are distinct from Core values and locations. Word arithmetic shares only the
mathematical 256-bit operations. External effects are an explicit parameter;
no evaluation rule refers to the compiler or the Core evaluator. -/
set_option autoImplicit false

namespace Solcore.Frontend.RustHull.Semantics

inductive Value where
  | word (value : Core.Word)
  | bool (value : Bool)
  | unit
  | pair (left right : Value)
  | inl (value : Value)
  | inr (value : Value)
  deriving Repr, BEq, DecidableEq

abbrev Environment := List (String × Nat)
abbrev Heap := List Value

structure State (σ : Type) where
  heap : Heap
  external : σ

def lookupLocation (environment : Environment) (name : String) : Option Nat :=
  (environment.find? (·.1 == name)).map Prod.snd

def allocate {σ : Type} (state : State σ) (value : Value) : Nat × State σ :=
  (state.heap.length, {state with heap := state.heap ++ [value]})

def write? {σ : Type} (state : State σ) (location : Nat) (value : Value) : Option (State σ) :=
  if location < state.heap.length then some {state with heap := state.heap.set location value}
  else none

inductive Fault where
  | language (reason : Core.Word)
  | invalidLiteral (text : String)
  | unknownVariable (name : String)
  | invalidLocation (location : Nat)
  | invalidValue (operation : String)
  | invalidPlace
  | invalidInjection
  | unsupportedType
  | arityMismatch
  deriving Repr, BEq, DecidableEq

inductive Result (α : Type) where
  | value (value : α)
  | fault (fault : Fault)
  deriving Repr, BEq

def Result.map {α β : Type} (f : α → β) : Result α → Result β
  | .value payload => .value (f payload)
  | .fault reason => .fault reason

def Result.bind {α β : Type} (result : Result α) (next : α → Result β) : Result β :=
  match result with
  | .value payload => next payload
  | .fault reason => .fault reason

inductive Control where
  | fallthrough
  | returned (value : Value)
  | breaking
  | continuing
  | fault (reason : Fault)
  deriving Repr, BEq, DecidableEq

inductive Shape where
  | word | bool | unit
  | product (left right : Shape)
  | sum (left right : Shape)
  deriving Repr, BEq, DecidableEq

/-- Names are transparent except recursive references, whose backend layout
is one opaque word. No implicit boxing or unfolding is part of Hull. -/
def shape : Ty → Option Shape
  | .word | .namedRef _ => some .word
  | .bool => some .bool
  | .unit => some .unit
  | .product left right => return .product (← shape left) (← shape right)
  | .sum left right => return .sum (← shape left) (← shape right)
  | .named _ inner | .located _ inner => shape inner
  | .function _ _ => none

def Shape.zero : Shape → Value
  | .word => .word Core.Word.zero
  | .bool => .bool false
  | .unit => .unit
  | .product left right => .pair left.zero right.zero
  | .sum left _ => .inl left.zero

def zero? (type : Ty) : Option Value := (shape type).map Shape.zero

def boolean? (type : Ty) (value : Bool) : Option Value :=
  match shape type with
  | some .bool => some (.bool value)
  | some (.sum .unit .unit) => some (if value then .inr .unit else .inl .unit)
  | _ => none

def condition? : Value → Option Bool
  | .bool value => some value
  | .inl .unit => some false
  | .inr .unit => some true
  | _ => none

/-- Parse a nonnegative decimal or hexadecimal literal modulo 2^256. -/
def parseWord? (text : String) : Option Core.Word := do
  let (base, digits) := match text.toList with
    | '0' :: 'x' :: digits | '0' :: 'X' :: digits => (16, digits)
    | digits => (10, digits)
  if digits.isEmpty then none else do
    let value ← digits.foldlM (fun accumulator char => do
      let digit := if '0' ≤ char && char ≤ '9' then char.toNat - '0'.toNat
        else if 'a' ≤ char && char ≤ 'f' then char.toNat - 'a'.toNat + 10
        else if 'A' ≤ char && char ≤ 'F' then char.toNat - 'A'.toNat + 10
        else base
      if digit < base then some ((accumulator * base + digit) % Core.wordModulus)
      else none) 0
    some (Core.Word.ofNatModulo value)

def literalResult (text : String) : Result Value :=
  match parseWord? text with
  | some value => .value (.word value)
  | none => .fault (.invalidLiteral text)

def booleanResult (type : Ty) (value : Bool) : Result Value :=
  match boolean? type value with
  | some value => .value value
  | none => .fault (.invalidValue "boolean representation")

def readResult {σ : Type} (environment : Environment) (state : State σ) (name : String) : Result Value :=
  match lookupLocation environment name with
  | none => .fault (.unknownVariable name)
  | some location => match state.heap[location]? with
      | some value => .value value
      | none => .fault (.invalidLocation location)

def projectResult (right : Bool) : Value → Result Value
  | .pair left value => .value (if right then value else left)
  | _ => .fault (.invalidValue "product projection")

def injectShape? (index : Nat) : Shape → Value → Option Value
  | .sum _ right, value =>
      if index = 0 then some (.inl value)
      else (injectShape? (index - 1) right value).map Value.inr
  | _, value => if index = 0 then some value else none

def inject? (index : Nat) (target : Ty) (value : Value) : Option Value := do
  injectShape? index (← shape target) value

def injectionResult (index : Nat) (target : Ty) (value : Value) : Result Value :=
  match inject? index target value with
  | some result => .value result
  | none => .fault .invalidInjection

def place? (expression : Expr) : Option (String × List Bool) :=
  match expression with
  | ⟨_, .var name, _⟩ => some (name, [])
  | ⟨_, .fst value, _⟩ => do let (name, path) ← place? value; pure (name, path ++ [false])
  | ⟨_, .snd value, _⟩ => do let (name, path) ← place? value; pure (name, path ++ [true])
  | _ => none
termination_by sizeOf expression

def updateProduct? : List Bool → Value → Value → Option Value
  | [], _, value => some value
  | direction :: rest, .pair left right, value =>
      if direction then return .pair left (← updateProduct? rest right value)
      else return .pair (← updateProduct? rest left value) right
  | _ :: _, _, _ => none

def assignResult {σ : Type} (environment : Environment) (state : State σ)
    (lhs : Expr) (value : Value) : Result (State σ) :=
  match place? lhs with
  | none => .fault .invalidPlace
  | some (name, path) => match lookupLocation environment name with
      | none => .fault (.unknownVariable name)
      | some location => match state.heap[location]? with
          | none => .fault (.invalidLocation location)
          | some old => match updateProduct? path old value with
              | none => .fault .invalidPlace
              | some updated => match write? state location updated with
                  | some final => .value final
                  | none => .fault (.invalidLocation location)

def patternIndex? (index : Nat) : Shape → Value → Option Value
  | .sum _ right, value =>
      if index = 0 then match value with
        | .inl payload => some payload
        | _ => none
      else match value with
        | .inr payload => patternIndex? (index - 1) right payload
        | _ => none
  | _, value => if index = 0 then some value else none

def patternPayload? (target : Ty) (pattern : PatKind) (value : Value) : Option Value :=
  match pattern with
  | .wildcard | .var _ => some value
  | .intLit text => match value, parseWord? text with
      | .word value, some literal => if value == literal then some (.word value) else none
      | _, _ => none
  | .con .inl => match value with | .inl payload => some payload | _ => none
  | .con .inr => match value with | .inr payload => some payload | _ => none
  | .con (.inK index) => do patternIndex? index (← shape target) value

def bindArguments {σ : Type} : List Arg → List Value → Environment → State σ → Option (Environment × State σ)
  | [], [], environment, state => some (environment, state)
  | argument :: arguments, value :: values, environment, state =>
      let (location, state) := allocate state value
      bindArguments arguments values ((argument.name, location) :: environment) state
  | _, _, _, _ => none

def finishFunction (result : Ty) : Control → Result Value
  | .returned value => .value value
  | .fault reason => .fault reason
  | .fallthrough => if shape result == some .unit then .value .unit
      else .fault (.language (Core.Word.ofNatModulo 4))
  | .breaking | .continuing => .fault (.language (Core.Word.ofNatModulo 5))

/-- Abstract external behavior is a separate source-level specification
obligation. It cannot inspect a Core expression or assume compiler correctness.
Assembly may update source locals; builtins and revert only affect external state. -/
structure ExternalSemantics (σ : Type) where
  builtin : String → Ty → List Value → σ → Result Value → σ → Prop
  assembly : List Function → Environment → List YulStmt → State σ → Control → State σ → Prop
  revert : String → σ → Control → σ → Prop

def unaryWord (operation : Core.Word → Core.Word) : List Value → Result Value
  | [.word value] => .value (.word (operation value))
  | _ => .fault (.invalidValue "unary word arguments")

def binaryWords (operation : Core.Word → Core.Word → Core.Word) : List Value → Result Value
  | [.word left, .word right] => .value (.word (operation left right))
  | _ => .fault (.invalidValue "binary word arguments")

def ternaryWords (operation : Core.Word → Core.Word → Core.Word → Core.Word) : List Value → Result Value
  | [.word first, .word second, .word third] => .value (.word (operation first second third))
  | _ => .fault (.invalidValue "ternary word arguments")

def compareWords (type : Ty) (operation : Core.Word → Core.Word → Bool) : List Value → Result Value
  | [.word left, .word right] => booleanResult type (operation left right)
  | _ => .fault (.invalidValue "comparison arguments")

/-- Pure source operations, independently specified by mathematical word
functions. Only names outside this table are delegated to external semantics. -/
def primitive? (name : String) (type : Ty) (arguments : List Value) : Option (Result Value) :=
  match name with
  | "primAddWord" | "integerAdd" | "add" => some (binaryWords Core.Word.add arguments)
  | "subWord" | "integerSub" | "sub" => some (binaryWords Core.Word.sub arguments)
  | "mulWord" | "integerMul" | "mul" => some (binaryWords Core.Word.mul arguments)
  | "div" => some (binaryWords Core.Word.udiv arguments)
  | "mod" => some (binaryWords Core.Word.umod arguments)
  | "sdiv" => some (binaryWords Core.Word.sdiv arguments)
  | "smod" => some (binaryWords Core.Word.smod arguments)
  | "exp" => some (binaryWords Core.Word.pow arguments)
  | "signextend" => some (binaryWords Core.Word.signExtend arguments)
  | "primEqWord" | "integerEq" | "eq" => some (compareWords type (· == ·) arguments)
  | "gtWord" | "gt" => some (compareWords type (fun left right => left.val > right.val) arguments)
  | "integerLt" | "lt" => some (compareWords type (fun left right => left.val < right.val) arguments)
  | "sgt" => some (compareWords type Core.Word.signedGt arguments)
  | "slt" => some (compareWords type (fun left right => Core.Word.signedGt right left) arguments)
  | "bxorWord" | "xor" => some (binaryWords Core.Word.bitXor arguments)
  | "bandWord" | "and" => some (binaryWords Core.Word.bitAnd arguments)
  | "borWord" | "or" => some (binaryWords Core.Word.bitOr arguments)
  | "bnotWord" | "not" => some (unaryWord Core.Word.bitNot arguments)
  | "clz" => some (unaryWord Core.Word.clz arguments)
  | "byte" => some (binaryWords Core.Word.byteAt arguments)
  | "shl" => some (binaryWords (fun distance value => Core.Word.shiftLeft value distance) arguments)
  | "shr" => some (binaryWords (fun distance value => Core.Word.shiftRight value distance) arguments)
  | "sar" => some (binaryWords (fun distance value => Core.Word.shiftArithmeticRight value distance) arguments)
  | "addmod" => some (ternaryWords Core.Word.addMod arguments)
  | "mulmod" => some (ternaryWords Core.Word.mulMod arguments)
  | "wordToInteger" | "wordFromInteger" => some (unaryWord id arguments)
  | "iszero" => some (match arguments with
      | [value] => match condition? value with
          | some value => booleanResult type (!value)
          | none => .fault (.invalidValue "boolean argument")
      | _ => .fault .arityMismatch)
  | "pop" => some (match arguments with
      | [.word _] => .value .unit
      | _ => .fault (.invalidValue "pop argument"))
  | _ => none

def sumInjectionResult (right : Bool) (target : Ty) (value : Value) : Result Value :=
  match shape target with
  | some (.sum _ _) => .value (if right then .inr value else .inl value)
  | _ => .fault .invalidInjection

mutual
  inductive EvalExpr {σ : Type} (functions : List Function) (effects : ExternalSemantics σ) :
      Environment → Expr → State σ → Result Value → State σ → Prop where
    | word {env expression state text} (kind : expression.kind = .word text) :
        EvalExpr functions effects env expression state (literalResult text) state
    | bool {env expression state value} (kind : expression.kind = .bool value) :
        EvalExpr functions effects env expression state (booleanResult expression.ty value) state
    | unit {env expression state} (kind : expression.kind = .unit) :
        EvalExpr functions effects env expression state (.value .unit) state
    | var {env expression state name} (kind : expression.kind = .var name) :
        EvalExpr functions effects env expression state (readResult env state name) state
    | pair {env expression initial middle final left right leftValue rightResult}
        (kind : expression.kind = .pair left right)
        (first : EvalExpr functions effects env left initial (.value leftValue) middle)
        (second : EvalExpr functions effects env right middle rightResult final) :
        EvalExpr functions effects env expression initial (rightResult.map (Value.pair leftValue)) final
    | pairFault {env expression initial final left right reason}
        (kind : expression.kind = .pair left right)
        (first : EvalExpr functions effects env left initial (.fault reason) final) :
        EvalExpr functions effects env expression initial (.fault reason) final
    | fst {env expression initial final operand result} (kind : expression.kind = .fst operand)
        (evaluated : EvalExpr functions effects env operand initial result final) :
        EvalExpr functions effects env expression initial (result.bind (projectResult false)) final
    | snd {env expression initial final operand result} (kind : expression.kind = .snd operand)
        (evaluated : EvalExpr functions effects env operand initial result final) :
        EvalExpr functions effects env expression initial (result.bind (projectResult true)) final
    | inl {env expression initial final target operand result} (kind : expression.kind = .inl target operand)
        (evaluated : EvalExpr functions effects env operand initial result final) :
        EvalExpr functions effects env expression initial (result.bind (sumInjectionResult false target)) final
    | inr {env expression initial final target operand result} (kind : expression.kind = .inr target operand)
        (evaluated : EvalExpr functions effects env operand initial result final) :
        EvalExpr functions effects env expression initial (result.bind (sumInjectionResult true target)) final
    | inK {env expression initial final index target operand result}
        (kind : expression.kind = .inK index target operand)
        (evaluated : EvalExpr functions effects env operand initial result final) :
        EvalExpr functions effects env expression initial (result.bind (injectionResult index target)) final
    | call {env expression initial middle final name arguments values result}
        (kind : expression.kind = .call name arguments)
        (argumentsEvaluated : EvalExprs functions effects env arguments initial (.value values) middle)
        (called : EvalCall functions effects name expression.ty values middle result final) :
        EvalExpr functions effects env expression initial result final
    | callFault {env expression initial final name arguments reason}
        (kind : expression.kind = .call name arguments)
        (argumentsEvaluated : EvalExprs functions effects env arguments initial (.fault reason) final) :
        EvalExpr functions effects env expression initial (.fault reason) final
    | ifTrue {env expression initial middle final target condition yes no value result}
        (kind : expression.kind = .ifThen target condition yes no)
        (tested : EvalExpr functions effects env condition initial (.value value) middle)
        (truth : condition? value = some true)
        (selected : EvalExpr functions effects env yes middle result final) :
        EvalExpr functions effects env expression initial result final
    | ifFalse {env expression initial middle final target condition yes no value result}
        (kind : expression.kind = .ifThen target condition yes no)
        (tested : EvalExpr functions effects env condition initial (.value value) middle)
        (truth : condition? value = some false)
        (selected : EvalExpr functions effects env no middle result final) :
        EvalExpr functions effects env expression initial result final
    | ifFault {env expression initial final target condition yes no reason}
        (kind : expression.kind = .ifThen target condition yes no)
        (tested : EvalExpr functions effects env condition initial (.fault reason) final) :
        EvalExpr functions effects env expression initial (.fault reason) final
    | ifInvalid {env expression initial final target condition yes no value}
        (kind : expression.kind = .ifThen target condition yes no)
        (tested : EvalExpr functions effects env condition initial (.value value) final)
        (invalid : condition? value = none) :
        EvalExpr functions effects env expression initial (.fault (.invalidValue "condition")) final

  inductive EvalExprs {σ : Type} (functions : List Function) (effects : ExternalSemantics σ) :
      Environment → List Expr → State σ → Result (List Value) → State σ → Prop where
    | nil {env state} : EvalExprs functions effects env [] state (.value []) state
    | cons {env expression rest initial middle final value values}
        (head : EvalExpr functions effects env expression initial (.value value) middle)
        (tail : EvalExprs functions effects env rest middle values final) :
        EvalExprs functions effects env (expression :: rest) initial (values.map (value :: ·)) final
    | fault {env expression rest initial final reason}
        (head : EvalExpr functions effects env expression initial (.fault reason) final) :
        EvalExprs functions effects env (expression :: rest) initial (.fault reason) final

  inductive EvalCall {σ : Type} (functions : List Function) (effects : ExternalSemantics σ) :
      String → Ty → List Value → State σ → Result Value → State σ → Prop where
    | function {name type arguments initial final function result}
        (selected : functions.find? (·.name == name) = some function)
        (called : EvalFunction functions effects function arguments initial result final) :
        EvalCall functions effects name type arguments initial result final
    | primitive {name type arguments state result}
        (notFunction : functions.find? (·.name == name) = none)
        (computed : primitive? name type arguments = some result) :
        EvalCall functions effects name type arguments state result state
    | external {name type arguments state result external}
        (notFunction : functions.find? (·.name == name) = none)
        (notPrimitive : primitive? name type arguments = none)
        (called : effects.builtin name type arguments state.external result external) :
        EvalCall functions effects name type arguments state result {state with external := external}

  inductive EvalFunction {σ : Type} (functions : List Function) (effects : ExternalSemantics σ) :
      Function → List Value → State σ → Result Value → State σ → Prop where
    | body {function arguments initial allocated final env control}
        (bound : bindArguments function.args arguments [] initial = some (env, allocated))
        (executed : EvalStatements functions effects env function.body allocated control final) :
        EvalFunction functions effects function arguments initial (finishFunction function.ret control) final
    | arity {function arguments state}
        (mismatch : bindArguments function.args arguments [] state = none) :
        EvalFunction functions effects function arguments state (.fault .arityMismatch) state

  inductive EvalStmt {σ : Type} (functions : List Function) (effects : ExternalSemantics σ) :
      Environment → Stmt → State σ → Control → State σ → Prop where
    | declare {env statement initial name type value}
        (kind : statement.kind = .letDecl name type) (zero : zero? type = some value) :
        EvalStmt functions effects env statement initial .fallthrough (allocate initial value).2
    | declareInvalid {env statement initial name type}
        (kind : statement.kind = .letDecl name type) (zero : zero? type = none) :
        EvalStmt functions effects env statement initial (.fault .unsupportedType) initial
    | assign {env statement lhs rhs initial middle final value}
        (kind : statement.kind = .assign lhs rhs)
        (evaluated : EvalExpr functions effects env rhs initial (.value value) middle)
        (written : assignResult env middle lhs value = .value final) :
        EvalStmt functions effects env statement initial .fallthrough final
    | assignFault {env statement lhs rhs initial final reason}
        (kind : statement.kind = .assign lhs rhs)
        (evaluated : EvalExpr functions effects env rhs initial (.fault reason) final) :
        EvalStmt functions effects env statement initial (.fault reason) final
    | assignInvalid {env statement lhs rhs initial middle value reason}
        (kind : statement.kind = .assign lhs rhs)
        (evaluated : EvalExpr functions effects env rhs initial (.value value) middle)
        (invalid : assignResult env middle lhs value = .fault reason) :
        EvalStmt functions effects env statement initial (.fault reason) middle
    | expression {env statement expression initial final value}
        (kind : statement.kind = .expression expression)
        (evaluated : EvalExpr functions effects env expression initial (.value value) final) :
        EvalStmt functions effects env statement initial .fallthrough final
    | expressionFault {env statement expression initial final reason}
        (kind : statement.kind = .expression expression)
        (evaluated : EvalExpr functions effects env expression initial (.fault reason) final) :
        EvalStmt functions effects env statement initial (.fault reason) final
    | returned {env statement expression initial final value}
        (kind : statement.kind = .returnStmt expression)
        (evaluated : EvalExpr functions effects env expression initial (.value value) final) :
        EvalStmt functions effects env statement initial (.returned value) final
    | returnFault {env statement expression initial final reason}
        (kind : statement.kind = .returnStmt expression)
        (evaluated : EvalExpr functions effects env expression initial (.fault reason) final) :
        EvalStmt functions effects env statement initial (.fault reason) final
    | block {env statement statements initial final control}
        (kind : statement.kind = .block statements)
        (evaluated : EvalStatements functions effects env statements initial control final) :
        EvalStmt functions effects env statement initial control final
    | forInit {env statement init condition post body initial final control}
        (kind : statement.kind = .forLoop init condition post body) (nonempty : init ≠ [])
        (evaluated : EvalStatements functions effects env
          (init ++ [⟨.forLoop [] condition post body, statement.span⟩]) initial control final) :
        EvalStmt functions effects env statement initial control final
    | forLoop {env statement condition post body initial final control}
        (kind : statement.kind = .forLoop [] condition post body)
        (evaluated : EvalLoop functions effects env condition post body initial control final) :
        EvalStmt functions effects env statement initial control final
    | breaking {env statement state} (kind : statement.kind = .breakStmt) :
        EvalStmt functions effects env statement state .breaking state
    | continuing {env statement state} (kind : statement.kind = .continueStmt) :
        EvalStmt functions effects env statement state .continuing state
    | matchStmt {env statement target expression alternatives initial middle final value control}
        (kind : statement.kind = .matchStmt target expression alternatives)
        (evaluated : EvalExpr functions effects env expression initial (.value value) middle)
        (selected : EvalAlternatives functions effects env target value alternatives middle control final) :
        EvalStmt functions effects env statement initial control final
    | matchFault {env statement target expression alternatives initial final reason}
        (kind : statement.kind = .matchStmt target expression alternatives)
        (evaluated : EvalExpr functions effects env expression initial (.fault reason) final) :
        EvalStmt functions effects env statement initial (.fault reason) final
    | assembly {env statement body initial final control} (kind : statement.kind = .assembly body)
        (executed : effects.assembly functions env body initial control final) :
        EvalStmt functions effects env statement initial control final
    | revert {env statement message state external control} (kind : statement.kind = .revert message)
        (executed : effects.revert message state.external control external) :
        EvalStmt functions effects env statement state control {state with external := external}
    | comment {env statement text state} (kind : statement.kind = .comment text) :
        EvalStmt functions effects env statement state .fallthrough state

  inductive EvalStatements {σ : Type} (functions : List Function) (effects : ExternalSemantics σ) :
      Environment → List Stmt → State σ → Control → State σ → Prop where
    | nil {env state} : EvalStatements functions effects env [] state .fallthrough state
    | declare {env statement rest name type value initial final control}
        (kind : statement.kind = .letDecl name type) (zero : zero? type = some value)
        (tail : EvalStatements functions effects ((name, initial.heap.length) :: env)
          rest (allocate initial value).2 control final) :
        EvalStatements functions effects env (statement :: rest) initial control final
    | declareInvalid {env statement rest name type state}
        (kind : statement.kind = .letDecl name type) (zero : zero? type = none) :
        EvalStatements functions effects env (statement :: rest) state (.fault .unsupportedType) state
    | next {env statement rest initial middle final control}
        (notDeclaration : ∀ name type, statement.kind ≠ .letDecl name type)
        (head : EvalStmt functions effects env statement initial .fallthrough middle)
        (tail : EvalStatements functions effects env rest middle control final) :
        EvalStatements functions effects env (statement :: rest) initial control final
    | stop {env statement rest initial final control}
        (notDeclaration : ∀ name type, statement.kind ≠ .letDecl name type)
        (head : EvalStmt functions effects env statement initial control final)
        (stopped : control ≠ .fallthrough) :
        EvalStatements functions effects env (statement :: rest) initial control final

  inductive EvalLoop {σ : Type} (functions : List Function) (effects : ExternalSemantics σ) :
      Environment → Expr → List Stmt → List Stmt → State σ → Control → State σ → Prop where
    | done {env condition post body initial final value}
        (tested : EvalExpr functions effects env condition initial (.value value) final)
        (truth : condition? value = some false) :
        EvalLoop functions effects env condition post body initial .fallthrough final
    | conditionFault {env condition post body initial final reason}
        (tested : EvalExpr functions effects env condition initial (.fault reason) final) :
        EvalLoop functions effects env condition post body initial (.fault reason) final
    | conditionInvalid {env condition post body initial final value}
        (tested : EvalExpr functions effects env condition initial (.value value) final)
        (invalid : condition? value = none) :
        EvalLoop functions effects env condition post body initial (.fault (.invalidValue "condition")) final
    | step {env condition post body initial testedState bodyState postState final value bodyControl postControl control}
        (tested : EvalExpr functions effects env condition initial (.value value) testedState)
        (truth : condition? value = some true)
        (bodyEvaluated : EvalStatements functions effects env body testedState bodyControl bodyState)
        (bodyContinues : bodyControl = .fallthrough ∨ bodyControl = .continuing)
        (postEvaluated : EvalStatements functions effects env post bodyState postControl postState)
        (postContinues : postControl = .fallthrough ∨ postControl = .continuing)
        (next : EvalLoop functions effects env condition post body postState control final) :
        EvalLoop functions effects env condition post body initial control final
    | bodyBreak {env condition post body initial testedState final value}
        (tested : EvalExpr functions effects env condition initial (.value value) testedState)
        (truth : condition? value = some true)
        (bodyEvaluated : EvalStatements functions effects env body testedState .breaking final) :
        EvalLoop functions effects env condition post body initial .fallthrough final
    | bodyStop {env condition post body initial testedState final value control}
        (tested : EvalExpr functions effects env condition initial (.value value) testedState)
        (truth : condition? value = some true)
        (bodyEvaluated : EvalStatements functions effects env body testedState control final)
        (stops : (∃ value, control = .returned value) ∨ (∃ reason, control = .fault reason)) :
        EvalLoop functions effects env condition post body initial control final
    | postBreak {env condition post body initial testedState bodyState final value bodyControl}
        (tested : EvalExpr functions effects env condition initial (.value value) testedState)
        (truth : condition? value = some true)
        (bodyEvaluated : EvalStatements functions effects env body testedState bodyControl bodyState)
        (bodyContinues : bodyControl = .fallthrough ∨ bodyControl = .continuing)
        (postEvaluated : EvalStatements functions effects env post bodyState .breaking final) :
        EvalLoop functions effects env condition post body initial .fallthrough final
    | postStop {env condition post body initial testedState bodyState final value bodyControl control}
        (tested : EvalExpr functions effects env condition initial (.value value) testedState)
        (truth : condition? value = some true)
        (bodyEvaluated : EvalStatements functions effects env body testedState bodyControl bodyState)
        (bodyContinues : bodyControl = .fallthrough ∨ bodyControl = .continuing)
        (postEvaluated : EvalStatements functions effects env post bodyState control final)
        (stops : (∃ value, control = .returned value) ∨ (∃ reason, control = .fault reason)) :
        EvalLoop functions effects env condition post body initial control final

  inductive EvalAlternatives {σ : Type} (functions : List Function) (effects : ExternalSemantics σ) :
      Environment → Ty → Value → List Alt → State σ → Control → State σ → Prop where
    | nil {env target value state} :
        EvalAlternatives functions effects env target value [] state .fallthrough state
    | matched {env target value alternative rest initial final payload control}
        (matched : patternPayload? target alternative.pat.kind value = some payload)
        (executed : EvalStatements functions effects ((alternative.binder, initial.heap.length) :: env)
          alternative.body (allocate initial payload).2 control final) :
        EvalAlternatives functions effects env target value (alternative :: rest) initial control final
    | next {env target value alternative rest initial final control}
        (notMatched : patternPayload? target alternative.pat.kind value = none)
        (executed : EvalAlternatives functions effects env target value rest initial control final) :
        EvalAlternatives functions effects env target value (alternative :: rest) initial control final
end

end Solcore.Frontend.RustHull.Semantics
