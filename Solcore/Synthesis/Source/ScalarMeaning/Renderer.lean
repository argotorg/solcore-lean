import Solcore.Core.Eval
import Solcore.Synthesis.Core.WordFunctionDAG
import Solcore.Synthesis.Source.ScalarMeaning.Frames
import Solcore.Synthesis.Source.ScalarMeaning.RendererEquations

/-! Meaning preservation for the actual scalar renderer. For every Core
expression admitted by the synthesis fragment and rendered successfully, the
renderer's lines are the printing of source statements. Executing those
statements under the independent source semantics yields the value that Core's
big-step evaluation yields, binds it to the rendered value name, allocates only
the rendered temporaries and leaves every other binding unchanged. Calls to
earlier helpers are related to the Core closures that follow the Word locals
in the environment. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.ScalarMeaning

open Solcore.Synthesis.Core (Target acceptsAt functionAcceptsAt)
open Solcore.Synthesis.Source.ScalarRenderer (Rendered)

abbrev CoreExpr := Solcore.Core.Wire.Expr
abbrev CoreValue := Solcore.Core.Value

/-- Representation of a Core value of a fragment type by a source value. -/
def Represents : Target → CoreValue → Value → Prop
  | .word, core, source => ∃ word : Solcore.Core.Word, core = .word word ∧ source = .word word.val
  | .bool, core, source => ∃ flag : Bool, core = .bool flag ∧ source = .bool flag

/-- `name` is not a temporary numbered `next` or later. -/
def OlderThan (next : Nat) (name : String) : Prop :=
  ∀ index, name = temporary index → index < next

/-- `name` is one of the temporaries numbered in `[first, last)`. -/
def AllocatedIn (first last : Nat) (name : String) : Prop :=
  ∃ index, name = temporary index ∧ first ≤ index ∧ index < last

/-- Core's de Bruijn environment and the source frames agree on every rendered
local name (nearest binder first). -/
def LocalsAgree (frames : Frames) (locals : List String)
    (environment : Solcore.Core.Environment) : Prop :=
  ∀ (index : Nat) (name : String), locals[index]? = some name →
    ∃ word : Solcore.Core.Word,
      environment[index]? = some (Solcore.Core.Value.word word) ∧
        frames.lookup name = some (.word word.val)

/-- Each rendered helper name denotes, in the source call context, the Word
function of the corresponding Core closure (nearest helper first). -/
def FunctionsAgree (context : Context) (functions : List String)
    (closures : List CoreValue) : Prop :=
  ∀ (index : Nat) (name : String), functions[index]? = some name →
    ∃ (parameterType resultType : Solcore.Core.Ty) (body : Solcore.Core.Expr)
      (captured : Solcore.Core.Environment),
      closures[index]? = some (.closure parameterType resultType body captured) ∧
      ∀ (argument : Solcore.Core.Word) (store : Solcore.Core.Store),
        ∃ result : Solcore.Core.Word,
          Solcore.Core.Evaluates (.word argument :: captured) store body (.word result) store ∧
          context.call name [.word argument.val] = some (.word result.val)

/-- Executing `statements` from frames that agree with a Core environment
evaluates `expression` in that environment. The environment holds the Word
locals followed by the helper closures. Only temporaries in `[first, last)`
are declared (in the innermost scope) or changed. -/
def Simulates (expression : CoreExpr) (target : Target) (functions locals : List String)
    (first last : Nat) (statements : List Stmt) (valueName : String) : Prop :=
  ∀ (context : Context) (environment : Solcore.Core.Environment) (store : Solcore.Core.Store)
    (scope : Scope) (outer : Frames),
    LocalsAgree (scope :: outer) locals environment →
    locals.length ≤ environment.length →
    FunctionsAgree context functions (environment.drop locals.length) →
    ∃ (coreValue : CoreValue) (value : Value) (scope' : Scope) (outer' : Frames)
      (added : List String),
      Solcore.Core.Evaluates environment store expression.toCore coreValue store ∧
      Represents target coreValue value ∧
      Stmt.execList context (scope :: outer) statements = some (scope' :: outer') ∧
      Frames.lookup (scope' :: outer') valueName = some value ∧
      (∀ name, ¬ AllocatedIn first last name →
        Frames.lookup (scope' :: outer') name = Frames.lookup (scope :: outer) name) ∧
      Frames.shape outer' = Frames.shape outer ∧
      scope'.names = added ++ scope.names ∧
      (∀ name ∈ added, AllocatedIn first last name)

/-- What the renderer establishes for one rendered expression. -/
def RenderSpec (expression : CoreExpr) (target : Target) (functions locals : List String)
    (indent first : Nat) (rendered : Rendered) : Prop :=
  ∃ statements : List Stmt,
    rendered.lines = Stmt.listLines indent statements ∧
    first ≤ rendered.nextId ∧
    (rendered.value ∈ locals ∨ AllocatedIn first rendered.nextId rendered.value) ∧
    (∀ name ∈ Stmt.listIdentifiers statements,
      name ∈ locals ∨ name ∈ functions ∨ AllocatedIn first rendered.nextId name) ∧
    Simulates expression target functions locals first rendered.nextId statements
      rendered.value

def RenderIH (expression : CoreExpr) : Prop :=
  ∀ (functions : List String) (depth prior : Nat) (target : Target) (locals : List String)
    (indent first : Nat) (rendered : Rendered),
    functionAcceptsAt depth prior target expression = true →
    ScalarRenderer.renderWithFunctions functions target locals indent first expression =
      .ok rendered →
    (∀ name ∈ locals, OlderThan first name) →
    RenderSpec expression target functions locals indent first rendered

/-! ### Auxiliary facts -/

theorem except_bind_eq_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (equation : x.bind f = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error error => simp [Except.bind] at equation
  | ok a => exact ⟨a, rfl, equation⟩

theorem target_beq_iff {first second : Target} : (first == second) = true ↔ first = second := by
  cases first <;> cases second <;> decide

theorem word_lt_modulus (word : Solcore.Core.Word) : word.val < Evm.modulus :=
  word.isLt

theorem older_mono {first second : Nat} {name : String} (older : OlderThan first name)
    (le : first ≤ second) : OlderThan second name :=
  fun index same => Nat.lt_of_lt_of_le (older index same) le

theorem temporary_older (index : Nat) : OlderThan (index + 1) (temporary index) := by
  intro other same
  have := temporary_injective same
  omega

theorem allocated_temporary {first last index : Nat} (low : first ≤ index) (high : index < last) :
    AllocatedIn first last (temporary index) :=
  ⟨index, rfl, low, high⟩

theorem allocated_mono {first last first' last' : Nat} {name : String}
    (allocated : AllocatedIn first last name) (low : first' ≤ first) (high : last ≤ last') :
    AllocatedIn first' last' name := by
  obtain ⟨index, rfl, lower, upper⟩ := allocated
  exact ⟨index, rfl, by omega, by omega⟩

theorem not_allocated_of_older {start first last : Nat} {name : String}
    (older : OlderThan start name) (le : start ≤ first) : ¬ AllocatedIn first last name := by
  rintro ⟨index, rfl, lower, _⟩
  have := older index rfl
  omega

theorem not_allocated_of_allocated {first last first' last' : Nat} {name : String}
    (allocated : AllocatedIn first last name) (disjoint : last ≤ first' ∨ last' ≤ first) :
    ¬ AllocatedIn first' last' name := by
  rintro ⟨index, rfl, lower, upper⟩
  obtain ⟨other, same, lower', upper'⟩ := allocated
  have := temporary_injective same
  omega

theorem temporary_not_allocated {first last index : Nat} (outside : index < first ∨ last ≤ index) :
    ¬ AllocatedIn first last (temporary index) := by
  rintro ⟨other, same, lower, upper⟩
  have := temporary_injective same
  omega

/-- A value name that is a local or was allocated before `middle` is not
allocated again in `[middle, last)`. -/
theorem value_not_reallocated {locals : List String} {first middle last : Nat} {name : String}
    (fresh : ∀ local_ ∈ locals, OlderThan first local_) (le : first ≤ middle)
    (classified : name ∈ locals ∨ AllocatedIn first middle name) :
    ¬ AllocatedIn middle last name := by
  rcases classified with mem | allocated
  · exact not_allocated_of_older (fresh name mem) le
  · exact not_allocated_of_allocated allocated (Or.inl (Nat.le_refl middle))

theorem LocalsAgree.transfer {frames frames' : Frames} {locals : List String}
    {environment : Solcore.Core.Environment} (agree : LocalsAgree frames locals environment)
    (same : ∀ name ∈ locals, frames'.lookup name = frames.lookup name) :
    LocalsAgree frames' locals environment := by
  unfold LocalsAgree at agree ⊢
  intro index name found
  obtain ⟨word, inEnvironment, lookup⟩ := agree index name found
  exact ⟨word, inEnvironment, (same name (List.mem_of_getElem? found)).trans lookup⟩

theorem Represents.admits {target : Target} {core : CoreValue} {source : Value}
    (represents : Represents target core source) :
    (LocalType.ofTarget target).admits source = true := by
  cases target
  · obtain ⟨_, _, rfl⟩ := represents
    rfl
  · obtain ⟨_, _, rfl⟩ := represents
    rfl

theorem Represents.sameType {target : Target} {core core' : CoreValue} {source source' : Value}
    (represents : Represents target core source) (represents' : Represents target core' source') :
    source.sameType source' = true := by
  cases target
  · obtain ⟨_, _, rfl⟩ := represents
    obtain ⟨_, _, rfl⟩ := represents'
    rfl
  · obtain ⟨_, _, rfl⟩ := represents
    obtain ⟨_, _, rfl⟩ := represents'
    rfl

/-- The zero value printed for an `if` result. -/
def zeroValue : Target → Value
  | .word => .word 0
  | .bool => .bool false

theorem zeroExpr_eval (context : Context) (frames : Frames) (target : Target) :
    (zeroExpr target).eval context frames = some (zeroValue target) := by
  cases target
  · simp [zeroExpr, zeroValue, Expr.eval, Evm.modulus]
  · rfl

theorem zeroValue_admits (target : Target) :
    (LocalType.ofTarget target).admits (zeroValue target) = true := by
  cases target <;> rfl

theorem Represents.sameType_zero {target : Target} {core : CoreValue} {source : Value}
    (represents : Represents target core source) : source.sameType (zeroValue target) = true := by
  cases target
  · obtain ⟨_, _, rfl⟩ := represents
    rfl
  · obtain ⟨_, _, rfl⟩ := represents
    rfl

theorem zeroExpr_print (target : Target) : (zeroExpr target).print = zeroText target := by
  cases target <;> rfl

/-! ### Core Word operations and the source EVM operations -/

theorem evm_add (left right : Solcore.Core.Word) :
    Evm.add left.val right.val = (left.add right).val := by
  simp [Evm.add, Evm.modulus, Solcore.Core.Word.add, Fin.val_add, Solcore.Core.wordModulus]

theorem evm_sub (left right : Solcore.Core.Word) :
    Evm.sub left.val right.val = (left.sub right).val := by
  have bound := right.isLt
  simp only [Solcore.Core.wordModulus] at bound
  simp only [Evm.sub, Evm.modulus, Solcore.Core.Word.sub, Fin.sub_def,
    Solcore.Core.wordModulus]
  congr 1
  omega

theorem evm_mul (left right : Solcore.Core.Word) :
    Evm.mul left.val right.val = (left.mul right).val := by
  simp [Evm.mul, Evm.modulus, Solcore.Core.Word.mul, Fin.val_mul, Solcore.Core.wordModulus]

theorem evm_and (left right : Solcore.Core.Word) :
    Evm.and left.val right.val = (left.bitAnd right).val := by
  simp [Evm.and, Solcore.Core.Word.bitAnd]

theorem evm_or (left right : Solcore.Core.Word) :
    Evm.or left.val right.val = (left.bitOr right).val := by
  have leftBound := left.isLt
  have rightBound := right.isLt
  simp only [Solcore.Core.wordModulus] at leftBound rightBound
  simp only [Evm.or, Solcore.Core.Word.bitOr, Fin.or_val, Solcore.Core.wordModulus]
  exact (Nat.mod_eq_of_lt (Nat.or_lt_two_pow leftBound rightBound)).symm

theorem evm_xor (left right : Solcore.Core.Word) :
    Evm.xor left.val right.val = (left.bitXor right).val := by
  have leftBound := left.isLt
  have rightBound := right.isLt
  simp only [Solcore.Core.wordModulus] at leftBound rightBound
  simp only [Evm.xor, Solcore.Core.Word.bitXor, Fin.xor_val, Solcore.Core.wordModulus]
  exact (Nat.mod_eq_of_lt (Nat.xor_lt_two_pow leftBound rightBound)).symm

theorem evm_not (value : Solcore.Core.Word) :
    Evm.not value.val = value.bitNot.val := by
  have bound := value.isLt
  simp only [Solcore.Core.wordModulus] at bound
  have le : value ≤ Solcore.Core.Word.maximum := by
    show value.val ≤ Solcore.Core.wordModulus - 1
    simp only [Solcore.Core.wordModulus]
    omega
  rw [Solcore.Core.Word.bitNot, Fin.sub_val_of_le le]
  rfl

theorem evm_eq (left right : Solcore.Core.Word) :
    toBool (Evm.eq left.val right.val) = (left == right) := by
  by_cases same : left = right
  · subst same
    simp [toBool, Evm.eq]
  · have values : left.val ≠ right.val := fun equal => same (Fin.ext equal)
    simp [toBool, Evm.eq, values, same]

theorem evm_gt (left right : Solcore.Core.Word) :
    toBool (Evm.gt left.val right.val) = decide (left > right) := by
  by_cases greater : right.val < left.val
  · have : left > right := greater
    simp [toBool, Evm.gt, greater, this]
  · have : ¬ left > right := greater
    simp [toBool, Evm.gt, greater, this]

theorem unary_agree {op : Solcore.Core.Wire.UnaryOp} {sourceOp : UnaryOp}
    (selected : sourceUnary? op = some sourceOp) {core : CoreValue} {source : Value}
    (operand : Represents (if op == .boolNot then .bool else .word) core source) :
    ∃ coreResult sourceResult,
      Solcore.Core.UnaryOp.apply op.toCore core = some coreResult ∧
      sourceOp.apply source = some sourceResult ∧
      Represents (Target.unaryResult op) coreResult sourceResult := by
  cases op <;> simp only [sourceUnary?, reduceCtorEq, Option.some.injEq] at selected
  · subst selected
    obtain ⟨flag, rfl, rfl⟩ := operand
    exact ⟨.bool (!flag), .bool (!flag), rfl, rfl, ⟨!flag, rfl, rfl⟩⟩
  · subst selected
    obtain ⟨word, rfl, rfl⟩ := operand
    exact ⟨.word word.bitNot, .word (Evm.not word.val), rfl, rfl,
      ⟨word.bitNot, rfl, by rw [evm_not]⟩⟩

theorem binary_agree {op : Solcore.Core.Wire.BinaryOp} {sourceOp : BinaryOp}
    (selected : sourceBinary? op = some sourceOp) (left right : Solcore.Core.Word) :
    ∃ coreResult sourceResult,
      Solcore.Core.BinaryOp.apply op.toCore (.word left) (.word right) = some coreResult ∧
      sourceOp.apply (.word left.val) (.word right.val) = some sourceResult ∧
      Represents (Target.binaryResult op) coreResult sourceResult := by
  cases op <;> simp only [sourceBinary?, reduceCtorEq, Option.some.injEq] at selected <;>
    subst selected
  · exact ⟨_, _, rfl, rfl, ⟨left.add right, rfl, by rw [evm_add]⟩⟩
  · exact ⟨_, _, rfl, rfl, ⟨left.sub right, rfl, by rw [evm_sub]⟩⟩
  · exact ⟨_, _, rfl, rfl, ⟨left.mul right, rfl, by rw [evm_mul]⟩⟩
  · exact ⟨_, _, rfl, rfl, ⟨left == right, rfl, by rw [evm_eq]⟩⟩
  · exact ⟨_, _, rfl, rfl, ⟨decide (left > right), rfl, by rw [evm_gt]⟩⟩
  · exact ⟨_, _, rfl, rfl, ⟨left.bitAnd right, rfl, by rw [evm_and]⟩⟩
  · exact ⟨_, _, rfl, rfl, ⟨left.bitOr right, rfl, by rw [evm_or]⟩⟩
  · exact ⟨_, _, rfl, rfl, ⟨left.bitXor right, rfl, by rw [evm_xor]⟩⟩

theorem acceptsAt_unary {depth prior : Nat} {target : Target}
    {op : Solcore.Core.Wire.UnaryOp} {sourceOp : UnaryOp} {operand : CoreExpr}
    (selected : sourceUnary? op = some sourceOp)
    (accepted : functionAcceptsAt depth prior target (.unary op operand) = true) :
    target = Target.unaryResult op ∧
      functionAcceptsAt depth prior (if op == .boolNot then .bool else .word) operand = true := by
  cases op <;> simp only [sourceUnary?, reduceCtorEq] at selected <;>
    simp only [functionAcceptsAt, Bool.and_eq_true, target_beq_iff] at accepted <;>
    exact accepted

theorem acceptsAt_binary {depth prior : Nat} {target : Target}
    {op : Solcore.Core.Wire.BinaryOp} {sourceOp : BinaryOp} {left right : CoreExpr}
    (selected : sourceBinary? op = some sourceOp)
    (accepted : functionAcceptsAt depth prior target (.binary op left right) = true) :
    target = Target.binaryResult op ∧ functionAcceptsAt depth prior .word left = true ∧
      functionAcceptsAt depth prior .word right = true := by
  cases op <;> simp only [sourceBinary?, reduceCtorEq] at selected <;>
    simp only [functionAcceptsAt, Bool.and_eq_true, target_beq_iff] at accepted <;>
    exact ⟨accepted.1.1, accepted.1.2, accepted.2⟩

/-- The closed synthesis fragment is the helper-free case of the function
fragment. -/
theorem acceptsAt_functionAcceptsAt : (expression : CoreExpr) → ∀ {depth : Nat} {target : Target}
    (prior : Nat), acceptsAt depth target expression = true →
    functionAcceptsAt depth prior target expression = true
  | .word _, _, _, _, accepted => by simpa [acceptsAt, functionAcceptsAt] using accepted
  | .bool _, _, _, _, accepted => by simpa [acceptsAt, functionAcceptsAt] using accepted
  | .var _, _, _, _, accepted => by simpa [acceptsAt, functionAcceptsAt] using accepted
  | .letE initializer body, _, _, prior, accepted => by
      simp only [acceptsAt, functionAcceptsAt, Bool.and_eq_true] at accepted ⊢
      exact ⟨acceptsAt_functionAcceptsAt initializer prior accepted.1,
        acceptsAt_functionAcceptsAt body prior accepted.2⟩
  | .ifE condition yes no, _, _, prior, accepted => by
      simp only [acceptsAt, functionAcceptsAt, Bool.and_eq_true] at accepted ⊢
      exact ⟨⟨acceptsAt_functionAcceptsAt condition prior accepted.1.1,
        acceptsAt_functionAcceptsAt yes prior accepted.1.2⟩,
        acceptsAt_functionAcceptsAt no prior accepted.2⟩
  | .unary op operand, _, _, prior, accepted => by
      cases op <;> simp only [acceptsAt, functionAcceptsAt, Bool.and_eq_true] at accepted ⊢ <;>
        first
        | exact accepted
        | exact ⟨accepted.1, acceptsAt_functionAcceptsAt operand prior accepted.2⟩
  | .binary op left right, _, _, prior, accepted => by
      cases op <;> simp only [acceptsAt, functionAcceptsAt, Bool.and_eq_true] at accepted ⊢ <;>
        first
        | exact accepted
        | exact ⟨⟨accepted.1.1, acceptsAt_functionAcceptsAt left prior accepted.1.2⟩,
            acceptsAt_functionAcceptsAt right prior accepted.2⟩
  | .ternary _ first second third, _, _, prior, accepted => by
      simp only [acceptsAt, functionAcceptsAt, Bool.and_eq_true] at accepted ⊢
      exact ⟨⟨⟨accepted.1.1.1, acceptsAt_functionAcceptsAt first prior accepted.1.1.2⟩,
        acceptsAt_functionAcceptsAt second prior accepted.1.2⟩,
        acceptsAt_functionAcceptsAt third prior accepted.2⟩
  | .unit, _, _, _, accepted => by simp [acceptsAt] at accepted
  | .integer _, _, _, _, accepted => by simp [acceptsAt] at accepted
  | .pair _ _, _, _, _, accepted => by simp [acceptsAt] at accepted
  | .first _, _, _, _, accepted => by simp [acceptsAt] at accepted
  | .second _, _, _, _, accepted => by simp [acceptsAt] at accepted
  | .lambda _ _ _, _, _, _, accepted => by simp [acceptsAt] at accepted
  | .apply _ _, _, _, _, accepted => by simp [acceptsAt] at accepted
  | .inLeft _ _, _, _, _, accepted => by simp [acceptsAt] at accepted
  | .inRight _ _, _, _, _, accepted => by simp [acceptsAt] at accepted
  | .caseE _ _ _, _, _, _, accepted => by simp [acceptsAt] at accepted
  | .newCell _ _, _, _, _, accepted => by simp [acceptsAt] at accepted
  | .loadCell _, _, _, _, accepted => by simp [acceptsAt] at accepted
  | .storeCell _ _, _, _, _, accepted => by simp [acceptsAt] at accepted
  | .construct _ _, _, _, _, accepted => by simp [acceptsAt] at accepted
  | .matchData _ _ _ _, _, _, _, accepted => by simp [acceptsAt] at accepted

end Solcore.Synthesis.Source.ScalarMeaning
