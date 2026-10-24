import Solcore.Frontend.RustHull.NamedCallCorrespondence

/-! Pointwise simulation statements for induction on a finite, independent Hull
execution derivation. No statement assumes the simulation of every execution
of a function, and no syntactic call rank is imposed. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.DerivationCorrespondence
open Correspondence ScalarExecution StatementCorrespondence PureCallCorrespondence

/-- Structural expressions and known named calls, including recursive calls.
An absent named function is accepted only for a supported pure builtin. -/
inductive RecursiveExpression (functions : List Function) : Expr → Prop where
  | word (type text span) : RecursiveExpression functions ⟨type, .word text, span⟩
  | bool (type value span) : RecursiveExpression functions ⟨type, .bool value, span⟩
  | unit (type span) : RecursiveExpression functions ⟨type, .unit, span⟩
  | var (type name span) : RecursiveExpression functions ⟨type, .var name, span⟩
  | pair {left right} (first : RecursiveExpression functions left)
      (second : RecursiveExpression functions right) (type span) :
      RecursiveExpression functions ⟨type, .pair left right, span⟩
  | fst {value} (operand : RecursiveExpression functions value) (type span) :
      RecursiveExpression functions ⟨type, .fst value, span⟩
  | snd {value} (operand : RecursiveExpression functions value) (type span) :
      RecursiveExpression functions ⟨type, .snd value, span⟩
  | inl {value} (operand : RecursiveExpression functions value) (type target span) :
      RecursiveExpression functions ⟨type, .inl target value, span⟩
  | inr {value} (operand : RecursiveExpression functions value) (type target span) :
      RecursiveExpression functions ⟨type, .inr target value, span⟩
  | inK {value} (operand : RecursiveExpression functions value) (index type target span) :
      RecursiveExpression functions ⟨type, .inK index target value, span⟩
  | conditional {test yes no} (condition : RecursiveExpression functions test)
      (yesBranch : RecursiveExpression functions yes) (noBranch : RecursiveExpression functions no)
      (type target span) : RecursiveExpression functions ⟨type, .ifThen target test yes no, span⟩
  | builtin {name arguments operation}
      (classified : pureBuiltin? name = some operation)
      (notFunction : functions.find? (·.name == name) = none)
      (argumentsEligible : ∀ argument ∈ arguments, RecursiveExpression functions argument)
      (type span) : RecursiveExpression functions ⟨type, .call name arguments, span⟩
  | named {name arguments function}
      (selected : functions.find? (·.name == name) = some function)
      (argumentsEligible : ∀ argument ∈ arguments, RecursiveExpression functions argument)
      (type span) : RecursiveExpression functions ⟨type, .call name arguments, span⟩

/-- The current statement fragment permits local declarations, direct local
assignment, expression statements and return. Recursion occurs in expressions. -/
def RecursiveStatement (functions : List Function) (statement : Stmt) : Prop :=
  match statement.kind with
  | .letDecl _ _ | .comment _ => True
  | .assign ⟨_, .var _, _⟩ value | .expression value | .returnStmt value =>
      RecursiveExpression functions value
  | _ => False

def RecursiveProgram (functions : List Function) : Prop :=
  ∀ function ∈ functions, ∀ statement ∈ function.body, RecursiveStatement functions statement

/-- The actual source result is an index. A fault branch has no normal-result
obligation; normal branches must preserve the exact emitted Core expression. -/
def ExprSimulation {σ : Type} (signatures : List Signature)
    (codes : List GlobalCode) (locations : Nat → Nat) (captured : Core.Environment)
    (sourceEnvironment : Semantics.Environment) (expression : Expr)
    (initial : Semantics.State σ) (result : Semantics.Result Semantics.Value) (final : Semantics.State σ) : Prop :=
  ∀ {sourceValue}, result = .value sourceValue →
    ∀ {fuel scope lowered}, lowerExpression fuel signatures scope expression = .ok lowered →
    ∀ {world mapping environment store},
      EnvironmentRel world sourceEnvironment scope mapping environment →
      GlobalEnvironmentRel codes locations scope mapping environment →
      HeapRel world initial.heap store → InstalledGlobals codes locations captured store →
      ∃ extension targetValue finalStore,
        ValueRel lowered.type sourceValue targetValue ∧
        Core.Evaluates environment store (lowered.expression.rename mapping)
          (.inRight .word targetValue) finalStore ∧
        HeapRel (world ++ extension) final.heap finalStore ∧ InstalledGlobals codes locations captured finalStore

def ExprsSimulation {σ : Type} (signatures : List Signature)
    (codes : List GlobalCode) (locations : Nat → Nat) (captured : Core.Environment)
    (sourceEnvironment : Semantics.Environment) (expressions : List Expr)
    (initial : Semantics.State σ) (result : Semantics.Result (List Semantics.Value))
    (final : Semantics.State σ) : Prop :=
  ∀ {sources}, result = .value sources →
    ∀ {fuel scope arguments}, expressions.mapM (lowerExpression fuel signatures scope) = .ok arguments →
    ∀ {world mapping environment store},
      EnvironmentRel world sourceEnvironment scope mapping environment →
      GlobalEnvironmentRel codes locations scope mapping environment →
      HeapRel world initial.heap store → InstalledGlobals codes locations captured store →
      ∃ extension targets finalStore,
        ArgumentsRel arguments sources targets ∧
        Core.Evaluates environment store ((packArguments arguments).expression.rename mapping)
          (.inRight .word (bundleValues targets)) finalStore ∧
        HeapRel (world ++ extension) final.heap finalStore ∧ InstalledGlobals codes locations captured finalStore

def StmtSimulation {σ : Type} (signatures : List Signature)
    (codes : List GlobalCode) (locations : Nat → Nat) (captured : Core.Environment)
    (sourceEnvironment : Semantics.Environment) (statement : Stmt)
    (initial : Semantics.State σ) (control : Semantics.Control) (final : Semantics.State σ) : Prop :=
  NormalControl control →
    ∀ {fuel scope result loops expression}, lowerStatement fuel signatures scope result loops statement = .ok expression →
    ∀ {world mapping environment store},
      EnvironmentRel world sourceEnvironment scope mapping environment →
      GlobalEnvironmentRel codes locations scope mapping environment →
      HeapRel world initial.heap store → InstalledGlobals codes locations captured store →
      ∃ extension targetValue finalStore,
        ControlRel result control targetValue ∧
        Core.Evaluates environment store (expression.rename mapping) targetValue finalStore ∧
        HeapRel (world ++ extension) final.heap finalStore ∧ InstalledGlobals codes locations captured finalStore

def StatementsSimulation {σ : Type} (signatures : List Signature)
    (codes : List GlobalCode) (locations : Nat → Nat) (captured : Core.Environment)
    (sourceEnvironment : Semantics.Environment) (statements : List Stmt)
    (initial : Semantics.State σ) (control : Semantics.Control) (final : Semantics.State σ) : Prop :=
  NormalControl control →
    ∀ {fuel scope result loops expression}, lowerStatements fuel signatures scope result loops statements = .ok expression →
    ∀ {world mapping environment store},
      EnvironmentRel world sourceEnvironment scope mapping environment →
      GlobalEnvironmentRel codes locations scope mapping environment →
      HeapRel world initial.heap store → InstalledGlobals codes locations captured store →
      ∃ extension targetValue finalStore,
        ControlRel result control targetValue ∧
        Core.Evaluates environment store (expression.rename mapping) targetValue finalStore ∧
        HeapRel (world ++ extension) final.heap finalStore ∧ InstalledGlobals codes locations captured finalStore

/-- The exact closure body installed at a real global slot. The source function
is tracked by the mutual induction motive and its compiler lookup premises. -/
def FunctionSimulation {σ : Type} (codes : List GlobalCode) (locations : Nat → Nat)
    (captured : Core.Environment) (code : GlobalCode) (index : Nat)
    (sources : List Semantics.Value) (initial : Semantics.State σ)
    (result : Semantics.Result Semantics.Value) (final : Semantics.State σ) : Prop :=
  ∀ {source}, result = .value source →
    ∀ {targets}, ValuesRel code.own.parameters sources targets →
    ∀ {world store}, HeapRel world initial.heap store → InstalledGlobals codes locations captured store →
      ∃ extension target finalStore,
        ValueRel code.own.result source target ∧
        Core.Evaluates (bundleValues targets :: installationEnvironment captured index) store
          (code.body.rename (globalShift index).lift) (.inRight .word target) finalStore ∧
        HeapRel (world ++ extension) final.heap finalStore ∧ InstalledGlobals codes locations captured finalStore

/-- Only named calls use the function IH. Primitive dispatch is proved at the
expression boundary from its actual argument pack and independent computation. -/
def CallSimulation {σ : Type} (functions : List Function) (signatures : List Signature)
    (codes : List GlobalCode) (locations : Nat → Nat) (captured : Core.Environment)
    (name : String) (sources : List Semantics.Value) (initial : Semantics.State σ)
    (result : Semantics.Result Semantics.Value) (final : Semantics.State σ) : Prop :=
  ∀ {function code index}, functions.find? (·.name == name) = some function →
    signatures.find? (·.name == name) = some code.own → codes[index]? = some code →
    FunctionSimulation codes locations captured code index sources initial result final

/- The six nontrivial motives below ignore proof identity. They can be supplied
to the generated mutual recursor by adding a final `fun _ => ...` argument.
Loop and pattern-alternative motives are `True` because their enclosing
statement forms are outside RecursiveStatement. -/
def ExprMotive {σ : Type} (functions : List Function) (signatures : List Signature)
    (codes : List GlobalCode) (locations : Nat → Nat) (captured : Core.Environment)
    (sourceEnvironment : Semantics.Environment) (expression : Expr)
    (initial : Semantics.State σ) (result : Semantics.Result Semantics.Value) (final : Semantics.State σ) : Prop :=
  RecursiveExpression functions expression →
    ExprSimulation signatures codes locations captured sourceEnvironment expression initial result final

def ExprsMotive {σ : Type} (functions : List Function) (signatures : List Signature)
    (codes : List GlobalCode) (locations : Nat → Nat) (captured : Core.Environment)
    (sourceEnvironment : Semantics.Environment) (expressions : List Expr)
    (initial : Semantics.State σ) (result : Semantics.Result (List Semantics.Value))
    (final : Semantics.State σ) : Prop :=
  (∀ expression ∈ expressions, RecursiveExpression functions expression) →
    ExprsSimulation signatures codes locations captured sourceEnvironment expressions initial result final

def FunctionMotive {σ : Type} (functions : List Function) (signatures : List Signature)
    (codes : List GlobalCode) (locations : Nat → Nat) (captured : Core.Environment)
    (function : Function) (sources : List Semantics.Value) (initial : Semantics.State σ)
    (result : Semantics.Result Semantics.Value) (final : Semantics.State σ) : Prop :=
  ∀ {name code index}, functions.find? (·.name == name) = some function →
    signatures.find? (·.name == name) = some code.own → codes[index]? = some code →
    FunctionSimulation codes locations captured code index sources initial result final

def StmtMotive {σ : Type} (functions : List Function) (signatures : List Signature)
    (codes : List GlobalCode) (locations : Nat → Nat) (captured : Core.Environment)
    (sourceEnvironment : Semantics.Environment) (statement : Stmt)
    (initial : Semantics.State σ) (control : Semantics.Control) (final : Semantics.State σ) : Prop :=
  RecursiveStatement functions statement →
    StmtSimulation signatures codes locations captured sourceEnvironment statement initial control final

def StatementsMotive {σ : Type} (functions : List Function) (signatures : List Signature)
    (codes : List GlobalCode) (locations : Nat → Nat) (captured : Core.Environment)
    (sourceEnvironment : Semantics.Environment) (statements : List Stmt)
    (initial : Semantics.State σ) (control : Semantics.Control) (final : Semantics.State σ) : Prop :=
  (∀ statement ∈ statements, RecursiveStatement functions statement) →
    StatementsSimulation signatures codes locations captured sourceEnvironment statements initial control final

theorem ExprSimulation.fault {σ : Type} (signatures : List Signature)
    (codes : List GlobalCode) (locations : Nat → Nat) (captured : Core.Environment)
    (sourceEnvironment : Semantics.Environment) (expression : Expr)
    (initial final : Semantics.State σ) (reason : Semantics.Fault) :
    ExprSimulation signatures codes locations captured sourceEnvironment expression initial (.fault reason) final := by
  intro source impossible
  cases impossible

theorem ExprsSimulation.fault {σ : Type} (signatures : List Signature)
    (codes : List GlobalCode) (locations : Nat → Nat) (captured : Core.Environment)
    (sourceEnvironment : Semantics.Environment) (expressions : List Expr)
    (initial final : Semantics.State σ) (reason : Semantics.Fault) :
    ExprsSimulation signatures codes locations captured sourceEnvironment expressions initial (.fault reason) final := by
  intro sources impossible
  cases impossible

theorem StmtSimulation.fault {σ : Type} (signatures : List Signature)
    (codes : List GlobalCode) (locations : Nat → Nat) (captured : Core.Environment)
    (sourceEnvironment : Semantics.Environment) (statement : Stmt)
    (initial final : Semantics.State σ) (reason : Semantics.Fault) :
    StmtSimulation signatures codes locations captured sourceEnvironment statement initial (.fault reason) final := by
  intro impossible
  cases impossible

theorem StatementsSimulation.fault {σ : Type} (signatures : List Signature)
    (codes : List GlobalCode) (locations : Nat → Nat) (captured : Core.Environment)
    (sourceEnvironment : Semantics.Environment) (statements : List Stmt)
    (initial final : Semantics.State σ) (reason : Semantics.Fault) :
    StatementsSimulation signatures codes locations captured sourceEnvironment statements initial (.fault reason) final := by
  intro impossible
  cases impossible

theorem FunctionSimulation.fault {σ : Type} (codes : List GlobalCode)
    (locations : Nat → Nat) (captured : Core.Environment) (code : GlobalCode) (index : Nat)
    (sources : List Semantics.Value) (initial final : Semantics.State σ) (reason : Semantics.Fault) :
    FunctionSimulation codes locations captured code index sources initial (.fault reason) final := by
  intro source impossible
  cases impossible

end Solcore.Frontend.RustHull.DerivationCorrespondence
