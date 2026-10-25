import Solcore.Frontend.RustHull.NamedCallCorrespondence
import Solcore.Frontend.RustHull.ClosureFrameCorrespondence

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

/-- Structured local control includes blocks, loops and loop transfers.
External effects and pattern alternatives have separate proof obligations. -/
def RecursiveStatement (functions : List Function) : Stmt → Prop
  | ⟨.letDecl _ _, _⟩ | ⟨.comment _, _⟩ => True
  | ⟨.assign _ value, _⟩ | ⟨.expression value, _⟩ | ⟨.returnStmt value, _⟩ =>
      RecursiveExpression functions value
  | ⟨.block body, _⟩ => ∀ statement ∈ body, RecursiveStatement functions statement
  | ⟨.forLoop init condition post body, _⟩ =>
      (∀ statement ∈ init, RecursiveStatement functions statement) ∧
      RecursiveExpression functions condition ∧
      (∀ statement ∈ post, RecursiveStatement functions statement) ∧
      (∀ statement ∈ body, RecursiveStatement functions statement)
  | ⟨.breakStmt, _⟩ | ⟨.continueStmt, _⟩ => True
  | _ => False
termination_by statement => sizeOf statement

/-- Language failures are executable outcomes. Malformed source observations
have no representation in the Core language result. -/
def SafeResult {α : Type} : Semantics.Result α → Prop
  | .value _ | .fault (.language _) => True
  | .fault _ => False

/-- Normal transfers and language failures can leave a statement or loop. -/
def SafeControl : Semantics.Control → Prop
  | .fault (.language _) => True
  | .fault _ => False
  | _ => True

theorem safeResult_fault_iff {α : Type} (reason : Semantics.Fault) :
    SafeResult (α := α) (.fault reason) ↔ ∃ word, reason = .language word := by
  cases reason <;> simp [SafeResult]

theorem safeControl_fault_iff (reason : Semantics.Fault) :
    SafeControl (.fault reason) ↔ ∃ word, reason = .language word := by
  cases reason <;> simp [SafeControl]

inductive ArgumentsResultRel (arguments : List Lowered) :
    Semantics.Result (List Semantics.Value) → Core.Value → Prop where
  | value {sources : List Semantics.Value} {targets : List Core.Value}
      (related : ArgumentsRel arguments sources targets) :
      ArgumentsResultRel arguments (.value sources) (.inRight .word (bundleValues targets))
  | language (reason : Core.Word) :
      ArgumentsResultRel arguments (.fault (.language reason))
        (.inLeft (packArguments arguments).type (.word reason))

theorem normalControl_safe {control : Semantics.Control} (normal : NormalControl control) :
    SafeControl control := by cases control <;> simp_all [NormalControl, SafeControl]

def RecursiveProgram (functions : List Function) : Prop :=
  ∀ function ∈ functions, ∀ statement ∈ function.body, RecursiveStatement functions statement

/-- Preserve the indexed source result through the exact emitted Core expression,
including the reason and heap at a language failure. -/
def ExprSimulation {σ : Type} (signatures : List Signature)
    (codes : List GlobalCode) (locations : Nat → Nat) (captured : Core.Environment)
    (sourceEnvironment : Semantics.Environment) (expression : Expr)
    (initial : Semantics.State σ) (result : Semantics.Result Semantics.Value) (final : Semantics.State σ) : Prop :=
  SafeResult result →
    ∀ {fuel scope lowered}, lowerExpression fuel signatures scope expression = .ok lowered →
    ∀ {world mapping environment store},
      EnvironmentRel world sourceEnvironment scope mapping environment →
      GlobalEnvironmentRel codes locations scope mapping environment →
      HeapRel world initial.heap store → InstalledGlobals codes locations captured store →
      ∃ extension targetValue finalStore,
        ResultRel lowered.type result targetValue ∧
        Core.Evaluates environment store (lowered.expression.rename mapping)
          targetValue finalStore ∧
        HeapRel (world ++ extension) final.heap finalStore ∧ InstalledGlobals codes locations captured finalStore ∧ ClosuresPreserved store finalStore

def ExprsSimulation {σ : Type} (signatures : List Signature)
    (codes : List GlobalCode) (locations : Nat → Nat) (captured : Core.Environment)
    (sourceEnvironment : Semantics.Environment) (expressions : List Expr)
    (initial : Semantics.State σ) (result : Semantics.Result (List Semantics.Value))
    (final : Semantics.State σ) : Prop :=
  SafeResult result →
    ∀ {fuel scope arguments}, expressions.mapM (lowerExpression fuel signatures scope) = .ok arguments →
    ∀ {world mapping environment store},
      EnvironmentRel world sourceEnvironment scope mapping environment →
      GlobalEnvironmentRel codes locations scope mapping environment →
      HeapRel world initial.heap store → InstalledGlobals codes locations captured store →
      ∃ extension targets finalStore,
        ArgumentsResultRel arguments result targets ∧
        Core.Evaluates environment store ((packArguments arguments).expression.rename mapping)
          targets finalStore ∧
        HeapRel (world ++ extension) final.heap finalStore ∧ InstalledGlobals codes locations captured finalStore ∧ ClosuresPreserved store finalStore

def StmtSimulation {σ : Type} (signatures : List Signature)
    (codes : List GlobalCode) (locations : Nat → Nat) (captured : Core.Environment)
    (sourceEnvironment : Semantics.Environment) (statement : Stmt)
    (initial : Semantics.State σ) (control : Semantics.Control) (final : Semantics.State σ) : Prop :=
  SafeControl control →
    ∀ {fuel scope result loops expression}, lowerStatement fuel signatures scope result loops statement = .ok expression →
    ∀ {world mapping environment store},
      EnvironmentRel world sourceEnvironment scope mapping environment →
      GlobalEnvironmentRel codes locations scope mapping environment →
      HeapRel world initial.heap store → InstalledGlobals codes locations captured store →
      ∃ extension targetValue finalStore,
        ControlRel result control targetValue ∧
        Core.Evaluates environment store (expression.rename mapping) targetValue finalStore ∧
        HeapRel (world ++ extension) final.heap finalStore ∧ InstalledGlobals codes locations captured finalStore ∧ ClosuresPreserved store finalStore

def StatementsSimulation {σ : Type} (signatures : List Signature)
    (codes : List GlobalCode) (locations : Nat → Nat) (captured : Core.Environment)
    (sourceEnvironment : Semantics.Environment) (statements : List Stmt)
    (initial : Semantics.State σ) (control : Semantics.Control) (final : Semantics.State σ) : Prop :=
  SafeControl control →
    ∀ {fuel scope result loops expression}, lowerStatements fuel signatures scope result loops statements = .ok expression →
    ∀ {world mapping environment store},
      EnvironmentRel world sourceEnvironment scope mapping environment →
      GlobalEnvironmentRel codes locations scope mapping environment →
      HeapRel world initial.heap store → InstalledGlobals codes locations captured store →
      ∃ extension targetValue finalStore,
        ControlRel result control targetValue ∧
        Core.Evaluates environment store (expression.rename mapping) targetValue finalStore ∧
        HeapRel (world ++ extension) final.heap finalStore ∧ InstalledGlobals codes locations captured finalStore ∧ ClosuresPreserved store finalStore

/-- The exact closure body installed at a real global slot. The source function
is tracked by the mutual induction motive and its compiler lookup premises. -/
def FunctionSimulation {σ : Type} (codes : List GlobalCode) (locations : Nat → Nat)
    (captured : Core.Environment) (code : GlobalCode) (index : Nat)
    (sources : List Semantics.Value) (initial : Semantics.State σ)
    (result : Semantics.Result Semantics.Value) (final : Semantics.State σ) : Prop :=
  SafeResult result →
    ∀ {targets}, ValuesRel code.own.parameters sources targets →
    ∀ {world store}, HeapRel world initial.heap store → InstalledGlobals codes locations captured store →
      ∃ extension target finalStore,
        ResultRel code.own.result result target ∧
        Core.Evaluates (bundleValues targets :: installationEnvironment captured index) store
          (code.body.rename (globalShift index).lift) target finalStore ∧
        HeapRel (world ++ extension) final.heap finalStore ∧ InstalledGlobals codes locations captured finalStore ∧ ClosuresPreserved store finalStore

theorem ExprSimulation.value {σ : Type} {signatures : List Signature}
    {codes : List GlobalCode} {locations : Nat → Nat} {captured : Core.Environment}
    {env : Semantics.Environment} {expression : Expr} {initial final : Semantics.State σ}
    {result : Semantics.Result Semantics.Value}
    (simulation : ExprSimulation signatures codes locations captured env expression initial result final)
    {source : Semantics.Value} (normal : result = .value source)
    {fuel : Nat} {scope : Scope} {lowered : Lowered}
    (compiled : lowerExpression fuel signatures scope expression = .ok lowered)
    {world : World} {mapping : Core.Renaming} {environment : Core.Environment} {store : Core.Store}
    (locals : EnvironmentRel world env scope mapping environment)
    (globals : GlobalEnvironmentRel codes locations scope mapping environment)
    (heap : HeapRel world initial.heap store) (installed : InstalledGlobals codes locations captured store) :
    ∃ extension target finalStore,
      ValueRel lowered.type source target ∧
      Core.Evaluates environment store (lowered.expression.rename mapping) (.inRight .word target) finalStore ∧
      HeapRel (world ++ extension) final.heap finalStore ∧ InstalledGlobals codes locations captured finalStore ∧
      ClosuresPreserved store finalStore := by
  subst result
  obtain ⟨extension, target, finalStore, related, evaluated, heap, installed, frame⟩ :=
    simulation trivial compiled locals globals heap installed
  cases related with
  | value related => exact ⟨extension, _, finalStore, related, evaluated, heap, installed, frame⟩

theorem ExprsSimulation.value {σ : Type} {signatures : List Signature}
    {codes : List GlobalCode} {locations : Nat → Nat} {captured : Core.Environment}
    {env : Semantics.Environment} {expressions : List Expr} {initial final : Semantics.State σ}
    {result : Semantics.Result (List Semantics.Value)}
    (simulation : ExprsSimulation signatures codes locations captured env expressions initial result final)
    {sources : List Semantics.Value} (normal : result = .value sources)
    {fuel : Nat} {scope : Scope} {arguments : List Lowered}
    (compiled : expressions.mapM (lowerExpression fuel signatures scope) = .ok arguments)
    {world : World} {mapping : Core.Renaming} {environment : Core.Environment} {store : Core.Store}
    (locals : EnvironmentRel world env scope mapping environment)
    (globals : GlobalEnvironmentRel codes locations scope mapping environment)
    (heap : HeapRel world initial.heap store) (installed : InstalledGlobals codes locations captured store) :
    ∃ extension targets finalStore,
      ArgumentsRel arguments sources targets ∧
      Core.Evaluates environment store ((packArguments arguments).expression.rename mapping)
        (.inRight .word (bundleValues targets)) finalStore ∧
      HeapRel (world ++ extension) final.heap finalStore ∧ InstalledGlobals codes locations captured finalStore ∧
      ClosuresPreserved store finalStore := by
  subst result
  obtain ⟨extension, target, finalStore, related, evaluated, heap, installed, frame⟩ :=
    simulation trivial compiled locals globals heap installed
  cases related with
  | value related => exact ⟨extension, _, finalStore, related, evaluated, heap, installed, frame⟩

/-- Only named calls use the function IH. Primitive dispatch is proved at the
expression boundary from its actual argument pack and independent computation. -/
def CallSimulation {σ : Type} (functions : List Function) (signatures : List Signature)
    (codes : List GlobalCode) (locations : Nat → Nat) (captured : Core.Environment)
    (name : String) (sources : List Semantics.Value) (initial : Semantics.State σ)
    (result : Semantics.Result Semantics.Value) (final : Semantics.State σ) : Prop :=
  ∀ {function code index}, functions.find? (·.name == name) = some function →
    signatures.find? (·.name == name) = some code.own → codes[index]? = some code →
    FunctionSimulation codes locations captured code index sources initial result final

/- These motives ignore proof identity. The mutual recursor uses the separate
LoopMotive for installed loop closures. Pattern alternatives remain outside
RecursiveStatement and therefore have no simulation obligation here. -/
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

end Solcore.Frontend.RustHull.DerivationCorrespondence
