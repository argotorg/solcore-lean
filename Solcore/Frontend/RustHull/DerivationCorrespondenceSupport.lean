import Solcore.Frontend.RustHull.NamedCallCorrespondence
import Solcore.Frontend.RustHull.ClosureFrameCorrespondence
import Solcore.Frontend.RustHull.ScopeCoverage
import Solcore.Frontend.RustHull.EffectStateCorrespondence
import Solcore.Frontend.RustHull.EffectEnvironmentCorrespondence

/-! Pointwise simulation statements for induction on a finite, independent Hull
execution derivation. No statement assumes the simulation of every execution
of a function, and no syntactic call rank is imposed. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.DerivationCorrespondence
open Correspondence ScalarExecution StatementCorrespondence PureCallCorrespondence

/-- Structural expressions and known named calls, including recursive calls.
An absent named function is accepted for a pure builtin or an explicitly
supported external operation. -/
inductive ExecutableExpression (supported : String → Prop) (functions : List Function) : Expr → Prop where
  | word (type text span) : ExecutableExpression supported functions ⟨type, .word text, span⟩
  | bool (type value span) : ExecutableExpression supported functions ⟨type, .bool value, span⟩
  | unit (type span) : ExecutableExpression supported functions ⟨type, .unit, span⟩
  | var (type name span) : ExecutableExpression supported functions ⟨type, .var name, span⟩
  | pair {left right} (first : ExecutableExpression supported functions left)
      (second : ExecutableExpression supported functions right) (type span) :
      ExecutableExpression supported functions ⟨type, .pair left right, span⟩
  | fst {value} (operand : ExecutableExpression supported functions value) (type span) :
      ExecutableExpression supported functions ⟨type, .fst value, span⟩
  | snd {value} (operand : ExecutableExpression supported functions value) (type span) :
      ExecutableExpression supported functions ⟨type, .snd value, span⟩
  | inl {value} (operand : ExecutableExpression supported functions value) (type target span) :
      ExecutableExpression supported functions ⟨type, .inl target value, span⟩
  | inr {value} (operand : ExecutableExpression supported functions value) (type target span) :
      ExecutableExpression supported functions ⟨type, .inr target value, span⟩
  | inK {value} (operand : ExecutableExpression supported functions value) (index type target span) :
      ExecutableExpression supported functions ⟨type, .inK index target value, span⟩
  | conditional {test yes no} (condition : ExecutableExpression supported functions test)
      (yesBranch : ExecutableExpression supported functions yes) (noBranch : ExecutableExpression supported functions no)
      (type target span) : ExecutableExpression supported functions ⟨type, .ifThen target test yes no, span⟩
  | builtin {name arguments operation}
      (classified : pureBuiltin? name = some operation)
      (notFunction : functions.find? (·.name == name) = none)
      (argumentsEligible : ∀ argument ∈ arguments, ExecutableExpression supported functions argument)
      (type span) : ExecutableExpression supported functions ⟨type, .call name arguments, span⟩
  | named {name arguments function}
      (selected : functions.find? (·.name == name) = some function)
      (argumentsEligible : ∀ argument ∈ arguments, ExecutableExpression supported functions argument)
      (type span) : ExecutableExpression supported functions ⟨type, .call name arguments, span⟩

  | external {name arguments}
      (available : supported name)
      (notFunction : functions.find? (·.name == name) = none)
      (argumentsEligible : ∀ argument ∈ arguments, ExecutableExpression supported functions argument)
      (type span) : ExecutableExpression supported functions ⟨type, .call name arguments, span⟩

abbrev RecursiveExpression (functions : List Function) (expression : Expr) : Prop :=
  ExecutableExpression (fun _ => False) functions expression

namespace RecursiveExpression
export ExecutableExpression (word bool unit var pair fst snd inl inr inK conditional builtin named)
end RecursiveExpression

/-- Structured local control includes blocks, loops and loop transfers.
External effects have separate proof obligations; Hull's explicit revert is
eligible where the `revert` builtin is supported. -/
def ExecutableStatement (supported : String → Prop) (functions : List Function) : Stmt → Prop
  | ⟨.letDecl _ _, _⟩ | ⟨.comment _, _⟩ => True
  | ⟨.assign _ value, _⟩ | ⟨.expression value, _⟩ | ⟨.returnStmt value, _⟩ =>
      ExecutableExpression supported functions value
  | ⟨.block body, _⟩ => ∀ statement ∈ body, ExecutableStatement supported functions statement
  | ⟨.forLoop init condition post body, _⟩ =>
      (∀ statement ∈ init, ExecutableStatement supported functions statement) ∧
      ExecutableExpression supported functions condition ∧
      (∀ statement ∈ post, ExecutableStatement supported functions statement) ∧
      (∀ statement ∈ body, ExecutableStatement supported functions statement)
  | ⟨.matchStmt _ value alternatives, _⟩ =>
      ExecutableExpression supported functions value ∧
      (∀ alternative ∈ alternatives, ∀ statement ∈ alternative.body, ExecutableStatement supported functions statement)
  | ⟨.breakStmt, _⟩ | ⟨.continueStmt, _⟩ => True
  | ⟨.revert _, _⟩ => supported "revert"
  | _ => False
termination_by statement => sizeOf statement
decreasing_by
  all_goals first | decreasing_trivial | skip
  have smaller := List.sizeOf_lt_of_mem ‹alternative ∈ alternatives›
  have bodySmaller : sizeOf alternative.body < sizeOf alternative := by
    cases alternative
    simp
    omega
  omega

abbrev RecursiveStatement (functions : List Function) (statement : Stmt) : Prop :=
  ExecutableStatement (fun _ => False) functions statement

inductive ArgumentsResultRel (arguments : List Lowered) :
    Semantics.Result (List Semantics.Value) → Core.Value → Prop where
  | value {sources : List Semantics.Value} {targets : List Core.Value}
      (related : ArgumentsRel arguments sources targets) :
      ArgumentsResultRel arguments (.value sources) (.inRight .word (bundleValues targets))
  | language (reason : Core.Word) :
      ArgumentsResultRel arguments (.fault (.language reason))
        (.inLeft (packArguments arguments).type (.word reason))

def ExecutableProgram (supported : String → Prop) (functions : List Function) : Prop :=
  ∀ function ∈ functions, ∀ statement ∈ function.body, ExecutableStatement supported functions statement

abbrev RecursiveProgram (functions : List Function) : Prop := ExecutableProgram (fun _ => False) functions

/-- Preserve the indexed source result through the exact emitted Core expression,
including the reason and heap at a language failure. -/
def ExprSimulation {σ : Type} {model : StateModel σ} {slots : List EffectSlot} (signatures : List Signature)
    (codes : List GlobalCode) (locations : Nat → Nat) (captured : Core.Environment)
    (sourceEnvironment : Semantics.Environment) (expression : Expr)
    (initial : Semantics.State σ) (result : Semantics.Result Semantics.Value) (final : Semantics.State σ) : Prop :=
  ∀ {fuel scope lowered}, lowerExpression fuel signatures scope expression = .ok lowered →
    ScopeCoverage sourceEnvironment scope →
    ∀ {world mapping environment store},
      EnvironmentRel world sourceEnvironment scope mapping environment →
      GlobalEnvironmentRel codes locations scope mapping environment →
      EffectEnvironmentRel slots scope mapping environment →
      StateRel model world initial store → InstalledGlobals codes locations captured store →
      ∃ extension targetValue finalStore,
        ResultRel lowered.type result targetValue ∧
        Core.Evaluates environment store (lowered.expression.rename mapping)
          targetValue finalStore ∧
        StateRel model (world ++ extension) final finalStore ∧ InstalledGlobals codes locations captured finalStore ∧ ClosuresPreserved store finalStore

def ExprsSimulation {σ : Type} {model : StateModel σ} {slots : List EffectSlot} (signatures : List Signature)
    (codes : List GlobalCode) (locations : Nat → Nat) (captured : Core.Environment)
    (sourceEnvironment : Semantics.Environment) (expressions : List Expr)
    (initial : Semantics.State σ) (result : Semantics.Result (List Semantics.Value))
    (final : Semantics.State σ) : Prop :=
  ∀ {fuel scope arguments}, expressions.mapM (lowerExpression fuel signatures scope) = .ok arguments →
    ScopeCoverage sourceEnvironment scope →
    ∀ {world mapping environment store},
      EnvironmentRel world sourceEnvironment scope mapping environment →
      GlobalEnvironmentRel codes locations scope mapping environment →
      EffectEnvironmentRel slots scope mapping environment →
      StateRel model world initial store → InstalledGlobals codes locations captured store →
      ∃ extension targets finalStore,
        ArgumentsResultRel arguments result targets ∧
        Core.Evaluates environment store ((packArguments arguments).expression.rename mapping)
          targets finalStore ∧
        StateRel model (world ++ extension) final finalStore ∧ InstalledGlobals codes locations captured finalStore ∧ ClosuresPreserved store finalStore

def StmtSimulation {σ : Type} {model : StateModel σ} {slots : List EffectSlot} (signatures : List Signature)
    (codes : List GlobalCode) (locations : Nat → Nat) (captured : Core.Environment)
    (sourceEnvironment : Semantics.Environment) (statement : Stmt)
    (initial : Semantics.State σ) (control : Semantics.Control) (final : Semantics.State σ) : Prop :=
  ∀ {fuel scope result loops expression}, lowerStatement fuel signatures scope result loops statement = .ok expression →
    ScopeCoverage sourceEnvironment scope →
    ∀ {world mapping environment store},
      EnvironmentRel world sourceEnvironment scope mapping environment →
      GlobalEnvironmentRel codes locations scope mapping environment →
      EffectEnvironmentRel slots scope mapping environment →
      StateRel model world initial store → InstalledGlobals codes locations captured store →
      ∃ extension targetValue finalStore,
        ControlRel result control targetValue ∧
        Core.Evaluates environment store (expression.rename mapping) targetValue finalStore ∧
        StateRel model (world ++ extension) final finalStore ∧ InstalledGlobals codes locations captured finalStore ∧ ClosuresPreserved store finalStore

def StatementsSimulation {σ : Type} {model : StateModel σ} {slots : List EffectSlot} (signatures : List Signature)
    (codes : List GlobalCode) (locations : Nat → Nat) (captured : Core.Environment)
    (sourceEnvironment : Semantics.Environment) (statements : List Stmt)
    (initial : Semantics.State σ) (control : Semantics.Control) (final : Semantics.State σ) : Prop :=
  ∀ {fuel scope result loops expression}, lowerStatements fuel signatures scope result loops statements = .ok expression →
    ScopeCoverage sourceEnvironment scope →
    ∀ {world mapping environment store},
      EnvironmentRel world sourceEnvironment scope mapping environment →
      GlobalEnvironmentRel codes locations scope mapping environment →
      EffectEnvironmentRel slots scope mapping environment →
      StateRel model world initial store → InstalledGlobals codes locations captured store →
      ∃ extension targetValue finalStore,
        ControlRel result control targetValue ∧
        Core.Evaluates environment store (expression.rename mapping) targetValue finalStore ∧
        StateRel model (world ++ extension) final finalStore ∧ InstalledGlobals codes locations captured finalStore ∧ ClosuresPreserved store finalStore

/-- The exact closure body installed at a real global slot. The source function
is tracked by the mutual induction motive and its compiler lookup premises. -/
def FunctionSimulation {σ : Type} {model : StateModel σ} (codes : List GlobalCode) (locations : Nat → Nat)
    (captured : Core.Environment) (code : GlobalCode) (index : Nat)
    (sources : List Semantics.Value) (initial : Semantics.State σ)
    (result : Semantics.Result Semantics.Value) (final : Semantics.State σ) : Prop :=
  ∀ {targets}, ValuesRel code.own.parameters sources targets →
    ∀ {world store}, StateRel model world initial store → InstalledGlobals codes locations captured store →
      ∃ extension target finalStore,
        ResultRel code.own.result result target ∧
        Core.Evaluates (bundleValues targets :: installationEnvironment captured index) store
          (code.body.rename (globalShift index).lift) target finalStore ∧
        StateRel model (world ++ extension) final finalStore ∧ InstalledGlobals codes locations captured finalStore ∧ ClosuresPreserved store finalStore

theorem ExprSimulation.value {σ : Type} {model : StateModel σ} {slots : List EffectSlot} {signatures : List Signature}
    {codes : List GlobalCode} {locations : Nat → Nat} {captured : Core.Environment}
    {env : Semantics.Environment} {expression : Expr} {initial final : Semantics.State σ}
    {result : Semantics.Result Semantics.Value}
    (simulation : ExprSimulation (model := model) (slots := slots) signatures codes locations captured env expression initial result final)
    {source : Semantics.Value} (normal : result = .value source)
    {fuel : Nat} {scope : Scope} {lowered : Lowered}
    (compiled : lowerExpression fuel signatures scope expression = .ok lowered)
    (covered : ScopeCoverage env scope)
    {world : World} {mapping : Core.Renaming} {environment : Core.Environment} {store : Core.Store}
    (locals : EnvironmentRel world env scope mapping environment)
    (globals : GlobalEnvironmentRel codes locations scope mapping environment)
    (runtime : EffectEnvironmentRel slots scope mapping environment)
    (heap : StateRel model world initial store) (installed : InstalledGlobals codes locations captured store) :
    ∃ extension target finalStore,
      ValueRel lowered.type source target ∧
      Core.Evaluates environment store (lowered.expression.rename mapping) (.inRight .word target) finalStore ∧
      StateRel model (world ++ extension) final finalStore ∧ InstalledGlobals codes locations captured finalStore ∧
      ClosuresPreserved store finalStore := by
  subst result
  obtain ⟨extension, target, finalStore, related, evaluated, heap, installed, frame⟩ :=
    simulation compiled covered locals globals runtime heap installed
  cases related with
  | value related => exact ⟨extension, _, finalStore, related, evaluated, heap, installed, frame⟩

theorem ExprsSimulation.value {σ : Type} {model : StateModel σ} {slots : List EffectSlot} {signatures : List Signature}
    {codes : List GlobalCode} {locations : Nat → Nat} {captured : Core.Environment}
    {env : Semantics.Environment} {expressions : List Expr} {initial final : Semantics.State σ}
    {result : Semantics.Result (List Semantics.Value)}
    (simulation : ExprsSimulation (model := model) (slots := slots) signatures codes locations captured env expressions initial result final)
    {sources : List Semantics.Value} (normal : result = .value sources)
    {fuel : Nat} {scope : Scope} {arguments : List Lowered}
    (compiled : expressions.mapM (lowerExpression fuel signatures scope) = .ok arguments)
    (covered : ScopeCoverage env scope)
    {world : World} {mapping : Core.Renaming} {environment : Core.Environment} {store : Core.Store}
    (locals : EnvironmentRel world env scope mapping environment)
    (globals : GlobalEnvironmentRel codes locations scope mapping environment)
    (runtime : EffectEnvironmentRel slots scope mapping environment)
    (heap : StateRel model world initial store) (installed : InstalledGlobals codes locations captured store) :
    ∃ extension targets finalStore,
      ArgumentsRel arguments sources targets ∧
      Core.Evaluates environment store ((packArguments arguments).expression.rename mapping)
        (.inRight .word (bundleValues targets)) finalStore ∧
      StateRel model (world ++ extension) final finalStore ∧ InstalledGlobals codes locations captured finalStore ∧
      ClosuresPreserved store finalStore := by
  subst result
  obtain ⟨extension, target, finalStore, related, evaluated, heap, installed, frame⟩ :=
    simulation compiled covered locals globals runtime heap installed
  cases related with
  | value related => exact ⟨extension, _, finalStore, related, evaluated, heap, installed, frame⟩

/-- Only named calls use the function IH. Primitive dispatch is proved at the
expression boundary from its actual argument pack and independent computation. -/
def CallSimulation {σ : Type} {model : StateModel σ} (functions : List Function) (signatures : List Signature)
    (codes : List GlobalCode) (locations : Nat → Nat) (captured : Core.Environment)
    (name : String) (sources : List Semantics.Value) (initial : Semantics.State σ)
    (result : Semantics.Result Semantics.Value) (final : Semantics.State σ) : Prop :=
  ∀ {function code index}, functions.find? (·.name == name) = some function →
    signatures.find? (·.name == name) = some code.own → codes[index]? = some code →
    FunctionSimulation (model := model) codes locations captured code index sources initial result final

/- These motives ignore proof identity. The mutual recursor uses the separate
LoopMotive for installed loop closures and AlternativesMotive for pattern
selection and binder allocation. -/
def ExprMotive {supported : String → Prop} {σ : Type} {model : StateModel σ} {slots : List EffectSlot} (functions : List Function) (signatures : List Signature)
    (codes : List GlobalCode) (locations : Nat → Nat) (captured : Core.Environment)
    (sourceEnvironment : Semantics.Environment) (expression : Expr)
    (initial : Semantics.State σ) (result : Semantics.Result Semantics.Value) (final : Semantics.State σ) : Prop :=
  ExecutableExpression supported functions expression →
    ExprSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment expression initial result final

def ExprsMotive {supported : String → Prop} {σ : Type} {model : StateModel σ} {slots : List EffectSlot} (functions : List Function) (signatures : List Signature)
    (codes : List GlobalCode) (locations : Nat → Nat) (captured : Core.Environment)
    (sourceEnvironment : Semantics.Environment) (expressions : List Expr)
    (initial : Semantics.State σ) (result : Semantics.Result (List Semantics.Value))
    (final : Semantics.State σ) : Prop :=
  (∀ expression ∈ expressions, ExecutableExpression supported functions expression) →
    ExprsSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment expressions initial result final

def FunctionMotive {σ : Type} {model : StateModel σ} (functions : List Function) (signatures : List Signature)
    (codes : List GlobalCode) (locations : Nat → Nat) (captured : Core.Environment)
    (function : Function) (sources : List Semantics.Value) (initial : Semantics.State σ)
    (result : Semantics.Result Semantics.Value) (final : Semantics.State σ) : Prop :=
  ∀ {name code index}, functions.find? (·.name == name) = some function →
    signatures.find? (·.name == name) = some code.own → codes[index]? = some code →
    FunctionSimulation (model := model) codes locations captured code index sources initial result final

def StmtMotive {supported : String → Prop} {σ : Type} {model : StateModel σ} {slots : List EffectSlot} (functions : List Function) (signatures : List Signature)
    (codes : List GlobalCode) (locations : Nat → Nat) (captured : Core.Environment)
    (sourceEnvironment : Semantics.Environment) (statement : Stmt)
    (initial : Semantics.State σ) (control : Semantics.Control) (final : Semantics.State σ) : Prop :=
  ExecutableStatement supported functions statement →
    StmtSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment statement initial control final

def StatementsMotive {supported : String → Prop} {σ : Type} {model : StateModel σ} {slots : List EffectSlot} (functions : List Function) (signatures : List Signature)
    (codes : List GlobalCode) (locations : Nat → Nat) (captured : Core.Environment)
    (sourceEnvironment : Semantics.Environment) (statements : List Stmt)
    (initial : Semantics.State σ) (control : Semantics.Control) (final : Semantics.State σ) : Prop :=
  (∀ statement ∈ statements, ExecutableStatement supported functions statement) →
    StatementsSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment statements initial control final

end Solcore.Frontend.RustHull.DerivationCorrespondence
