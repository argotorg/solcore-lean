import Solcore.Frontend.RustHull.Internal.NamedFunctions
import Solcore.Frontend.RustHull.Lowering
import Solcore.Frontend.RustHull.Internal.LoweringFacts
import Solcore.Frontend.RustHull.Internal.StorageState
import Solcore.Frontend.RustHull.Internal.Statements
import Solcore.Frontend.RustHull.Internal.PublicFunctions
import Solcore.Core.Internal.LocalLoopCorrespondence
import Solcore.Frontend.RustHull.Safety
import Solcore.Frontend.RustHull.Semantics.Frames

/-!
# Derivation-driven simulation

Simulation by induction on a finite independent Hull derivation: atoms, expressions, calls,
statements, loops, matches, faults and inline Yul.
-/

section
-- leanmerge: from Solcore.Frontend.RustHull.DerivationCorrespondenceSupport
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
eligible where the `revert` builtin is supported, and an assembly block when
`YulFragment.Eligible` holds. -/
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
  | ⟨.assembly body, _⟩ => YulFragment.Eligible supported body
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
end

section
-- leanmerge: from Solcore.Frontend.RustHull.AtomDerivationCorrespondence
/-! Actual successful lowering and represented source bindings rule out malformed
literal and variable observations. No source-result classification is assumed. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.DerivationCorrespondence
open Correspondence

theorem word {σ : Type} {model : StateModel σ} {slots : List EffectSlot} {signatures : List Signature} {codes : List GlobalCode}
    {locations : Nat → Nat} {captured : Core.Environment} {env : Semantics.Environment}
    {expression : Expr} {initial : Semantics.State σ} {text : String}
    (kind : expression.kind = .word text) :
    ExprSimulation (model := model) (slots := slots) signatures codes locations captured env expression initial
      (Semantics.literalResult text) initial := by
  intro fuel scope lowered compiled _ world mapping environment store _ _ _ heap installed
  obtain ⟨target, related, evaluated⟩ := ExpressionCorrespondence.word kind compiled mapping environment store
  exact ⟨[], target, store, related, evaluated, by simpa using heap, installed, ClosuresPreserved.refl store⟩

theorem bool {σ : Type} {model : StateModel σ} {slots : List EffectSlot} {signatures : List Signature} {codes : List GlobalCode}
    {locations : Nat → Nat} {captured : Core.Environment} {env : Semantics.Environment}
    {expression : Expr} {initial : Semantics.State σ} {value : Bool}
    (kind : expression.kind = .bool value) :
    ExprSimulation (model := model) (slots := slots) signatures codes locations captured env expression initial
      (Semantics.booleanResult expression.ty value) initial := by
  intro fuel scope lowered compiled _ world mapping environment store _ _ _ heap installed
  obtain ⟨target, related, evaluated⟩ := ExpressionCorrespondence.bool kind compiled mapping environment store
  exact ⟨[], target, store, related, evaluated, by simpa using heap, installed, ClosuresPreserved.refl store⟩

theorem unit {σ : Type} {model : StateModel σ} {slots : List EffectSlot} {signatures : List Signature} {codes : List GlobalCode}
    {locations : Nat → Nat} {captured : Core.Environment} {env : Semantics.Environment}
    {expression : Expr} {initial : Semantics.State σ}
    (kind : expression.kind = .unit) :
    ExprSimulation (model := model) (slots := slots) signatures codes locations captured env expression initial (.value .unit) initial := by
  intro fuel scope lowered compiled _ world mapping environment store _ _ _ heap installed
  obtain ⟨related, evaluated⟩ := ExpressionCorrespondence.unit kind compiled mapping environment store
  exact ⟨[], _, store, related, evaluated, by simpa using heap, installed, ClosuresPreserved.refl store⟩

theorem var {σ : Type} {model : StateModel σ} {slots : List EffectSlot} {signatures : List Signature} {codes : List GlobalCode}
    {locations : Nat → Nat} {captured : Core.Environment} {env : Semantics.Environment}
    {expression : Expr} {initial : Semantics.State σ} {name : String}
    (kind : expression.kind = .var name) :
    ExprSimulation (model := model) (slots := slots) signatures codes locations captured env expression initial
      (Semantics.readResult env initial name) initial := by
  intro fuel scope lowered compiled covered world mapping environment store locals _ _ heap installed
  cases fuel with
  | zero => simp [lowerExpression, fail] at compiled
  | succ fuel =>
      simp only [lowerExpression, kind] at compiled
      obtain ⟨expected, _, compiled⟩ := lower_bind_eq_ok.mp compiled
      cases allowed : name.startsWith Effects.reservedPrefix with
      | true => simp [allowed, fail, lower_bind_eq_ok] at compiled
      | false =>
          simp only [allowed, Bool.false_eq_true, ↓reduceIte] at compiled
          obtain ⟨readCode, readCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
          obtain ⟨checked, _, returned⟩ := lower_bind_eq_ok.mp compiled
          cases checked
          cases returned
          have originalRead := readCompiled
          unfold Scope.read at readCompiled
          obtain ⟨⟨binding, index⟩, looked, _⟩ := lower_bind_eq_ok.mp readCompiled
          obtain ⟨sourceLocation, found⟩ := covered name binding index allowed looked
          obtain ⟨targetLocation, entry, _, _⟩ := locals name sourceLocation binding index found looked
          obtain ⟨source, _, sourceRead, _, _⟩ := heap.cell sourceLocation binding.type targetLocation entry
          obtain ⟨target, related, evaluated⟩ := ExpressionCorrespondence.read locals heap.toHeapRel found sourceRead originalRead
          refine ⟨[], .inRight .word target, store, ?_, evaluated, by simpa using heap,
            installed, ClosuresPreserved.refl store⟩
          simpa only [Semantics.readResult, found, sourceRead] using ResultRel.value related

/-- The actual Boolean conversion accepts only representations whose source
value has a Boolean observation. -/
theorem condition_valid {lowered : Lowered} {expression : Core.Expr}
    {source : Semantics.Value} {target : Core.Value}
    (compiled : condition lowered = .ok expression) (related : ValueRel lowered.type source target) :
    ∃ truth, Semantics.condition? source = some truth := by
  by_cases native : lowered.type = .bool
  · rw [native] at related
    cases related
    exact ⟨_, rfl⟩
  · by_cases sum : lowered.type = .sum .unit .unit
    · rw [sum] at related
      cases related with
      | inl payload => cases payload; exact ⟨false, rfl⟩
      | inr payload => cases payload; exact ⟨true, rfl⟩
    · simp [condition, native, sum, fail] at compiled

end Solcore.Frontend.RustHull.DerivationCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.CallFaultCorrespondence
/-! A failed argument bundle skips the named callee after the actual function
slot read. The call wrapper preserves its reason and the arguments' final store. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.NamedCallCorrespondence

theorem primitive_not_language (name : String) (type : Ty)
    (arguments : List Semantics.Value) (reason : Core.Word) :
    Semantics.primitive? name type arguments ≠ some (.fault (.language reason)) := by
  intro computed
  simp only [Semantics.primitive?] at computed
  split at computed
  all_goals try simp only [Semantics.binaryWords, Semantics.unaryWord, Semantics.ternaryWords,
    Semantics.compareWords, Semantics.booleanResult] at computed
  all_goals repeat (any_goals (first | cases computed | split at computed))

theorem call_argument_failure {codes : List Lowered} {functionCode : Lowered}
    {resultType inputType outputType : Core.Ty} {body : Core.Expr}
    {captured environment : Core.Environment} {mapping : Core.Renaming}
    {initial final : Core.Store} {reason : Core.Word}
    (functionEvaluated : Core.Evaluates environment initial (functionCode.expression.rename mapping)
      (.inRight .word (.closure inputType outputType body captured)) initial)
    (argumentsEvaluated : Core.Evaluates
      (.closure inputType outputType body captured :: environment) initial
      ((packArguments codes).expression.rename (fun index => 1 + mapping index))
      (.inLeft (packArguments codes).type (.word reason)) final) :
    Core.Evaluates environment initial
      ((Core.LanguageResult.bind resultType functionCode.expression
        (Core.LanguageResult.bind resultType ((packArguments codes).expression.weakenAt 0)
          (.apply (.var 1) (.var 0)))).rename mapping)
      (.inLeft resultType (.word reason)) final := by
  have shifted : ((packArguments codes).expression.weakenAt 0).rename mapping.lift =
      (packArguments codes).expression.rename (fun index => 1 + mapping index) := by
    rw [← Core.Expr.rename_insertion, Core.Expr.rename_comp,
      Core.Renaming.lift_comp_insertion_zero]
    congr 1
    funext index
    simp [Core.Renaming.comp, Core.Renaming.insertion, Nat.add_comm]
  apply Core.LanguageResult.bind_success resultType functionEvaluated
  exact Core.LanguageResult.bind_failure resultType
    (by simpa only [shifted] using argumentsEvaluated)

end Solcore.Frontend.RustHull.NamedCallCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.BuiltinTotalCorrespondence
/-! Accepted pure builtin calls derive their argument shape and source result
from the actual compiler checks, then reuse the existing Core execution bridge. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.BuiltinTotalCorrespondence
open Correspondence BuiltinCorrespondence PureCallCorrespondence ScalarExecution

private def checkWords (arguments : List Lowered) : LowerM PUnit :=
  forIn arguments PUnit.unit fun argument _ => do
    expectType .word argument.type
    pure (.yield PUnit.unit)

private theorem checkedWords {arguments : List Lowered}
    (checked : checkWords arguments = .ok PUnit.unit) :
    ∀ argument ∈ arguments, argument.type = .word := by
  induction arguments with
  | nil => simp
  | cons argument rest ih =>
      by_cases same : argument.type = .word
      · have tail : checkWords rest = .ok PUnit.unit := by
          simpa [checkWords, List.forIn_cons, expectType, same] using checked
        intro value member
        rcases List.mem_cons.mp member with rfl | member
        · exact same
        · exact ih tail value member
      · simp [checkWords, List.forIn_cons, expectType, Ne.symm same, fail,
          Bind.bind, Except.bind] at checked

private theorem ordinary_components {scope : Scope} {name : String} {type : Core.Ty}
    {arguments : List Lowered} {lowered : Lowered}
    (effect : Effects.supports name = false)
    (notTo : name ≠ "wordToInteger") (notFrom : name ≠ "wordFromInteger")
    (notZero : name ≠ "iszero")
    (compiled : lowerBuiltin scope name type arguments = .ok lowered) :
    (∀ argument ∈ arguments, argument.type = .word) ∧
      ∃ raw, RustYulPrimitives.compile (primitiveName name)
        ((List.range arguments.length).map fun index =>
          projectArgument index arguments.length (.var 0)) = .ok raw := by
  simp only [lowerBuiltin, effect, notTo, notFrom, notZero, Bool.false_eq_true,
    ↓reduceIte] at compiled
  obtain ⟨checked, wordChecked, compiled⟩ := lower_bind_eq_ok.mp compiled
  cases checked
  obtain ⟨raw, rawCompiled, _⟩ := lower_bind_eq_ok.mp compiled
  refine ⟨checkedWords wordChecked, raw, ?_⟩
  cases found : RustYulPrimitives.compile (primitiveName name)
      ((List.range arguments.length).map fun index => projectArgument index arguments.length (.var 0)) with
  | error reason => simp [found, Except.mapError] at rawCompiled
  | ok result => simpa [found, Except.mapError] using rawCompiled

private def arity : PureBuiltin → Nat
  | .binary _ | .comparison _ => 2
  | .ternary _ => 3
  | _ => 1

private theorem raw_arity (operation : PureBuiltin) {arguments : List Core.Expr}
    {raw : RustYulPrimitives.Lowered}
    (compiled : RustYulPrimitives.compile operation.name arguments = .ok raw) :
    arguments.length = arity operation := by
  by_cases wrong : arguments.length = arity operation
  · exact wrong
  exfalso
  cases operation with
  | binary op =>
      cases op <;> change (if arguments.length = 2 then _ else Except.error _) = .ok raw at compiled
      all_goals simp only [arity] at wrong
      all_goals simp [wrong] at compiled
  | unary op =>
      cases op <;> change (if arguments.length = 1 then _ else Except.error _) = .ok raw at compiled
      all_goals simp only [arity] at wrong
      all_goals simp [wrong] at compiled
  | ternary op =>
      cases op <;> change (if arguments.length = 3 then _ else Except.error _) = .ok raw at compiled
      all_goals simp only [arity] at wrong
      all_goals simp [wrong] at compiled
  | comparison op =>
      cases op <;> change (if arguments.length = 2 then _ else Except.error _) = .ok raw at compiled
      all_goals simp only [arity] at wrong
      all_goals simp [wrong] at compiled
  | toInteger | fromInteger => contradiction
  | iszero | pop =>
      change (if arguments.length = 1 then _ else Except.error _) = .ok raw at compiled
      simp only [arity] at wrong
      simp [wrong] at compiled

private theorem normalized_compiled {scope : Scope} {name : String} {type : Core.Ty}
    {arguments : List Lowered} {lowered : Lowered}
    (compiled : lowerBuiltin scope name type arguments = .ok lowered) :
    lowerBuiltin scope (primitiveName name) type arguments = .ok lowered := by
  have normalized := lowerBuiltin_primitiveName scope name type arguments
  rw [compiled] at normalized
  cases accepted : lowerBuiltin scope (primitiveName name) type arguments with
  | error error => rw [accepted] at normalized; cases normalized
  | ok result =>
      rw [accepted] at normalized
      exact congrArg Except.ok (Option.some.inj normalized).symm

private theorem canonical_name (operation : PureBuiltin) :
    primitiveName operation.name = operation.name := by
  cases operation with
  | binary op => cases op <;> rfl
  | unary op => cases op <;> rfl
  | ternary op => cases op <;> rfl
  | comparison op => cases op <;> rfl
  | toInteger | fromInteger | iszero | pop => rfl

private def Ordinary : PureBuiltin → Prop
  | .toInteger | .fromInteger | .iszero => False
  | _ => True

private theorem ordinary_arguments (operation : PureBuiltin) (ordinary : Ordinary operation)
    {scope : Scope} {type : Core.Ty} {arguments : List Lowered} {lowered : Lowered}
    (compiled : lowerBuiltin scope operation.name type arguments = .ok lowered) :
    (∀ argument ∈ arguments, argument.type = .word) ∧ arguments.length = arity operation := by
  have effect : Effects.supports operation.name = false := by
    cases operation with
    | binary op => cases op <;> rfl
    | unary op => cases op <;> rfl
    | ternary op => cases op <;> rfl
    | comparison op => cases op <;> rfl
    | toInteger | fromInteger | iszero | pop => rfl
  have noTo : operation.name ≠ "wordToInteger" := by
    cases operation with
    | binary op => cases op <;> decide
    | unary op => cases op <;> decide
    | ternary op => cases op <;> decide
    | comparison op => cases op <;> decide
    | toInteger | fromInteger | iszero => exact ordinary.elim
    | pop => decide
  have noFrom : operation.name ≠ "wordFromInteger" := by
    cases operation with
    | binary op => cases op <;> decide
    | unary op => cases op <;> decide
    | ternary op => cases op <;> decide
    | comparison op => cases op <;> decide
    | toInteger | fromInteger | iszero => exact ordinary.elim
    | pop => decide
  have noZero : operation.name ≠ "iszero" := by
    cases operation with
    | binary op => cases op <;> decide
    | unary op => cases op <;> decide
    | ternary op => cases op <;> decide
    | comparison op => cases op <;> decide
    | toInteger | fromInteger | iszero => exact ordinary.elim
    | pop => decide
  obtain ⟨words, raw, accepted⟩ := ordinary_components effect noTo noFrom noZero compiled
  rw [canonical_name] at accepted
  exact ⟨words, by simpa only [List.length_map, List.length_range] using raw_arity operation accepted⟩

private theorem word_arguments {arguments : List Lowered} {sources : List Semantics.Value}
    {targets : List Core.Value} (related : ArgumentsRel arguments sources targets)
    (words : ∀ argument ∈ arguments, argument.type = .word) :
    ∃ (expressions : List Core.Expr) (values : List Core.Word),
      arguments = expressions.map (fun expression => Lowered.mk .word expression) ∧
      sources = values.map Semantics.Value.word ∧ targets = values.map Core.Value.word ∧
      expressions.length = values.length := by
  induction related with
  | nil => exact ⟨[], [], rfl, rfl, rfl, rfl⟩
  | @cons argument arguments source sources target targets head tail ih =>
      obtain ⟨expressions, values, rfl, rfl, rfl, lengths⟩ :=
        ih (fun member selected => words member (List.mem_cons_of_mem _ selected))
      have typed := words argument (List.mem_cons_self ..)
      cases argument with
      | mk type expression =>
          simp only at typed
          subst type
          cases head with
          | word value =>
              exact ⟨expression :: expressions, value :: values, rfl, rfl, rfl, congrArg Nat.succ lengths⟩

private theorem one_word {arguments : List Lowered} {sources : List Semantics.Value}
    {targets : List Core.Value} (related : ArgumentsRel arguments sources targets)
    (words : ∀ argument ∈ arguments, argument.type = .word) (length : arguments.length = 1) :
    ∃ expression value, arguments = [⟨.word, expression⟩] ∧
      sources = [.word value] ∧ targets = [.word value] := by
  obtain ⟨expressions, values, rfl, rfl, rfl, sizes⟩ := word_arguments related words
  simp only [List.length_map] at length
  cases expressions with
  | nil => cases length
  | cons expression rest =>
      have empty : rest = [] := List.eq_nil_of_length_eq_zero (Nat.succ.inj length)
      subst rest
      cases values with
      | nil => cases sizes
      | cons value rest =>
          have empty : rest = [] := List.eq_nil_of_length_eq_zero (Nat.succ.inj sizes.symm)
          subst rest
          exact ⟨expression, value, rfl, rfl, rfl⟩

private theorem two_words {arguments : List Lowered} {sources : List Semantics.Value}
    {targets : List Core.Value} (related : ArgumentsRel arguments sources targets)
    (words : ∀ argument ∈ arguments, argument.type = .word) (length : arguments.length = 2) :
    ∃ leftCode rightCode left right, arguments = [⟨.word, leftCode⟩, ⟨.word, rightCode⟩] ∧
      sources = [.word left, .word right] ∧ targets = [.word left, .word right] := by
  cases related with
  | nil => cases length
  | @cons argument arguments source sources target targets head tail =>
      obtain ⟨rightCode, right, rfl, rfl, rfl⟩ := one_word tail
        (fun member selected => words member (List.mem_cons_of_mem _ selected)) (Nat.succ.inj length)
      have typed := words argument (List.mem_cons_self ..)
      cases argument with
      | mk type expression =>
          simp only at typed
          subst type
          cases head with
          | word left => exact ⟨expression, rightCode, left, right, rfl, rfl, rfl⟩

private theorem three_words {arguments : List Lowered} {sources : List Semantics.Value}
    {targets : List Core.Value} (related : ArgumentsRel arguments sources targets)
    (words : ∀ argument ∈ arguments, argument.type = .word) (length : arguments.length = 3) :
    ∃ firstCode secondCode thirdCode first second third,
      arguments = [⟨.word, firstCode⟩, ⟨.word, secondCode⟩, ⟨.word, thirdCode⟩] ∧
      sources = [.word first, .word second, .word third] ∧ targets = [.word first, .word second, .word third] := by
  cases related with
  | nil => cases length
  | @cons argument arguments source sources target targets head tail =>
      obtain ⟨secondCode, thirdCode, second, third, rfl, rfl, rfl⟩ := two_words tail
        (fun member selected => words member (List.mem_cons_of_mem _ selected)) (Nat.succ.inj length)
      have typed := words argument (List.mem_cons_self ..)
      cases argument with
      | mk type expression =>
          simp only at typed
          subst type
          cases head with
          | word first => exact ⟨expression, secondCode, thirdCode, first, second, third, rfl, rfl, rfl⟩

private theorem conversion_arguments {name : String}
    (named : name = "wordToInteger" ∨ name = "wordFromInteger")
    {scope : Scope} {type : Core.Ty} {arguments : List Lowered} {lowered : Lowered}
    (compiled : lowerBuiltin scope name type arguments = .ok lowered)
    {sources : List Semantics.Value} {targets : List Core.Value}
    (related : ArgumentsRel arguments sources targets) :
    ∃ expression value, arguments = [⟨.word, expression⟩] ∧
      sources = [.word value] ∧ targets = [.word value] := by
  have size : arguments.length = 1 := by
    by_cases size : arguments.length = 1
    · exact size
    · rcases named with rfl | rfl
      all_goals
        change (if arguments.length = 1 then _ else _) = (Except.ok lowered : LowerM Lowered) at compiled
        simp [size, fail, Bind.bind, Except.bind] at compiled
  obtain ⟨argument, rfl⟩ := List.length_eq_one_iff.mp size
  have reduced : lowerBuiltin scope name type [argument] = (do
      expectType .word argument.type
      expectType .word type
      pure argument) := by rcases named with rfl | rfl <;> rfl
  rw [reduced] at compiled
  obtain ⟨checked, typed, _⟩ := lower_bind_eq_ok.mp compiled
  cases checked
  have word := (expectType_eq_of_ok typed).symm
  exact one_word related (by intro member found; simp only [List.mem_singleton] at found; subst member; exact word) rfl

private theorem iszero_arguments {scope : Scope} {type : Core.Ty}
    {arguments : List Lowered} {lowered : Lowered}
    (compiled : lowerBuiltin scope "iszero" type arguments = .ok lowered) :
    ∃ argument, arguments = [argument] := by
  apply List.length_eq_one_iff.mp
  by_cases size : arguments.length = 1
  · exact size
  · change (if decide (arguments.length = 1) && boolLike (packArguments arguments).type then _ else _) =
        (Except.ok lowered : LowerM Lowered) at compiled
    simp [size, fail, Bind.bind, Except.bind] at compiled

private theorem preserved_value {name : String} {sourceType : Ty}
    {sources : List Semantics.Value} {lowered : Lowered}
    {mapping : Core.Renaming} {environment : Core.Environment} {initial final : Core.Store}
    (preserved : ∃ result target, Semantics.primitive? name sourceType sources = some result ∧
      ResultRel lowered.type result target ∧
      Core.Evaluates environment initial (lowered.expression.rename mapping) target final) :
    ∃ source target, Semantics.primitive? name sourceType sources = some (.value source) ∧
      ValueRel lowered.type source target ∧
      Core.Evaluates environment initial (lowered.expression.rename mapping) (.inRight .word target) final := by
  obtain ⟨result, target, meaning, related, evaluated⟩ := preserved
  cases related with
  | value related => exact ⟨_, _, meaning, related, evaluated⟩
  | language reason => exact (NamedCallCorrespondence.primitive_not_language name sourceType sources reason meaning).elim

private theorem canonical_total (operation : PureBuiltin)
    {fuel : Nat} {sourceType : Ty} {type : Core.Ty}
    (typeCompiled : lowerType fuel sourceType = .ok type)
    {scope : Scope} {arguments : List Lowered} {lowered : Lowered}
    (compiled : lowerBuiltin scope operation.name type arguments = .ok lowered)
    {sources : List Semantics.Value} {targets : List Core.Value}
    (related : ArgumentsRel arguments sources targets)
    {mapping : Core.Renaming} {environment : Core.Environment} {initial final : Core.Store}
    (evaluated : Core.Evaluates environment initial ((packArguments arguments).expression.rename mapping)
      (.inRight .word (bundleValues targets)) final) :
    ∃ source target, Semantics.primitive? operation.name sourceType sources = some (.value source) ∧
      ValueRel lowered.type source target ∧
      Core.Evaluates environment initial (lowered.expression.rename mapping) (.inRight .word target) final := by
  cases operation with
  | binary op =>
      obtain ⟨words, length⟩ := ordinary_arguments (.binary op) trivial compiled
      obtain ⟨leftCode, rightCode, left, right, rfl, rfl, rfl⟩ := two_words related words length
      have meaning := op.meaning sourceType left right
      obtain ⟨target, represented, executed⟩ := canonical_preserves (.binary op)
        typeCompiled compiled meaning related evaluated
      exact ⟨_, target, meaning, represented, executed⟩
  | unary op =>
      obtain ⟨words, length⟩ := ordinary_arguments (.unary op) trivial compiled
      obtain ⟨expression, value, rfl, rfl, rfl⟩ := one_word related words length
      have meaning := op.meaning sourceType value
      obtain ⟨target, represented, executed⟩ := canonical_preserves (.unary op)
        typeCompiled compiled meaning related evaluated
      exact ⟨_, target, meaning, represented, executed⟩
  | ternary op =>
      obtain ⟨words, length⟩ := ordinary_arguments (.ternary op) trivial compiled
      obtain ⟨firstCode, secondCode, thirdCode, first, second, third, rfl, rfl, rfl⟩ :=
        three_words related words length
      have meaning := op.meaning sourceType first second third
      obtain ⟨target, represented, executed⟩ := canonical_preserves (.ternary op)
        typeCompiled compiled meaning related evaluated
      exact ⟨_, target, meaning, represented, executed⟩
  | comparison op =>
      obtain ⟨words, length⟩ := ordinary_arguments (.comparison op) trivial compiled
      obtain ⟨leftCode, rightCode, left, right, rfl, rfl, rfl⟩ := two_words related words length
      exact preserved_value (wordComparison op (by cases op <;> rfl) typeCompiled compiled evaluated)
  | toInteger =>
      obtain ⟨expression, value, rfl, rfl, rfl⟩ := conversion_arguments (Or.inl rfl) compiled related
      have meaning : Semantics.primitive? PureBuiltin.toInteger.name sourceType [.word value] =
          some (.value (.word value)) := rfl
      obtain ⟨target, represented, executed⟩ := canonical_preserves .toInteger
        typeCompiled compiled meaning related evaluated
      exact ⟨_, target, meaning, represented, executed⟩
  | fromInteger =>
      obtain ⟨expression, value, rfl, rfl, rfl⟩ := conversion_arguments (Or.inr rfl) compiled related
      have meaning : Semantics.primitive? PureBuiltin.fromInteger.name sourceType [.word value] =
          some (.value (.word value)) := rfl
      obtain ⟨target, represented, executed⟩ := canonical_preserves .fromInteger
        typeCompiled compiled meaning related evaluated
      exact ⟨_, target, meaning, represented, executed⟩
  | iszero =>
      obtain ⟨argument, rfl⟩ := iszero_arguments compiled
      cases related with
      | cons head tail =>
          cases tail
          exact preserved_value (iszero typeCompiled compiled head evaluated)
  | pop =>
      obtain ⟨words, length⟩ := ordinary_arguments .pop trivial compiled
      obtain ⟨expression, value, rfl, rfl, rfl⟩ := one_word related words length
      have meaning : Semantics.primitive? PureBuiltin.pop.name sourceType [.word value] =
          some (.value .unit) := rfl
      obtain ⟨target, represented, executed⟩ := canonical_preserves .pop
        typeCompiled compiled meaning related evaluated
      exact ⟨_, target, meaning, represented, executed⟩

/-- Actual builtin checks determine a successful source primitive result; no
source computation premise is needed. The argument pack's heap is retained. -/
theorem builtin_preserves_result {name : String} {operation : PureBuiltin}
    (classified : pureBuiltin? name = some operation)
    {fuel : Nat} {sourceType : Ty} {type : Core.Ty}
    (typeCompiled : lowerType fuel sourceType = .ok type)
    {scope : Scope} {arguments : List Lowered} {lowered : Lowered}
    (compiled : lowerBuiltin scope name type arguments = .ok lowered)
    {sources : List Semantics.Value} {targets : List Core.Value}
    (related : ArgumentsRel arguments sources targets)
    {mapping : Core.Renaming} {environment : Core.Environment} {initial final : Core.Store}
    (evaluated : Core.Evaluates environment initial ((packArguments arguments).expression.rename mapping)
      (.inRight .word (bundleValues targets)) final) :
    ∃ source target, Semantics.primitive? name sourceType sources = some (.value source) ∧
      ValueRel lowered.type source target ∧
      Core.Evaluates environment initial (lowered.expression.rename mapping) (.inRight .word target) final := by
  have accepted := normalized_compiled compiled
  rw [pureBuiltin_name classified] at accepted
  obtain ⟨source, target, meaning, represented, executed⟩ :=
    canonical_total operation typeCompiled accepted related evaluated
  exact ⟨source, target, by rw [primitiveName_meaning, pureBuiltin_name classified]; exact meaning,
    represented, executed⟩

end Solcore.Frontend.RustHull.BuiltinTotalCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ExternalCallCorrespondence
/-! The operation boundary used by the common recursive proof. Concrete effect
implementations discharge this interface using their independent state model
and the actual accepted builtin code. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.DerivationCorrespondence
open Correspondence ScalarExecution PureCallCorrespondence

def ExternalCallPreservation {σ : Type} (supported : String → Prop)
    (model : StateModel σ) (slots : List EffectSlot) (effects : Semantics.ExternalSemantics σ) : Prop :=
  ∀ {functions name type sources initial final result}, supported name →
    functions.find? (·.name == name) = none →
    Semantics.EvalCall functions effects name type sources initial result final →
    ∀ {typeFuel expected}, lowerType typeFuel type = .ok expected →
    ∀ {scope arguments lowered}, lowerBuiltin scope name expected arguments = .ok lowered →
    ∀ {world mapping environment initialStore argumentStore targets codes locations captured},
      ArgumentsRel arguments sources targets →
      Core.Evaluates environment initialStore ((packArguments arguments).expression.rename mapping)
        (.inRight .word (bundleValues targets)) argumentStore →
      EffectEnvironmentRel slots scope mapping environment →
      StateRel model world initial argumentStore →
      InstalledGlobals codes locations captured argumentStore →
      ∃ target finalStore,
        ResultRel lowered.type result target ∧
        Core.Evaluates environment initialStore (lowered.expression.rename mapping) target finalStore ∧
        StateRel model world final finalStore ∧ InstalledGlobals codes locations captured finalStore ∧
        ClosuresPreserved argumentStore finalStore

theorem ExternalCallPreservation.empty {σ : Type} (model : StateModel σ)
    (slots : List EffectSlot) (effects : Semantics.ExternalSemantics σ) :
    ExternalCallPreservation (fun _ => False) model slots effects := by
  intro functions name type sources initial final result impossible
  cases impossible

end Solcore.Frontend.RustHull.DerivationCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.DerivationCallCorrespondence
/-! Calls and argument lists composed along one independent source execution.
Only the operand and callee derivations already encountered by that execution
are used; recursive callees need no syntactic rank. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.DerivationCallCorrespondence
open Correspondence ScalarExecution NamedCallCorrespondence PureCallCorrespondence
open DerivationCorrespondence

theorem builtin_components {fuel : Nat} {signatures : List Signature} {scope : Scope}
    {name : String} {type : Ty} {arguments : List Expr} {span : Option Span} {lowered : Lowered}
    (notSignature : signatures.find? (·.name == name) = none)
    (compiled : lowerExpression (fuel + 1) signatures scope ⟨type, .call name arguments, span⟩ = .ok lowered) :
    ∃ expected codes, lowerType (fuel + 1) type = .ok expected ∧
      arguments.mapM (lowerExpression fuel signatures scope) = .ok codes ∧
      lowerBuiltin scope name expected codes = .ok lowered := by
  simp only [lowerExpression] at compiled
  obtain ⟨expected, typeCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨codes, argumentsCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  simp only [notSignature] at compiled
  obtain ⟨result, builtinCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨checked, _, returned⟩ := lower_bind_eq_ok.mp compiled
  cases checked
  cases returned
  exact ⟨expected, codes, typeCompiled, argumentsCompiled, builtinCompiled⟩

theorem primitive_call_result {σ : Type} {functions : List Function}
    {effects : Semantics.ExternalSemantics σ} {name : String} {type : Ty}
    {values : List Semantics.Value} {result : Semantics.Result Semantics.Value} {initial final : Semantics.State σ}
    {operation : PureBuiltin} (classified : pureBuiltin? name = some operation)
    (notFunction : functions.find? (·.name == name) = none)
    (called : Semantics.EvalCall functions effects name type values initial result final) :
    final = initial ∧ Semantics.primitive? name type values = some result := by
  cases called with
  | function selected _ => rw [notFunction] at selected; cases selected
  | primitive _ computed => exact ⟨rfl, computed⟩
  | external _ notPrimitive _ =>
      have known := pureBuiltin_known classified type values
      rw [notPrimitive] at known
      cases known

theorem arguments_nil {σ : Type} {model : StateModel σ} {slots : List EffectSlot} (signatures : List Signature) (codes : List GlobalCode)
    (locations : Nat → Nat) (captured : Core.Environment)
    (sourceEnvironment : Semantics.Environment) (state : Semantics.State σ) :
    ExprsSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment [] state (.value []) state := by
  intro fuel scope arguments compiled coverage world mapping environment store locals globals runtime heap installed
  cases compiled
  exact ⟨[], .inRight .word .unit, store, .value .nil, .inRight .unit,
    by simpa using heap, installed, ClosuresPreserved.refl store⟩

theorem arguments_cons {σ : Type} {model : StateModel σ} {slots : List EffectSlot} {functions : List Function} {effects : Semantics.ExternalSemantics σ}
    {signatures : List Signature} {codes : List GlobalCode} {locations : Nat → Nat}
    {captured : Core.Environment} {sourceEnvironment : Semantics.Environment}
    {argument : Expr} {rest : List Expr} {initial middle final : Semantics.State σ}
    {source : Semantics.Value} {result : Semantics.Result (List Semantics.Value)}
    (tailEvaluated : Semantics.EvalExprs functions effects sourceEnvironment rest middle result final)
    (head : ExprSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment argument initial (.value source) middle)
    (tail : ExprsSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment rest middle result final) :
    ExprsSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment (argument :: rest)
      initial (result.map (source :: ·)) final := by
  cases result with
  | value sources =>
      intro fuel scope lowered compiled coverage world mapping environment store locals globals runtime heap installed
      simp only [List.mapM_cons] at compiled
      obtain ⟨headCode, headCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
      obtain ⟨tailCode, tailCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
      cases returned
      obtain ⟨headExtension, target, middleStore, related, headEvaluation, middleHeap, middleInstalled, headFrame⟩ :=
        head.value rfl headCompiled coverage locals globals runtime heap installed
      cases rest with
      | nil =>
          cases tailCompiled
          cases tailEvaluated
          exact ⟨headExtension, .inRight .word target, middleStore, .value (.cons related .nil),
            headEvaluation, middleHeap, middleInstalled, headFrame⟩
      | cons next rest =>
          have tailLocals := (locals.extendWorld headExtension).prepend [target]
          obtain ⟨tailExtension, targets, finalStore, tailRelated, tailEvaluation, finalHeap, finalInstalled, tailFrame⟩ :=
            tail.value rfl tailCompiled coverage tailLocals (globals.prepend [target]) (runtime.prepend [target]) middleHeap middleInstalled
          have nonempty : tailCode ≠ [] := by
            intro empty
            subst tailCode
            simp only [List.mapM_cons] at tailCompiled
            obtain ⟨_, _, tailCompiled⟩ := lower_bind_eq_ok.mp tailCompiled
            obtain ⟨_, _, returned⟩ := lower_bind_eq_ok.mp tailCompiled
            cases returned
          have targetsNonempty : targets ≠ [] := by
            intro empty
            subst targets
            cases tailRelated
            exact nonempty rfl
          refine ⟨headExtension ++ tailExtension, .inRight .word (bundleValues (target :: targets)), finalStore,
            .value (.cons related tailRelated), ?_, ?_, finalInstalled, headFrame.trans tailFrame⟩
          · have renamed : ((packArguments tailCode).expression.rename mapping).weakenAt 0 =
                (packArguments tailCode).expression.rename (fun index => 1 + mapping index) := by
              simp only [← Core.Expr.rename_insertion, Core.Expr.rename_comp]
              congr 1
              funext index
              simp [Core.Renaming.comp, Core.Renaming.insertion, Nat.add_comm]
            cases tailCode with
            | nil => exact (nonempty rfl).elim
            | cons nextCode restCode =>
                change Core.Evaluates environment store
                  ((Core.LocalSequence.pair headCode.type (packArguments (nextCode :: restCode)).type
                    headCode.expression (packArguments (nextCode :: restCode)).expression).rename mapping) _ _
                rw [ContextualExpressionCorrespondence.pair_rename]
                have tailEvaluation' : Core.Evaluates (target :: environment) middleStore
                    (((packArguments (nextCode :: restCode)).expression.rename mapping).weakenAt 0)
                    (.inRight .word (bundleValues targets)) finalStore := by
                  rw [renamed]
                  exact tailEvaluation
                have paired := Core.LocalSequence.pair_success headCode.type
                  (packArguments (nextCode :: restCode)).type headEvaluation tailEvaluation'
                cases targets with
                | nil => exact (targetsNonempty rfl).elim
                | cons firstTarget restTargets => exact paired
          · simpa only [List.append_assoc] using finalHeap


  | fault reason =>
      intro fuel scope lowered compiled coverage world mapping environment store locals globals runtime heap installed
      simp only [List.mapM_cons] at compiled
      obtain ⟨headCode, headCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
      obtain ⟨tailCode, tailCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
      cases returned
      obtain ⟨headExtension, target, middleStore, related, headEvaluation, middleHeap, middleInstalled, headFrame⟩ :=
        head.value rfl headCompiled coverage locals globals runtime heap installed
      cases rest with
      | nil => cases tailEvaluated
      | cons next rest =>
          have tailLocals := (locals.extendWorld headExtension).prepend [target]
          obtain ⟨tailExtension, tailTarget, finalStore, tailRelated, tailEvaluation, finalHeap, finalInstalled, tailFrame⟩ :=
            tail tailCompiled coverage tailLocals (globals.prepend [target]) (runtime.prepend [target]) middleHeap middleInstalled
          cases tailRelated
          rename_i reason
          have nonempty : tailCode ≠ [] := by
            intro empty
            subst tailCode
            simp only [List.mapM_cons] at tailCompiled
            obtain ⟨_, _, tailCompiled⟩ := lower_bind_eq_ok.mp tailCompiled
            obtain ⟨_, _, returned⟩ := lower_bind_eq_ok.mp tailCompiled
            cases returned
          cases tailCode with
          | nil => exact (nonempty rfl).elim
          | cons nextCode restCode =>
              refine ⟨headExtension ++ tailExtension, _, finalStore, .language reason, ?_,
                ?_, finalInstalled, headFrame.trans tailFrame⟩
              · change Core.Evaluates environment store
                  ((Core.LocalSequence.pair headCode.type (packArguments (nextCode :: restCode)).type
                    headCode.expression (packArguments (nextCode :: restCode)).expression).rename mapping) _ _
                rw [ContextualExpressionCorrespondence.pair_rename]
                apply Core.LocalSequence.pair_right_failure _ _ headEvaluation
                have renamed : ((packArguments (nextCode :: restCode)).expression.rename mapping).weakenAt 0 =
                    (packArguments (nextCode :: restCode)).expression.rename (fun index => 1 + mapping index) := by
                  simp only [← Core.Expr.rename_insertion, Core.Expr.rename_comp]
                  congr 1
                  funext index
                  simp [Core.Renaming.comp, Core.Renaming.insertion, Nat.add_comm]
                simpa [renamed] using tailEvaluation
              · simpa only [List.append_assoc] using finalHeap

/-- A failed head skips the rest of the actual compiled argument bundle. -/
theorem arguments_fault {σ : Type} {model : StateModel σ} {slots : List EffectSlot} {signatures : List Signature}
    {codes : List GlobalCode} {locations : Nat → Nat} {captured : Core.Environment}
    {sourceEnvironment : Semantics.Environment} {argument : Expr} {rest : List Expr}
    {initial final : Semantics.State σ} {reason : Semantics.Fault}
    (head : ExprSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment argument
      initial (.fault reason) final) :
    ExprsSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment (argument :: rest)
      initial (.fault reason) final := by
  intro fuel scope lowered compiled coverage world mapping environment store locals globals runtime heap installed
  simp only [List.mapM_cons] at compiled
  obtain ⟨headCode, headCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨tailCode, _, returned⟩ := lower_bind_eq_ok.mp compiled
  cases returned
  obtain ⟨extension, target, finalStore, related, evaluation, finalHeap, finalInstalled, frame⟩ :=
    head headCompiled coverage locals globals runtime heap installed
  cases related
  rename_i reason
  cases tailCode with
  | nil =>
      exact ⟨extension, _, finalStore, .language reason, evaluation, finalHeap, finalInstalled, frame⟩
  | cons first remaining =>
      refine ⟨extension, _, finalStore, .language reason, ?_, finalHeap, finalInstalled, frame⟩
      change Core.Evaluates environment store
        ((Core.LocalSequence.pair headCode.type (packArguments (first :: remaining)).type
          headCode.expression (packArguments (first :: remaining)).expression).rename mapping) _ _
      rw [ContextualExpressionCorrespondence.pair_rename]
      exact Core.LocalSequence.pair_left_failure _ _ evaluation

theorem call_function {σ : Type} {model : StateModel σ} {functions : List Function} {signatures : List Signature}
    {codes : List GlobalCode} {locations : Nat → Nat} {captured : Core.Environment}
    {name : String} {function : Function} {sources : List Semantics.Value}
    {initial final : Semantics.State σ} {result : Semantics.Result Semantics.Value}
    (selected : functions.find? (·.name == name) = some function)
    (continued : ∀ {name code index}, functions.find? (·.name == name) = some function →
      signatures.find? (·.name == name) = some code.own → codes[index]? = some code →
      FunctionSimulation (model := model) codes locations captured code index sources initial result final) :
    CallSimulation (model := model) functions signatures codes locations captured name sources initial result final := by
  intro other code index sourceSelected signatureSelected codeFound
  have same := Option.some.inj (sourceSelected.symm.trans selected)
  subst other
  intro targets values world store heap installed
  exact continued selected signatureSelected codeFound values heap installed

theorem call_not_function {σ : Type} {model : StateModel σ} {functions : List Function} {signatures : List Signature}
    {codes : List GlobalCode} {locations : Nat → Nat} {captured : Core.Environment}
    {name : String} {sources : List Semantics.Value} {initial final : Semantics.State σ}
    {result : Semantics.Result Semantics.Value}
    (absent : functions.find? (·.name == name) = none) :
    CallSimulation (model := model) functions signatures codes locations captured name sources initial result final := by
  intro function code index selected
  rw [absent] at selected
  cases selected

/-- A particular call derivation uses only the argument-list IH and its
selected callee IH. Builtin computation uses the actual compiler branch and
does not assume any callee simulation. -/
theorem call {supported : String → Prop} {σ : Type} {model : StateModel σ} {slots : List EffectSlot} {functions : List Function} {effects : Semantics.ExternalSemantics σ}
    {compilationFuel : Nat} {signatures : List Signature} {programScope : Scope}
    {codes : List GlobalCode} {locations : Nat → Nat} {captured : Core.Environment}
    (signaturesCompiled : functions.mapM (signature compilationFuel) = .ok signatures)
    (codesCompiled : CompiledGlobals compilationFuel signatures programScope (functions.zip signatures).reverse codes)
    {sourceEnvironment : Semantics.Environment} {type : Ty} {name : String} {arguments : List Expr}
    {span : Option Span} {sources : List Semantics.Value} {initial middle final : Semantics.State σ}
    {result : Semantics.Result Semantics.Value}
    (eligible : ExecutableExpression supported functions ⟨type, .call name arguments, span⟩)
    (external : ExternalCallPreservation supported model slots effects)
    (called : Semantics.EvalCall functions effects name type sources middle result final)
    (argumentsIH : ExprsSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment arguments
      initial (.value sources) middle)
    (callIH : CallSimulation (model := model) functions signatures codes locations captured name sources middle result final) :
    ExprSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment
      ⟨type, .call name arguments, span⟩ initial result final := by
  intro fuel scope lowered compiled coverage world mapping environment store locals globals runtime heap installed
  cases fuel with
  | zero => simp [lowerExpression, fail] at compiled
  | succ fuel =>
      cases eligible with
      | builtin classified notFunction argumentsEligible =>
          have notSignature := (SignatureNames.compiled signaturesCompiled).absent notFunction
          obtain ⟨rfl, computed⟩ := primitive_call_result classified notFunction called
          obtain ⟨expected, argumentCodes, typeCompiled, argumentsCompiled, builtinCompiled⟩ :=
            builtin_components notSignature compiled
          obtain ⟨extension, targets, finalStore, related, argumentsEvaluation, finalHeap, finalInstalled, tailFrame⟩ :=
            argumentsIH.value rfl argumentsCompiled coverage locals globals runtime heap installed
          obtain ⟨source, target, meaning, resultRelated, resultEvaluation⟩ :=
            BuiltinTotalCorrespondence.builtin_preserves_result classified typeCompiled builtinCompiled
              related argumentsEvaluation
          have sameResult := Option.some.inj (computed.symm.trans meaning)
          subst result
          exact ⟨extension, .inRight .word target, finalStore, .value resultRelated,
            resultEvaluation, finalHeap, finalInstalled, tailFrame⟩
      | external available notFunction argumentsEligible =>
          have notSignature := (SignatureNames.compiled signaturesCompiled).absent notFunction
          obtain ⟨expected, argumentCodes, typeCompiled, argumentsCompiled, builtinCompiled⟩ :=
            builtin_components notSignature compiled
          obtain ⟨extension, targets, argumentStore, related, argumentsEvaluation, argumentHeap, argumentInstalled, argumentFrame⟩ :=
            argumentsIH.value rfl argumentsCompiled coverage locals globals runtime heap installed
          obtain ⟨target, finalStore, resultRelated, resultEvaluation, finalHeap, finalInstalled, frame⟩ :=
            external available notFunction called typeCompiled builtinCompiled related argumentsEvaluation
              runtime argumentHeap argumentInstalled
          exact ⟨extension, target, finalStore, resultRelated, resultEvaluation, finalHeap, finalInstalled,
            argumentFrame.trans frame⟩
      | named selected argumentsEligible =>
          obtain ⟨index, code, foundSignature, foundCode, _, _⟩ :=
            compiledFunction_resolve signaturesCompiled codesCompiled selected
          obtain ⟨argumentCodes, functionCode, argumentsCompiled, argumentTypes, functionCompiled, _, rfl⟩ :=
            call_components foundSignature compiled
          have sameName : code.own.name = name := by
            simpa only [beq_iff_eq] using List.find?_some foundSignature
          rw [← sameName] at functionCompiled
          have functionEvaluation := global_read_evaluates foundCode globals installed functionCompiled
          let closure := Core.Value.closure (bundleType code.own.parameters)
            (Core.LanguageResult.resultType code.own.result) (code.body.rename (globalShift index).lift)
            (installationEnvironment captured index)
          obtain ⟨argumentExtension, targets, argumentStore, argumentsRelated,
              argumentsEvaluation, argumentHeap, argumentInstalled, argumentFrame⟩ :=
            argumentsIH.value rfl argumentsCompiled coverage (locals.prepend [closure]) (globals.prepend [closure]) (runtime.prepend [closure]) heap installed
          have values : ValuesRel code.own.parameters sources targets :=
            argumentTypes ▸ ArgumentsRel.values argumentsRelated
          obtain ⟨callExtension, target, finalStore, related, bodyEvaluation, finalHeap, finalInstalled, tailFrame⟩ :=
            callIH selected foundSignature foundCode values argumentHeap argumentInstalled
          exact ⟨argumentExtension ++ callExtension, target, finalStore, related,
            call_evaluates functionEvaluation argumentsEvaluation bodyEvaluation,
            by simpa only [List.append_assoc] using finalHeap, finalInstalled, argumentFrame.trans tailFrame⟩


/-- Failed arguments preserve their actual heap and skip both builtin bodies
and named function invocation. The named closure read still precedes the pack. -/
theorem call_fault {supported : String → Prop} {σ : Type} {model : StateModel σ} {slots : List EffectSlot} {functions : List Function}
    {compilationFuel : Nat} {signatures : List Signature} {programScope : Scope}
    {codes : List GlobalCode} {locations : Nat → Nat} {captured : Core.Environment}
    (signaturesCompiled : functions.mapM (signature compilationFuel) = .ok signatures)
    (codesCompiled : CompiledGlobals compilationFuel signatures programScope (functions.zip signatures).reverse codes)
    {sourceEnvironment : Semantics.Environment} {type : Ty} {name : String} {arguments : List Expr}
    {span : Option Span} {initial final : Semantics.State σ} {reason : Semantics.Fault}
    (eligible : ExecutableExpression supported functions ⟨type, .call name arguments, span⟩)
    (argumentsIH : ExprsSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment arguments
      initial (.fault reason) final) :
    ExprSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment
      ⟨type, .call name arguments, span⟩ initial (.fault reason) final := by
  intro fuel scope lowered compiled coverage world mapping environment store locals globals runtime heap installed
  cases fuel with
  | zero => simp [lowerExpression, fail] at compiled
  | succ fuel =>
      cases eligible with
      | builtin classified notFunction argumentsEligible =>
          have notSignature := (SignatureNames.compiled signaturesCompiled).absent notFunction
          obtain ⟨expected, argumentCodes, typeCompiled, argumentsCompiled, builtinCompiled⟩ :=
            builtin_components notSignature compiled
          obtain ⟨extension, target, finalStore, related, argumentsEvaluation, finalHeap, finalInstalled, frame⟩ :=
            argumentsIH argumentsCompiled coverage locals globals runtime heap installed
          cases related
          rename_i reason
          exact ⟨extension, _, finalStore, .language reason,
            BuiltinCorrespondence.argument_failure builtinCompiled argumentsEvaluation,
            finalHeap, finalInstalled, frame⟩
      | external available notFunction argumentsEligible =>
          have notSignature := (SignatureNames.compiled signaturesCompiled).absent notFunction
          obtain ⟨expected, argumentCodes, typeCompiled, argumentsCompiled, builtinCompiled⟩ :=
            builtin_components notSignature compiled
          obtain ⟨extension, target, finalStore, related, argumentsEvaluation, finalHeap, finalInstalled, frame⟩ :=
            argumentsIH argumentsCompiled coverage locals globals runtime heap installed
          cases related
          rename_i reason
          exact ⟨extension, _, finalStore, .language reason,
            BuiltinCorrespondence.argument_failure builtinCompiled argumentsEvaluation,
            finalHeap, finalInstalled, frame⟩
      | named selected argumentsEligible =>
          obtain ⟨index, code, foundSignature, foundCode, _, _⟩ :=
            compiledFunction_resolve signaturesCompiled codesCompiled selected
          obtain ⟨argumentCodes, functionCode, argumentsCompiled, argumentTypes, functionCompiled, _, rfl⟩ :=
            call_components foundSignature compiled
          have sameName : code.own.name = name := by
            simpa only [beq_iff_eq] using List.find?_some foundSignature
          rw [← sameName] at functionCompiled
          have functionEvaluation := global_read_evaluates foundCode globals installed functionCompiled
          let closure := Core.Value.closure (bundleType code.own.parameters)
            (Core.LanguageResult.resultType code.own.result) (code.body.rename (globalShift index).lift)
            (installationEnvironment captured index)
          obtain ⟨extension, target, finalStore, related, argumentsEvaluation, finalHeap, finalInstalled, frame⟩ :=
            argumentsIH argumentsCompiled coverage (locals.prepend [closure]) (globals.prepend [closure]) (runtime.prepend [closure]) heap installed
          cases related
          rename_i reason
          exact ⟨extension, _, finalStore, .language reason,
            call_argument_failure functionEvaluation argumentsEvaluation,
            finalHeap, finalInstalled, frame⟩

end Solcore.Frontend.RustHull.DerivationCallCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.DerivationExpressionCorrespondence
/-! Structural expression simulation consumes only the child executions in a
finite independent Hull derivation. Named calls may recur in those children. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.DerivationCorrespondence
open Correspondence StatementCorrespondence ContextualExpressionCorrespondence

theorem pair {σ : Type} {model : StateModel σ} {slots : List EffectSlot} {signatures : List Signature} {codes : List GlobalCode}
    {locations : Nat → Nat} {captured : Core.Environment} {sourceEnvironment : Semantics.Environment}
    {initial middle final : Semantics.State σ} {left right : Expr}
    {leftValue : Semantics.Value} {rightResult : Semantics.Result Semantics.Value}
    (leftPreserves : ExprSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment left initial (.value leftValue) middle)
    (rightPreserves : ExprSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment right middle rightResult final)
    (type : Ty) (span : Option Span) :
    ExprSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment ⟨type, .pair left right, span⟩
      initial (rightResult.map (Semantics.Value.pair leftValue)) final := by
  intro fuel scope lowered compiled covered world mapping environment store environmentRelated globals runtime heap externalRelated
  cases fuel with
  | zero => simp [lowerExpression, fail] at compiled
  | succ fuel =>
      obtain ⟨leftCode, rightCode, leftCompiled, rightCompiled, rfl⟩ :=
        lowerExpression_pair_components compiled
      obtain ⟨leftExtension, targetLeft, middleStore, leftRelated, leftEvaluation, middleHeap, middleExternal, firstFrame⟩ :=
        leftPreserves.value rfl leftCompiled covered environmentRelated globals runtime heap externalRelated
      have middleEnvironment := (environmentRelated.extendWorld leftExtension).prepend [targetLeft]
      obtain ⟨rightExtension, targetRight, finalStore, rightRelated, rightEvaluation, finalHeap, finalExternal, lastFrame⟩ :=
        rightPreserves rightCompiled covered middleEnvironment (globals.prepend [targetLeft]) (runtime.prepend [targetLeft]) middleHeap middleExternal
      have renamed : (rightCode.expression.rename mapping).weakenAt 0 =
          rightCode.expression.rename (fun index => 1 + mapping index) := by
        simp only [← Core.Expr.rename_insertion, Core.Expr.rename_comp]
        congr 1
        funext index
        simp [Core.Renaming.comp, Core.Renaming.insertion, Nat.add_comm]
      cases rightRelated with
      | value related =>
          refine ⟨leftExtension ++ rightExtension, .inRight .word (.pair targetLeft _), finalStore,
            .value (.pair leftRelated related), ?_, ?_, finalExternal, firstFrame.trans lastFrame⟩
          · rw [pair_rename]
            apply Core.LocalSequence.pair_success _ _ leftEvaluation
            simpa [renamed] using rightEvaluation
          · simpa only [List.append_assoc] using finalHeap
      | language reason =>
          refine ⟨leftExtension ++ rightExtension, .inLeft _ (.word reason), finalStore,
            .language reason, ?_, ?_, finalExternal, firstFrame.trans lastFrame⟩
          · rw [pair_rename]
            apply Core.LocalSequence.pair_right_failure _ _ leftEvaluation
            simpa [renamed] using rightEvaluation
          · simpa only [List.append_assoc] using finalHeap

/-- A failing first operand skips the second operand of the actual pair code. -/
theorem pair_fault {σ : Type} {model : StateModel σ} {slots : List EffectSlot} {signatures : List Signature} {codes : List GlobalCode}
    {locations : Nat → Nat} {captured : Core.Environment} {sourceEnvironment : Semantics.Environment}
    {initial final : Semantics.State σ} {left right : Expr} {reason : Semantics.Fault}
    (preserves : ExprSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment left initial (.fault reason) final)
    (type : Ty) (span : Option Span) :
    ExprSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment ⟨type, .pair left right, span⟩
      initial (.fault reason) final := by
  intro fuel scope lowered compiled covered world mapping environment store locals globals runtime heap installed
  cases fuel with
  | zero => simp [lowerExpression, fail] at compiled
  | succ fuel =>
      obtain ⟨leftCode, rightCode, leftCompiled, _, rfl⟩ := lowerExpression_pair_components compiled
      obtain ⟨extension, target, finalStore, related, evaluated, finalHeap, finalInstalled, frame⟩ :=
        preserves leftCompiled covered locals globals runtime heap installed
      cases related with
      | language reason =>
          refine ⟨extension, .inLeft _ (.word reason), finalStore, .language reason,
            ?_, finalHeap, finalInstalled, frame⟩
          rw [pair_rename]
          exact Core.LocalSequence.pair_left_failure _ _ evaluated

theorem projection {σ : Type} {model : StateModel σ} {slots : List EffectSlot} {signatures : List Signature} {codes : List GlobalCode}
    {locations : Nat → Nat} {captured : Core.Environment} {sourceEnvironment : Semantics.Environment}
    {initial final : Semantics.State σ} {operand : Expr} {result : Semantics.Result Semantics.Value}
    (preserves : ExprSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment operand initial result final)
    (right : Bool) (type : Ty) (span : Option Span) :
    ExprSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment
      ⟨type, if right then .snd operand else .fst operand, span⟩ initial
      (result.bind (Semantics.projectResult right)) final := by
  intro fuel scope lowered compiled covered world mapping environment store locals globals runtime heap installed
  cases fuel with
  | zero => simp [lowerExpression, fail] at compiled
  | succ fuel =>
      obtain ⟨operandCode, leftType, rightType, operandCompiled, operandType, rfl⟩ :=
        lowerExpression_projection_components right compiled
      obtain ⟨extension, targetValue, finalStore, related, evaluation, finalHeap, finalInstalled, frame⟩ :=
        preserves operandCompiled covered locals globals runtime heap installed
      cases related with
      | language reason =>
          exact ⟨extension, .inLeft _ (.word reason), finalStore, .language reason,
            Core.LanguageResult.bind_failure _ evaluation, finalHeap, finalInstalled, frame⟩
      | value related =>
          rw [operandType] at related
          cases related with
          | pair leftRelated rightRelated =>
              cases right <;> simp only [Semantics.Result.bind, Semantics.projectResult,
                Bool.false_eq_true, ↓reduceIte]
              · exact ⟨extension, .inRight .word _, finalStore, .value leftRelated,
                  Core.LanguageResult.bind_success _ evaluation (.inRight (.first (.var rfl))),
                  finalHeap, finalInstalled, frame⟩
              · exact ⟨extension, .inRight .word _, finalStore, .value rightRelated,
                  Core.LanguageResult.bind_success _ evaluation (.inRight (.second (.var rfl))),
                  finalHeap, finalInstalled, frame⟩

theorem injection {σ : Type} {model : StateModel σ} {slots : List EffectSlot} {signatures : List Signature} {codes : List GlobalCode}
    {locations : Nat → Nat} {captured : Core.Environment} {sourceEnvironment : Semantics.Environment}
    {initial final : Semantics.State σ} {operand : Expr} {result : Semantics.Result Semantics.Value}
    (preserves : ExprSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment operand initial result final)
    (right : Bool) (type target : Ty) (span : Option Span) :
    ExprSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment
      ⟨type, if right then .inr target operand else .inl target operand, span⟩ initial
      (result.bind (Semantics.sumInjectionResult right target)) final := by
  intro fuel scope lowered compiled covered world mapping environment store locals globals runtime heap installed
  cases fuel with
  | zero => simp [lowerExpression, fail] at compiled
  | succ fuel =>
      obtain ⟨operandCode, leftType, rightType, targetCompiled, operandCompiled, operandType, rfl⟩ :=
        lowerExpression_injection_components right compiled
      obtain ⟨extension, targetValue, finalStore, related, evaluation, finalHeap, finalInstalled, frame⟩ :=
        preserves operandCompiled covered locals globals runtime heap installed
      cases related with
      | language reason =>
          exact ⟨extension, .inLeft _ (.word reason), finalStore, .language reason,
            Core.LanguageResult.bind_failure _ evaluation, finalHeap, finalInstalled, frame⟩
      | @value sourceValue targetValue related =>
          obtain ⟨shape, sourceShape, targetShape⟩ := lowerType_shape targetCompiled
          cases shape <;> try { cases targetShape }
          rename_i leftShape rightShape
          have injected : Semantics.sumInjectionResult right target sourceValue =
              .value (if right then .inr sourceValue else .inl sourceValue) := by
            simp [Semantics.sumInjectionResult, sourceShape]
          simp only [Semantics.Result.bind, injected]
          rw [operandType] at related
          cases right <;> simp only [Bool.false_eq_true, ↓reduceIte] at related ⊢
          · exact ⟨extension, .inRight .word (.inLeft rightType _), finalStore, .value (.inl related),
              Core.LanguageResult.bind_success _ evaluation (.inRight (.inLeft (.var rfl))),
              finalHeap, finalInstalled, frame⟩
          · exact ⟨extension, .inRight .word (.inRight leftType _), finalStore, .value (.inr related),
              Core.LanguageResult.bind_success _ evaluation (.inRight (.inRight (.var rfl))),
              finalHeap, finalInstalled, frame⟩

theorem conditional {σ : Type} {model : StateModel σ} {slots : List EffectSlot} {signatures : List Signature} {codes : List GlobalCode}
    {locations : Nat → Nat} {captured : Core.Environment} {sourceEnvironment : Semantics.Environment}
    {initial middle final : Semantics.State σ} {conditionExpr yes no : Expr}
    {conditionValue : Semantics.Value} {result : Semantics.Result Semantics.Value}
    (truth : Bool) (tested : Semantics.condition? conditionValue = some truth)
    (conditionPreserves : ExprSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment conditionExpr initial (.value conditionValue) middle)
    (branchPreserves : ExprSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment (if truth then yes else no) middle result final)
    (type target : Ty) (span : Option Span) :
    ExprSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment
      ⟨type, .ifThen target conditionExpr yes no, span⟩ initial result final := by
  intro fuel scope lowered compiled covered world mapping environment store environmentRelated globals runtime heap externalRelated
  cases fuel with
  | zero => simp [lowerExpression, fail] at compiled
  | succ fuel =>
      obtain ⟨conditionCode, test, yesCode, noCode, conditionCompiled, testCompiled,
        yesCompiled, noCompiled, yesType, noType, expressionEqual⟩ :=
        lowerExpression_conditional_components compiled
      obtain ⟨conditionExtension, targetCondition, middleStore, conditionRelated,
        conditionEvaluation, middleHeap, middleExternal, firstFrame⟩ :=
        conditionPreserves.value rfl conditionCompiled covered environmentRelated globals runtime heap externalRelated
      have testEvaluation := ExpressionCorrespondence.condition_evaluates
        testCompiled conditionRelated tested conditionEvaluation
      have middleEnvironment :=
        (environmentRelated.extendWorld conditionExtension).prepend [.bool truth]
      have branchCompiled : lowerExpression fuel signatures scope (if truth then yes else no) =
          .ok (if truth then yesCode else noCode) := by cases truth <;> assumption
      obtain ⟨branchExtension, targetValue, finalStore, related, branchEvaluation, finalHeap, finalExternal, lastFrame⟩ :=
        branchPreserves branchCompiled covered middleEnvironment (globals.prepend [.bool truth]) (runtime.prepend [.bool truth]) middleHeap middleExternal
      refine ⟨conditionExtension ++ branchExtension, targetValue, finalStore, ?_, ?_, ?_, finalExternal, firstFrame.trans lastFrame⟩
      · cases truth <;> simpa only [Bool.false_eq_true, ↓reduceIte, yesType, noType] using related
      · have renamed (expression : Core.Expr) : (expression.rename mapping).weakenAt 0 =
            expression.rename (fun index => 1 + mapping index) := by
          simp only [← Core.Expr.rename_insertion, Core.Expr.rename_comp]
          congr 1
          funext index
          simp [Core.Renaming.comp, Core.Renaming.insertion, Nat.add_comm]
        rw [expressionEqual, choose_rename]
        cases truth with
        | false =>
            apply Core.LocalControl.choose_false _ testEvaluation
            simpa [renamed] using branchEvaluation
        | true =>
            apply Core.LocalControl.choose_true _ testEvaluation
            simpa [renamed] using branchEvaluation
      · simpa only [List.append_assoc] using finalHeap

theorem indexedInjection {σ : Type} {model : StateModel σ} {slots : List EffectSlot} {signatures : List Signature} {codes : List GlobalCode}
    {locations : Nat → Nat} {captured : Core.Environment} {sourceEnvironment : Semantics.Environment}
    {initial final : Semantics.State σ} {operand : Expr} {result : Semantics.Result Semantics.Value}
    (preserves : ExprSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment operand initial result final)
    (index : Nat) (type target : Ty) (span : Option Span) :
    ExprSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment
      ⟨type, .inK index target operand, span⟩ initial (result.bind (Semantics.injectionResult index target)) final := by
  intro fuel scope lowered compiled covered world mapping environment store locals globals runtime heap installed
  cases fuel with
  | zero => simp [lowerExpression, fail] at compiled
  | succ fuel =>
      obtain ⟨operandCode, targetType, injected, targetCompiled, operandCompiled, injectionCompiled, rfl⟩ :=
        lowerExpression_indexedInjection_components compiled
      obtain ⟨extension, targetValue, finalStore, related, evaluation, finalHeap, finalInstalled, frame⟩ :=
        preserves operandCompiled covered locals globals runtime heap installed
      cases related with
      | language reason =>
          exact ⟨extension, .inLeft _ (.word reason), finalStore, .language reason,
            Core.LanguageResult.bind_failure _ evaluation, finalHeap, finalInstalled, frame⟩
      | @value sourceValue targetValue related =>
          obtain ⟨shape, sourceShape, targetShape⟩ := lowerType_shape targetCompiled
          rw [← targetShape] at injectionCompiled
          have supplied : Core.Evaluates (targetValue :: environment) finalStore
              ((Core.Expr.var 0).rename (Core.Renaming.lift mapping)) targetValue finalStore := .var rfl
          obtain ⟨sourceInjected, targetInjected, sourceInjection, injectionRelated, injectionEvaluation⟩ :=
            PureExpressionCorrespondence.inject_evaluates shape related injectionCompiled supplied
          refine ⟨extension, .inRight .word targetInjected, finalStore, ?_, ?_, finalHeap, finalInstalled, frame⟩
          · simpa [Semantics.Result.bind, Semantics.injectionResult, Semantics.inject?,
              sourceShape, sourceInjection, targetShape] using ResultRel.value injectionRelated
          · exact Core.LanguageResult.bind_success _ evaluation (.inRight injectionEvaluation)

/-- A failing condition skips both branches and preserves the condition's heap. -/
theorem conditional_fault {σ : Type} {model : StateModel σ} {slots : List EffectSlot} {signatures : List Signature} {codes : List GlobalCode}
    {locations : Nat → Nat} {captured : Core.Environment} {sourceEnvironment : Semantics.Environment}
    {initial final : Semantics.State σ} {conditionExpr yes no : Expr} {reason : Semantics.Fault}
    (preserves : ExprSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment conditionExpr initial (.fault reason) final)
    (type target : Ty) (span : Option Span) :
    ExprSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment
      ⟨type, .ifThen target conditionExpr yes no, span⟩ initial (.fault reason) final := by
  intro fuel scope lowered compiled covered world mapping environment store locals globals runtime heap installed
  cases fuel with
  | zero => simp [lowerExpression, fail] at compiled
  | succ fuel =>
      obtain ⟨conditionCode, test, yesCode, noCode, conditionCompiled, testCompiled,
        _, _, _, _, expressionEqual⟩ := lowerExpression_conditional_components compiled
      obtain ⟨extension, value, finalStore, related, evaluated, finalHeap, finalInstalled, frame⟩ :=
        preserves conditionCompiled covered locals globals runtime heap installed
      cases related with
      | language reason =>
          refine ⟨extension, .inLeft _ (.word reason), finalStore, .language reason,
            ?_, finalHeap, finalInstalled, frame⟩
          rw [expressionEqual, choose_rename]
          exact Core.LocalControl.choose_failure _
            (ExpressionCorrespondence.condition_failure testCompiled evaluated)

/-- A compiled condition whose operand has a represented value cannot produce
the independent semantics' malformed-condition observation. -/
theorem conditional_invalid {σ : Type} {model : StateModel σ} {slots : List EffectSlot} {signatures : List Signature} {codes : List GlobalCode}
    {locations : Nat → Nat} {captured : Core.Environment} {sourceEnvironment : Semantics.Environment}
    {initial final : Semantics.State σ} {conditionExpr yes no : Expr} {sourceValue : Semantics.Value}
    (preserves : ExprSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment conditionExpr initial (.value sourceValue) final)
    (invalid : Semantics.condition? sourceValue = none) (type target : Ty) (span : Option Span) :
    ExprSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment
      ⟨type, .ifThen target conditionExpr yes no, span⟩ initial
      (.fault (.invalidValue "condition")) final := by
  intro fuel scope lowered compiled covered world mapping environment store locals globals runtime heap installed
  cases fuel with
  | zero => simp [lowerExpression, fail] at compiled
  | succ fuel =>
      obtain ⟨conditionCode, test, _, _, conditionCompiled, testCompiled, _⟩ :=
        lowerExpression_conditional_components compiled
      obtain ⟨_, _, _, related, _⟩ := preserves.value rfl conditionCompiled covered locals globals runtime heap installed
      obtain ⟨truth, valid⟩ := condition_valid testCompiled related
      rw [invalid] at valid
      cases valid

end Solcore.Frontend.RustHull.DerivationCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.DerivationStatementCorrespondence
/-! Statement steps consume simulation hypotheses for the particular source
subderivations. They do not assume a rank on calls or a universal expression
preservation theorem. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.DerivationStatementCorrespondence
open Correspondence StatementCorrespondence DerivationCorrespondence

variable {σ : Type} {model : StateModel σ} {slots : List EffectSlot} {signatures : List Signature}
  {codes : List GlobalCode} {locations : Nat → Nat} {captured : Core.Environment}
  {sourceEnvironment : Semantics.Environment}

/-- The actual compiler checks a local or nested product path. The root is
read after the RHS finishes, and only the selected component is replaced. -/
theorem assign {statement : Stmt} {lhs rhs : Expr}
    {initial middle final : Semantics.State σ} {sourceValue : Semantics.Value}
    (kind : statement.kind = .assign lhs rhs)
    (right : ExprSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment rhs initial (.value sourceValue) middle)
    (assigned : Semantics.assignResult sourceEnvironment middle lhs sourceValue = .value final) :
    StmtSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment statement initial .fallthrough final := by
  intro fuel scope result loops expression compiled covered world mapping environment store
    environmentRelated globalsRelated runtime heapRelated installed
  cases statement with | mk statementKind span =>
  cases kind
  cases fuel with
  | zero => simp [lowerStatement, fail] at compiled
  | succ fuel =>
      obtain ⟨lowered, name, path, binding, index, updated, rightCompiled, placed,
          looked, _, selected, updatedCompiled, rfl⟩ := assignment_components compiled
      obtain ⟨extension, value, middleStore, valueRelated, evaluated, middleHeap, middleInstalled, firstFrame⟩ :=
        right.value rfl rightCompiled covered environmentRelated globalsRelated runtime heapRelated installed
      obtain ⟨sourceLocation, sourceOld, sourceUpdated, found, read, updateSource, rfl⟩ :=
        assignment_source placed assigned
      obtain ⟨location, entry, _, targetFound⟩ :=
        (environmentRelated.extendWorld extension) name sourceLocation binding index found looked
      obtain ⟨oldValue, targetRead, oldRelated⟩ := middleHeap.read entry read
      have updatedRenamed : updateProduct path binding.type (.var 0) (.var 1) =
          .ok (updated.rename (Core.Renaming.lift (Core.Renaming.lift mapping))) :=
        updateProduct_rename updatedCompiled (Core.Renaming.lift (Core.Renaming.lift mapping))
      have oldEvaluated : Core.Evaluates (oldValue :: value :: environment) middleStore
          (.var 0) oldValue middleStore := .var rfl
      have valueEvaluated : Core.Evaluates (oldValue :: value :: environment) middleStore
          (.var 1) value middleStore := .var rfl
      obtain ⟨newValue, newRelated, updatedEvaluated⟩ :=
        updateProduct_evaluates updatedRenamed selected oldRelated valueRelated updateSource oldEvaluated valueEvaluated
      have written : middleStore.write? location (.inRight .unit newValue) =
          some (middleStore.set location (.inRight .unit newValue)) :=
        Core.Store.write?_eq_some_iff.mpr ⟨middleHeap.location_bound entry, rfl⟩
      exact ⟨extension, _, _, .fallthrough, assignment_core evaluated targetFound targetRead updatedEvaluated written,
        middleHeap.write entry newRelated written, middleInstalled.write middleHeap.toHeapRel entry written,
        firstFrame.trans (ClosuresPreserved.write middleHeap.toHeapRel entry written)⟩

theorem returned {statement : Stmt} {value : Expr} {initial final : Semantics.State σ}
    {sourceValue : Semantics.Value} (kind : statement.kind = .returnStmt value)
    (preserves : ExprSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment value initial (.value sourceValue) final) :
    StmtSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment statement initial (.returned sourceValue) final := by
  intro fuel scope type loops expression compiled covered world mapping environment store
    environmentRelated globalsRelated runtime heapRelated installed
  cases statement with | mk statementKind span =>
  cases kind
  cases fuel with
  | zero => simp [lowerStatement, fail] at compiled
  | succ fuel =>
      have components := compiled
      simp only [lowerStatement] at components
      obtain ⟨lowered, valueCompiled, components⟩ := lower_bind_eq_ok.mp components
      obtain ⟨checked, matched, _⟩ := lower_bind_eq_ok.mp components
      cases checked
      have sameType := expectType_eq_of_ok matched
      obtain ⟨extension, targetValue, finalStore, valueRelated, evaluated, finalHeap, finalInstalled, lastFrame⟩ :=
        preserves.value rfl valueCompiled covered environmentRelated globalsRelated runtime heapRelated installed
      exact ⟨extension, Core.LocalLoop.returnedValue targetValue, finalStore,
        .returned (sameType ▸ valueRelated), return_success compiled valueCompiled evaluated,
        finalHeap, finalInstalled, lastFrame⟩

theorem expression_statement {statement : Stmt} {value : Expr} {initial final : Semantics.State σ}
    {sourceValue : Semantics.Value} (kind : statement.kind = .expression value)
    (preserves : ExprSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment value initial (.value sourceValue) final) :
    StmtSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment statement initial .fallthrough final := by
  intro fuel scope type loops expression compiled covered world mapping environment store
    environmentRelated globalsRelated runtime heapRelated installed
  cases statement with | mk statementKind span =>
  cases kind
  cases fuel with
  | zero => simp [lowerStatement, fail] at compiled
  | succ fuel =>
      simp only [lowerStatement] at compiled
      obtain ⟨lowered, valueCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
      cases returned
      obtain ⟨extension, targetValue, finalStore, _, evaluated, finalHeap, finalInstalled, lastFrame⟩ :=
        preserves.value rfl valueCompiled covered environmentRelated globalsRelated runtime heapRelated installed
      refine ⟨extension, _, finalStore, .fallthrough, ?_, finalHeap, finalInstalled, lastFrame⟩
      apply Core.LanguageResult.bind_success _ evaluated
      simpa only [← Core.Expr.rename_insertion, rename_fallthrough] using
        Core.LocalLoop.fallthrough_evaluates type (targetValue :: environment) finalStore

/-- A failed RHS leaves the target untouched and skips its cell read/write. -/
theorem assign_fault {statement : Stmt} {lhs rhs : Expr}
    {initial final : Semantics.State σ} {reason : Semantics.Fault}
    (kind : statement.kind = .assign lhs rhs)
    (right : ExprSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment rhs initial (.fault reason) final) :
    StmtSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment statement initial (.fault reason) final := by
  intro fuel scope result loops expression compiled covered world mapping environment store locals globals runtime heap installed
  cases statement with | mk statementKind span =>
  cases kind
  cases fuel with
  | zero => simp [lowerStatement, fail] at compiled
  | succ fuel =>
      obtain ⟨lowered, name, path, binding, index, updated, rightCompiled,
          _, _, _, _, _, rfl⟩ := assignment_components compiled
      obtain ⟨extension, target, finalStore, related, executed, finalHeap, finalInstalled, frame⟩ :=
        right rightCompiled covered locals globals runtime heap installed
      cases related with
      | language reason =>
          exact ⟨extension, _, finalStore, .language reason,
            Core.LanguageResult.bind_failure _ executed, finalHeap, finalInstalled, frame⟩

theorem return_fault {statement : Stmt} {value : Expr} {initial final : Semantics.State σ}
    {reason : Semantics.Fault} (kind : statement.kind = .returnStmt value)
    (preserves : ExprSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment value initial (.fault reason) final) :
    StmtSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment statement initial (.fault reason) final := by
  intro fuel scope type loops expression compiled covered world mapping environment store locals globals runtime heap installed
  cases statement with | mk statementKind span =>
  cases kind
  cases fuel with
  | zero => simp [lowerStatement, fail] at compiled
  | succ fuel =>
      simp only [lowerStatement] at compiled
      obtain ⟨lowered, valueCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
      obtain ⟨checked, matched, returned⟩ := lower_bind_eq_ok.mp compiled
      cases checked
      cases returned
      have sameType := expectType_eq_of_ok matched
      obtain ⟨extension, target, finalStore, related, executed, finalHeap, finalInstalled, frame⟩ :=
        preserves valueCompiled covered locals globals runtime heap installed
      cases related with
      | language reason =>
          exact ⟨extension, _, finalStore, .language reason,
            Core.LanguageResult.bind_failure _ executed, finalHeap, finalInstalled, frame⟩

theorem expression_fault {statement : Stmt} {value : Expr} {initial final : Semantics.State σ}
    {reason : Semantics.Fault} (kind : statement.kind = .expression value)
    (preserves : ExprSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment value initial (.fault reason) final) :
    StmtSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment statement initial (.fault reason) final := by
  intro fuel scope type loops expression compiled covered world mapping environment store locals globals runtime heap installed
  cases statement with | mk statementKind span =>
  cases kind
  cases fuel with
  | zero => simp [lowerStatement, fail] at compiled
  | succ fuel =>
      simp only [lowerStatement] at compiled
      obtain ⟨lowered, valueCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
      cases returned
      obtain ⟨extension, target, finalStore, related, executed, finalHeap, finalInstalled, frame⟩ :=
        preserves valueCompiled covered locals globals runtime heap installed
      cases related with
      | language reason =>
          exact ⟨extension, _, finalStore, .language reason,
            Core.LanguageResult.bind_failure _ executed, finalHeap, finalInstalled, frame⟩

/-- A successful RHS leaves a represented heap. The checked assignment path
therefore has a source update, excluding every malformed assignment outcome. -/
theorem assign_invalid {statement : Stmt} {lhs rhs : Expr}
    {initial middle : Semantics.State σ} {sourceValue : Semantics.Value} {reason : Semantics.Fault}
    (kind : statement.kind = .assign lhs rhs)
    (right : ExprSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment rhs initial (.value sourceValue) middle)
    (invalid : Semantics.assignResult sourceEnvironment middle lhs sourceValue = .fault reason) :
    StmtSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment statement initial (.fault reason) middle := by
  intro fuel scope result loops expression compiled covered world mapping environment store locals globals runtime heap installed
  cases statement with | mk statementKind span =>
  cases kind
  cases fuel with
  | zero => simp [lowerStatement, fail] at compiled
  | succ fuel =>
      obtain ⟨lowered, name, path, binding, index, updated, rightCompiled, _⟩ := assignment_components compiled
      obtain ⟨extension, value, middleStore, _, _, middleHeap, _, _⟩ :=
        right.value rfl rightCompiled covered locals globals runtime heap installed
      obtain ⟨finalState, assigned⟩ := assignment_valid (value := sourceValue) compiled covered
        (locals.extendWorld extension) middleHeap.toHeapRel
      rw [invalid] at assigned
      cases assigned

/-- The accepted initializer supplies a source zero value, so a malformed
source declaration cannot occur in a compiled statement list. -/
theorem declare_invalid {statement : Stmt} {rest : List Stmt} {name : String} {type : Ty}
    {state : Semantics.State σ} (kind : statement.kind = .letDecl name type)
    (invalid : Semantics.zero? type = none) :
    StatementsSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment (statement :: rest)
      state (.fault .unsupportedType) state := by
  intro fuel scope result loops expression compiled
  cases statement with | mk statementKind span =>
  cases kind
  cases fuel with
  | zero => simp [lowerStatements, fail] at compiled
  | succ fuel =>
      obtain ⟨localType, initializer, body, typeCompiled, _⟩ := declaration_components compiled
      obtain ⟨shape, sourceShape, _⟩ := lowerType_shape typeCompiled
      simp [Semantics.zero?, sourceShape] at invalid

theorem declared_invalid {statement : Stmt} {name : String} {type : Ty}
    {state : Semantics.State σ} (kind : statement.kind = .letDecl name type)
    (invalid : Semantics.zero? type = none) :
    StmtSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment statement state (.fault .unsupportedType) state := by
  intro fuel scope result loops expression compiled
  cases statement with | mk statementKind span =>
  cases kind
  cases fuel with
  | zero => simp [lowerStatement, fail] at compiled
  | succ fuel => exact declare_invalid rfl invalid compiled

theorem comment {statement : Stmt} {text : String} {state : Semantics.State σ}
    (kind : statement.kind = .comment text) :
    StmtSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment statement state .fallthrough state := by
  intro fuel scope type loops expression compiled covered world mapping environment store
    _ _ _ heapRelated installed
  cases statement with | mk statementKind span =>
  cases kind
  cases fuel with
  | zero => simp [lowerStatement, fail] at compiled
  | succ fuel =>
      simp only [lowerStatement] at compiled
      cases compiled
      exact ⟨[], _, store, .fallthrough, Core.LocalLoop.fallthrough_evaluates _ _ _,
        by simpa only [List.append_nil] using heapRelated, installed, ClosuresPreserved.refl store⟩

theorem nil {state : Semantics.State σ} :
    StatementsSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment [] state .fallthrough state := by
  intro fuel scope type loops expression compiled covered world mapping environment store
    _ _ _ heapRelated installed
  exact ⟨[], _, store, .fallthrough, empty compiled mapping environment store,
    by simpa only [List.append_nil] using heapRelated, installed, ClosuresPreserved.refl store⟩

theorem declare {statement : Stmt} {rest : List Stmt} {name : String} {sourceType : Ty}
    {sourceValue : Semantics.Value} {initial final : Semantics.State σ} {control : Semantics.Control}
    (kind : statement.kind = .letDecl name sourceType) (zero : Semantics.zero? sourceType = some sourceValue)
    (tail : StatementsSimulation (model := model) (slots := slots) signatures codes locations captured
      ((name, initial.heap.length) :: sourceEnvironment) rest (Semantics.allocate initial sourceValue).2 control final) :
    StatementsSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment (statement :: rest) initial control final := by
  intro fuel scope type loops expression compiled covered world mapping environment store
    environmentRelated globalsRelated runtime heapRelated installed
  cases statement with | mk statementKind span =>
  cases kind
  cases fuel with
  | zero => simp [lowerStatements, fail] at compiled
  | succ fuel =>
      have allowed := ContextualStatementCorrespondence.declaration_allowed compiled
      obtain ⟨localType, initializer, body, typeCompiled, zeroCompiled, bodyCompiled, rfl⟩ :=
        declaration_components compiled
      obtain ⟨shape, shapeFound, rfl⟩ := lowerType_shape typeCompiled
      have zeroEqual : sourceValue = shape.zero := by
        simpa only [Semantics.zero?, shapeFound, Option.map_some, Option.some.injEq] using zero.symm
      obtain ⟨value, valueRelated, evaluated⟩ := zeroValue_evaluates shape zeroCompiled environment store
      have allocated := heapRelated.allocate (zeroEqual ▸ valueRelated)
      have entry : (world ++ [(coreType shape, store.length)])[initial.heap.length]? =
          some (coreType shape, store.length) := by
        rw [← heapRelated.length_eq, List.getElem?_concat_length]
      have environmentExtended :=
        (environmentRelated.extendWorld [(coreType shape, store.length)]).addLocal
          name (coreType shape) initial.heap.length store.length entry
      have globalsExtended := globalsRelated.addLocal name (coreType shape)
        (.cellRef (Core.OptionalCell.cellType (coreType shape)) store.length) allowed
      obtain ⟨extension, targetValue, finalStore, related, bodyEvaluated, finalHeap, finalInstalled, lastFrame⟩ :=
        tail bodyCompiled (covered.addLocal name (coreType shape) initial.heap.length) environmentExtended globalsExtended
          (runtime.addLocal name (coreType shape) (.cellRef (Core.OptionalCell.cellType (coreType shape)) store.length) allowed) allocated (installed.append _)
      refine ⟨[(coreType shape, store.length)] ++ extension, targetValue, finalStore,
        related, ?_, ?_, finalInstalled, ClosuresPreserved.trans (ClosuresPreserved.append _ _) lastFrame⟩
      · have initialized := Core.OptionalCell.allocateInitialized_evaluates (type := coreType shape) evaluated
        have same := zeroValue_rename shape zeroCompiled mapping
        simpa only [Core.Expr.rename, Core.OptionalCell.allocateInitialized, same] using
          Core.Evaluates.letE initialized bodyEvaluated
      · simpa only [List.append_assoc] using finalHeap

theorem next {statement : Stmt} {rest : List Stmt} {initial middle final : Semantics.State σ}
    {control : Semantics.Control}
    (notDeclaration : ∀ name type, statement.kind ≠ .letDecl name type)
    (head : StmtSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment statement initial .fallthrough middle)
    (tail : StatementsSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment rest middle control final) :
    StatementsSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment (statement :: rest) initial control final := by
  intro fuel scope type loops expression compiled covered world mapping environment store
    environmentRelated globalsRelated runtime heapRelated installed
  cases fuel with
  | zero => simp [lowerStatements, fail] at compiled
  | succ fuel =>
      obtain ⟨first, next, firstCompiled, nextCompiled, rfl⟩ := sequence_components notDeclaration compiled
      obtain ⟨firstExtension, firstValue, middleStore, firstRelated, firstEvaluated, middleHeap, middleInstalled, firstFrame⟩ :=
        head firstCompiled covered environmentRelated globalsRelated runtime heapRelated installed
      cases firstRelated
      have nextEnvironment : EnvironmentRel (world ++ firstExtension) sourceEnvironment scope
          (fun index => mapping index + 3)
          (.unit :: .inLeft type .unit :: .inLeft Core.LocalLoop.transferType (.inLeft type .unit) :: environment) := by
        simpa only [List.length_cons, List.length_nil, Nat.zero_add, Nat.add_comm, List.cons_append,
          List.nil_append] using
          (environmentRelated.extendWorld firstExtension).prepend
            [.unit, .inLeft type .unit, .inLeft Core.LocalLoop.transferType (.inLeft type .unit)]
      have nextGlobals : GlobalEnvironmentRel codes locations scope
          (fun index => mapping index + 3)
          (.unit :: .inLeft type .unit :: .inLeft Core.LocalLoop.transferType (.inLeft type .unit) :: environment) := by
        simpa only [List.length_cons, List.length_nil, Nat.zero_add, Nat.add_comm, List.cons_append,
          List.nil_append] using globalsRelated.prepend
            [.unit, .inLeft type .unit, .inLeft Core.LocalLoop.transferType (.inLeft type .unit)]
      obtain ⟨extension, targetValue, finalStore, related, nextEvaluated, finalHeap, finalInstalled, lastFrame⟩ :=
        tail nextCompiled covered nextEnvironment nextGlobals
          (by simpa only [Nat.add_comm, List.length_cons, List.length_nil, Nat.zero_add, List.cons_append, List.nil_append]
            using runtime.prepend [.unit, .inLeft type .unit,
              .inLeft Core.LocalLoop.transferType (.inLeft type .unit)]) middleHeap middleInstalled
      exact ⟨firstExtension ++ extension, targetValue, finalStore, related,
        sequence_fallthrough firstEvaluated nextEvaluated,
        by simpa only [List.append_assoc] using finalHeap, finalInstalled, firstFrame.trans lastFrame⟩

theorem stop {statement : Stmt} {rest : List Stmt} {initial final : Semantics.State σ}
    {control : Semantics.Control}
    (notDeclaration : ∀ name type, statement.kind ≠ .letDecl name type)
    (head : StmtSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment statement initial control final)
    (stopped : control ≠ .fallthrough) :
    StatementsSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment (statement :: rest) initial control final := by
  intro fuel scope type loops expression compiled covered world mapping environment store
    environmentRelated globalsRelated runtime heapRelated installed
  cases fuel with
  | zero => simp [lowerStatements, fail] at compiled
  | succ fuel =>
      obtain ⟨first, next, firstCompiled, _, rfl⟩ := sequence_components notDeclaration compiled
      obtain ⟨extension, targetValue, finalStore, related, evaluated, finalHeap, finalInstalled, lastFrame⟩ :=
        head firstCompiled covered environmentRelated globalsRelated runtime heapRelated installed
      refine ⟨extension, targetValue, finalStore, related, ?_, finalHeap, finalInstalled, lastFrame⟩
      rw [rename_sequence]
      cases related with
      | fallthrough => exact False.elim (stopped rfl)
      | returned valueRelated => exact Core.LocalLoop.sequence_returned type evaluated
      | breaking => exact Core.LocalLoop.sequence_transfer type evaluated
      | continuing => exact Core.LocalLoop.sequence_transfer type evaluated
      | language => exact Core.LocalLoop.sequence_failure type evaluated

/-- The standalone declaration compiler delegates to its actual singleton
statement-list compiler. The new local remains represented in the final heap. -/
theorem declared {statement : Stmt} {name : String} {type : Ty}
    {value : Semantics.Value} (kind : statement.kind = .letDecl name type)
    (zero : Semantics.zero? type = some value) {initial : Semantics.State σ} :
    StmtSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment statement initial
      .fallthrough (Semantics.allocate initial value).2 := by
  intro fuel scope result loops expression compiled covered world mapping environment store
    locals globals runtime heap installed
  cases statement with | mk statementKind span =>
  cases kind
  cases fuel with
  | zero => simp [lowerStatement, fail] at compiled
  | succ fuel =>
      simp only [lowerStatement] at compiled
      exact declare rfl zero nil compiled covered locals globals runtime heap installed

theorem block {statement : Stmt} {body : List Stmt}
    {initial final : Semantics.State σ} {control : Semantics.Control}
    (kind : statement.kind = .block body)
    (continued : StatementsSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment body initial control final) :
    StmtSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment statement initial control final := by
  intro fuel scope result loops expression compiled
  cases statement with | mk statementKind span =>
  cases kind
  cases fuel with
  | zero => simp [lowerStatement, fail] at compiled
  | succ fuel => exact continued compiled

theorem breaking {statement : Stmt} {state : Semantics.State σ}
    (kind : statement.kind = .breakStmt) :
    StmtSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment statement state .breaking state := by
  intro fuel scope result loops expression compiled covered world mapping environment store _ _ _ heap installed
  cases statement with | mk statementKind span =>
  cases kind
  cases fuel with
  | zero => simp [lowerStatement, fail] at compiled
  | succ fuel =>
      cases loops with
      | zero => simp [lowerStatement, fail] at compiled
      | succ loops =>
          simp only [lowerStatement, Nat.add_one_ne_zero, ↓reduceIte] at compiled
          cases compiled
          exact ⟨[], _, store, .breaking, Core.LocalLoop.breaking_evaluates _ _ _,
            by simpa only [List.append_nil] using heap, installed, ClosuresPreserved.refl store⟩

theorem continuing {statement : Stmt} {state : Semantics.State σ}
    (kind : statement.kind = .continueStmt) :
    StmtSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment statement state .continuing state := by
  intro fuel scope result loops expression compiled covered world mapping environment store _ _ _ heap installed
  cases statement with | mk statementKind span =>
  cases kind
  cases fuel with
  | zero => simp [lowerStatement, fail] at compiled
  | succ fuel =>
      cases loops with
      | zero => simp [lowerStatement, fail] at compiled
      | succ loops =>
          simp only [lowerStatement, Nat.add_one_ne_zero, ↓reduceIte] at compiled
          cases compiled
          exact ⟨[], _, store, .continuing, Core.LocalLoop.continuing_evaluates _ _ _,
            by simpa only [List.append_nil] using heap, installed, ClosuresPreserved.refl store⟩

end Solcore.Frontend.RustHull.DerivationStatementCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.DerivationFunctionCorrespondence
/-! Function initialization and statement steps driven by induction hypotheses
for the particular independent source evaluation. No function rank or premise
quantifying over every source execution is needed at this boundary. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.DerivationFunctionCorrespondence
open Correspondence ScalarExecution StatementCorrespondence DerivationCorrespondence

/-- The actual parameter binder retains reserved effect references while
adding the same ordinary local names checked by the compiler. -/
theorem _root_.Solcore.Frontend.RustHull.Correspondence.ParameterCells.effectEnvironment {types : List Core.Ty}
    {values : List Core.Value} {environment finalEnvironment : Core.Environment}
    {store finalStore : Core.Store}
    (cells : ParameterCells types values environment store finalEnvironment finalStore)
    {arguments : List Arg} (arity : arguments.length = types.length)
    (allowed : ∀ argument ∈ arguments, argument.name.startsWith Effects.reservedPrefix = false)
    {slots : List EffectSlot} {scope : Scope} {mapping : Core.Renaming}
    (related : EffectEnvironmentRel slots scope mapping environment) :
    EffectEnvironmentRel slots (parameterScope arguments types scope)
      (parameterRenaming types.length mapping) finalEnvironment := by
  induction cells generalizing arguments scope mapping with
  | nil =>
      have empty : arguments = [] := List.eq_nil_of_length_eq_zero arity
      subst arguments
      exact related
  | @cons type types value values environment store finalEnvironment finalStore rest ih =>
      cases arguments with
      | nil => simp at arity
      | cons argument arguments =>
          apply ih (Nat.succ.inj arity)
            (fun arg member => allowed arg (List.mem_cons_of_mem argument member))
          exact related.addLocal argument.name type
            (.cellRef (Core.OptionalCell.cellType type) store.length)
            (allowed argument (List.mem_cons_self ..))

/-- Initialize the actual function parameters, then consume the induction
hypothesis at the exact source state produced by bindArguments. -/
theorem function_body {σ : Type} {model : StateModel σ} {slots : List EffectSlot} {signatures : List Signature}
    {codes : List GlobalCode} {locations : Nat → Nat} {captured : Core.Environment}
    {typeFuel fuel : Nat} {scope : Scope} {function : Function} {own : Signature} {body : Core.Expr}
    (signatureCompiled : signature typeFuel function = .ok own)
    (compiled : lowerFunction fuel signatures scope function own =
      .ok (.lambda (bundleType own.parameters) (Core.LanguageResult.resultType own.result) body))
    {sources : List Semantics.Value} {targets : List Core.Value}
    (values : ValuesRel own.parameters sources targets)
    {initial allocated final : Semantics.State σ} {sourceEnvironment : Semantics.Environment}
    (bound : Semantics.bindArguments function.args sources [] initial = some (sourceEnvironment, allocated))
    {control : Semantics.Control}
    (continued : ∀ {bodyFuel bodyScope result loops expression},
      lowerStatements bodyFuel signatures bodyScope result loops function.body = .ok expression →
      ScopeCoverage sourceEnvironment bodyScope →
      ∀ {world mapping environment store},
      EnvironmentRel world sourceEnvironment bodyScope mapping environment →
      GlobalEnvironmentRel codes locations bodyScope mapping environment →
      EffectEnvironmentRel slots bodyScope mapping environment →
      StateRel model world allocated store → InstalledGlobals codes locations captured store →
      ∃ extension targetValue finalStore,
        ControlRel result control targetValue ∧
        Core.Evaluates environment store (expression.rename mapping) targetValue finalStore ∧
        StateRel model (world ++ extension) final finalStore ∧ InstalledGlobals codes locations captured finalStore ∧ ClosuresPreserved store finalStore)
    {world : World} {mapping : Core.Renaming} {environment : Core.Environment} {store : Core.Store}
    (covered : ScopeCoverage [] scope)
    (globalsRelated : GlobalEnvironmentRel codes locations scope mapping environment)
    (runtimeRelated : EffectEnvironmentRel slots scope mapping environment)
    (heapRelated : StateRel model world initial store) (installed : InstalledGlobals codes locations captured store) :
    ∃ extension targetValue finalStore,
      ResultRel own.result (Semantics.finishFunction function.ret control) targetValue ∧
      Core.Evaluates (bundleValues targets :: environment) store (body.rename mapping.lift) targetValue finalStore ∧
      StateRel model (world ++ extension) final finalStore ∧ InstalledGlobals codes locations captured finalStore ∧ ClosuresPreserved store finalStore := by
  have allowed := ContextualStatementCorrespondence.lowerFunction_parameters_allowed compiled
  obtain ⟨arity, resultCompiled⟩ := signature_components signatureCompiled
  obtain ⟨statements, statementsCompiled, bodyShape⟩ := lowerFunction_components compiled
  have bodyEqual := Core.Expr.lambda.inj bodyShape
  rcases bodyEqual with ⟨_, _, rfl⟩
  have emptyEnvironment : EnvironmentRel world [] (scope.temporary (bundleType own.parameters))
      mapping.lift (bundleValues targets :: environment) := by
    intro name sourceLocation binding index found looked
    simp [Semantics.lookupLocation] at found
  obtain ⟨parameterExtension, sourceEnvironment', allocated', environment', store',
      sourceBound, cells, parametersRelated, allocatedHeap, allocatedGlobals⟩ :=
    initialize_parameters_state_renamed
      (external := fun (_ : σ) targetStore => InstalledGlobals codes locations captured targetStore ∧
        ClosuresPreserved store targetStore)
      values arity emptyEnvironment heapRelated ⟨installed, ClosuresPreserved.refl store⟩
      (fun _ _ _ _ hypothesis => ⟨hypothesis.1.append _, ClosuresPreserved.trans hypothesis.2 (ClosuresPreserved.append _ _)⟩)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (bound.symm.trans sourceBound))
  have parameterGlobals := cells.globalEnvironment arity allowed
    (globalsRelated.temporary (bundleType own.parameters) (bundleValues targets))
  have parameterRuntime := cells.effectEnvironment arity allowed
    (runtimeRelated.temporary (bundleType own.parameters) (bundleValues targets))
  obtain ⟨extension, controlValue, finalStore, related, executed, finalHeap, finalInstalled, lastFrame⟩ :=
    continued statementsCompiled
      ((covered.temporary (bundleType own.parameters)).bindArguments arity sourceBound)
      parametersRelated parameterGlobals parameterRuntime allocatedHeap allocatedGlobals.1
  obtain ⟨targetValue, resultRelated, finished⟩ := finish_preserves resultCompiled related executed
  have initialized := cells.evaluates_renamed (allValues := targets) (start := 0)
    (mapping := mapping.lift) rfl
    (fun index value found => by simpa only [Nat.zero_add] using found) finished
  refine ⟨parameterExtension ++ extension, targetValue, finalStore, resultRelated, ?_, ?_, finalInstalled, ClosuresPreserved.trans allocatedGlobals.2 lastFrame⟩
  · simpa only [parameterCode, values.length.2] using initialized
  · simpa only [List.append_assoc] using finalHeap

/-- The actual signature and represented arguments have the same arity.
The source binder therefore returns a state, excluding the arity fault rule. -/
theorem arity {σ : Type} {model : StateModel σ} {codes : List GlobalCode} {locations : Nat → Nat}
    {captured : Core.Environment} {typeFuel : Nat} {function : Function}
    {code : GlobalCode} {index : Nat} {sources : List Semantics.Value} {state : Semantics.State σ}
    (signatureCompiled : signature typeFuel function = .ok code.own)
    (mismatch : Semantics.bindArguments function.args sources [] state = none) :
    FunctionSimulation (model := model) codes locations captured code index sources state (.fault .arityMismatch) state := by
  intro targets values
  obtain ⟨sameLength, _⟩ := signature_components signatureCompiled
  obtain ⟨environment, finalState, bound⟩ :=
    bindArguments_exists (sameLength.trans values.length.1.symm) [] state
  rw [mismatch] at bound
  cases bound

/-- The function constructor in the mutual source derivation uses the body
IH at its specific allocated state and preserves the exact installed closure. -/
theorem function_simulation {σ : Type} {model : StateModel σ} {slots : List EffectSlot} {signatures : List Signature}
    {codes : List GlobalCode} {locations : Nat → Nat} {captured : Core.Environment}
    {typeFuel fuel : Nat} {scope : Scope} {function : Function} {code : GlobalCode} {index : Nat}
    (signatureCompiled : signature typeFuel function = .ok code.own)
    (compiled : lowerFunction fuel signatures scope function code.own = .ok code.expression)
    (covered : ScopeCoverage [] scope)
    (globals : GlobalEnvironmentRel codes locations scope Core.Renaming.id captured)
    (runtime : EffectEnvironmentRel slots scope Core.Renaming.id captured)
    {sources : List Semantics.Value} {initial allocated final : Semantics.State σ}
    {sourceEnvironment : Semantics.Environment}
    (bound : Semantics.bindArguments function.args sources [] initial = some (sourceEnvironment, allocated))
    {control : Semantics.Control}
    (continued : StatementsSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment
      function.body allocated control final) :
    FunctionSimulation (model := model) codes locations captured code index sources initial
      (Semantics.finishFunction function.ret control) final := by
  intro targets values world store heap installed
  have capturedGlobals : GlobalEnvironmentRel codes locations scope (globalShift index)
      (installationEnvironment captured index) := by
    change GlobalEnvironmentRel codes locations scope (fun slot => index + slot)
      (List.replicate index Core.Value.unit ++ captured)
    simpa only [List.length_replicate, Core.Renaming.id]
      using globals.prepend (List.replicate index Core.Value.unit)
  have capturedRuntime : EffectEnvironmentRel slots scope (globalShift index)
      (installationEnvironment captured index) := by
    change EffectEnvironmentRel slots scope (fun slot => index + slot)
      (List.replicate index Core.Value.unit ++ captured)
    simpa only [List.length_replicate, Core.Renaming.id]
      using runtime.prepend (List.replicate index Core.Value.unit)
  obtain ⟨extension, value, finalStore, related, evaluated, finalHeap, finalInstalled, lastFrame⟩ :=
    function_body signatureCompiled compiled values bound continued
      covered capturedGlobals capturedRuntime heap installed
  exact ⟨extension, _, finalStore, related, evaluated, finalHeap, finalInstalled, lastFrame⟩

end Solcore.Frontend.RustHull.DerivationFunctionCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.LoopDerivationCorrespondence
/-! A source loop derivation reuses the one self closure installed by the actual
compiler. Condition, body and post computations may allocate further closures;
each stage therefore retains its actual environment and store. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.LoopDerivationCorrespondence
open Correspondence DerivationCorrespondence StatementCorrespondence

/-- Simulation of an already installed loop closure, at a fixed source
configuration. Iteration does not allocate another self cell. -/
def LoopSimulation {σ : Type} {model : StateModel σ} {slots : List EffectSlot} (signatures : List Signature)
    (codes : List GlobalCode) (locations : Nat → Nat) (captured : Core.Environment)
    (sourceEnvironment : Semantics.Environment) (test : Expr) (post body : List Stmt)
    (initial : Semantics.State σ) (control : Semantics.Control) (final : Semantics.State σ) : Prop :=
  ∀ {scope result loops} (compiled : LoopLoweringStructure.Compiled signatures scope result loops test post body),
    ScopeCoverage sourceEnvironment scope →
  ∀ {world mapping environment store location},
    EnvironmentRel world sourceEnvironment scope mapping environment →
    GlobalEnvironmentRel codes locations scope mapping environment →
    EffectEnvironmentRel slots scope mapping environment →
    StateRel model world initial store → InstalledGlobals codes locations captured store →
    store.read? location = some (.inRight .unit
      (Core.LocalLoop.installedClosure result (compiled.conditionCore.rename mapping)
        (compiled.bodyCore.rename mapping) (compiled.postCore.rename mapping)
        (Core.Word.ofNatModulo 3) location environment)) →
    ∃ extension target finalStore,
      ControlRel result control target ∧
      Core.Evaluates (Core.LocalLoop.conditionPrefix result location ++ environment) store
        (Core.LocalLoop.loopBody result (compiled.conditionCore.rename mapping)
          (compiled.bodyCore.rename mapping) (compiled.postCore.rename mapping) (Core.Word.ofNatModulo 3))
        target finalStore ∧
      StateRel model (world ++ extension) final finalStore ∧
      InstalledGlobals codes locations captured finalStore ∧ ClosuresPreserved store finalStore

def LoopMotive {supported : String → Prop} {σ : Type} {model : StateModel σ} {slots : List EffectSlot} (functions : List Function) (signatures : List Signature)
    (codes : List GlobalCode) (locations : Nat → Nat) (captured : Core.Environment)
    (sourceEnvironment : Semantics.Environment) (test : Expr) (post body : List Stmt)
    (initial : Semantics.State σ) (control : Semantics.Control) (final : Semantics.State σ) : Prop :=
  ExecutableExpression supported functions test →
  (∀ statement ∈ post, ExecutableStatement supported functions statement) →
  (∀ statement ∈ body, ExecutableStatement supported functions statement) →
  LoopSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment test post body initial control final

variable {σ : Type} {model : StateModel σ} {slots : List EffectSlot} {signatures : List Signature} {codes : List GlobalCode}
  {locations : Nat → Nat} {captured : Core.Environment} {sourceEnvironment : Semantics.Environment}

/-- Instantiate the condition IH under the exact administrative prefix of a
loop stage, including any heap effects performed while testing it. -/
theorem test_at {test : Expr} {initial final : Semantics.State σ} {value : Semantics.Value}
    {truth : Bool}
    (evaluated : ExprSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment test initial (.value value) final)
    (tested : Semantics.condition? value = some truth)
    {fuel : Nat} {scope : Scope} {lowered : Lowered} {expression : Core.Expr}
    (compiled : lowerExpression fuel signatures scope test = .ok lowered)
    (converted : condition lowered = .ok expression)
    (covered : ScopeCoverage sourceEnvironment scope)
    (extra : Core.Environment)
    {world : World} {mapping : Core.Renaming} {environment : Core.Environment} {store : Core.Store}
    (locals : EnvironmentRel world sourceEnvironment scope mapping environment)
    (globals : GlobalEnvironmentRel codes locations scope mapping environment)
    (runtime : EffectEnvironmentRel slots scope mapping environment)
    (heap : StateRel model world initial store) (installed : InstalledGlobals codes locations captured store) :
    ∃ extension finalStore,
      Core.Evaluates (extra ++ environment) store
        ((expression.rename mapping).rename (Core.LocalLoop.shift extra.length))
        (.inRight .word (.bool truth)) finalStore ∧
      StateRel model (world ++ extension) final finalStore ∧
      InstalledGlobals codes locations captured finalStore ∧ ClosuresPreserved store finalStore := by
  obtain ⟨extension, target, finalStore, related, execution, finalHeap, finalInstalled, frame⟩ :=
    evaluated.value rfl compiled covered (locals.prepend extra) (globals.prepend extra) (runtime.prepend extra) heap installed
  have conditionExecution := ExpressionCorrespondence.condition_evaluates converted related tested execution
  exact ⟨extension, finalStore,
    by rw [Core.Expr.rename_comp]; exact conditionExecution,
    finalHeap, finalInstalled, frame⟩

/-- Instantiate a body or post IH at its actual control-transfer prefix. -/
theorem statements_at {statements : List Stmt} {initial final : Semantics.State σ}
    {control : Semantics.Control}
    (evaluated : StatementsSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment statements initial control final)
    {fuel : Nat} {scope : Scope} {result : Core.Ty} {loops : Nat} {expression : Core.Expr}
    (compiled : lowerStatements fuel signatures scope result loops statements = .ok expression)
    (covered : ScopeCoverage sourceEnvironment scope)
    (extra : Core.Environment)
    {world : World} {mapping : Core.Renaming} {environment : Core.Environment} {store : Core.Store}
    (locals : EnvironmentRel world sourceEnvironment scope mapping environment)
    (globals : GlobalEnvironmentRel codes locations scope mapping environment)
    (runtime : EffectEnvironmentRel slots scope mapping environment)
    (heap : StateRel model world initial store) (installed : InstalledGlobals codes locations captured store) :
    ∃ extension target finalStore,
      ControlRel result control target ∧
      Core.Evaluates (extra ++ environment) store
        ((expression.rename mapping).rename (Core.LocalLoop.shift extra.length)) target finalStore ∧
      StateRel model (world ++ extension) final finalStore ∧
      InstalledGlobals codes locations captured finalStore ∧ ClosuresPreserved store finalStore := by
  obtain ⟨extension, target, finalStore, related, execution, finalHeap, finalInstalled, frame⟩ :=
    evaluated compiled covered (locals.prepend extra) (globals.prepend extra) (runtime.prepend extra) heap installed
  exact ⟨extension, target, finalStore, related,
    by rw [Core.Expr.rename_comp]; exact execution,
    finalHeap, finalInstalled, frame⟩


/-- The public loop statement allocates and installs its actual self closure
once, then enters the loop derivation. -/
theorem statement {statement : Stmt} {test : Expr} {post body : List Stmt}
    {initial final : Semantics.State σ} {control : Semantics.Control}
    (kind : statement.kind = .forLoop [] test post body)
    (continued : LoopSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment test post body initial control final) :
    StmtSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment statement initial control final := by
  intro fuel scope result loops expression compiled covered world mapping environment store
    locals globals runtime heap installed
  cases statement with | mk statementKind span =>
  cases kind
  cases fuel with
  | zero => simp [lowerStatement, fail] at compiled
  | succ fuel =>
      obtain ⟨conditionCode, conditionCore, bodyCore, postCore,
        conditionCompiled, conditionConverted, bodyCompiled, postCompiled, rfl⟩ :=
        LoopLoweringStructure.empty_init_components compiled
      let code : LoopLoweringStructure.Compiled signatures scope result loops test post body :=
        ⟨fuel, conditionCode, conditionCore, bodyCore, postCore,
          conditionCompiled, conditionConverted, bodyCompiled, postCompiled⟩
      let cell := Core.Value.inRight .unit (Core.LocalLoop.installedClosure result
        (conditionCore.rename mapping) (bodyCore.rename mapping) (postCore.rename mapping)
        (Core.Word.ofNatModulo 3) store.length environment)
      have self : (store ++ [cell]).read? store.length = some cell := by simp [Core.Store.read?]
      obtain ⟨extension, target, finalStore, related, executed, finalHeap, finalInstalled, frame⟩ :=
        continued code covered locals globals runtime (heap.appendCore [cell]) (installed.append [cell]) self
      refine ⟨extension, target, finalStore, related, ?_, finalHeap, finalInstalled,
        ClosuresPreserved.trans (ClosuresPreserved.append store [cell]) frame⟩
      rw [Core.LocalLoop.iterate_rename]
      exact Core.LocalLoop.iterate_start result (Core.Word.ofNatModulo 3) executed

/-- Initializers retain the exact compiler's statement-list scope and control
behavior before reaching the single allocation above. -/
theorem initialized_statement {statement : Stmt} {test : Expr} {init post body : List Stmt}
    {initial final : Semantics.State σ} {control : Semantics.Control}
    (kind : statement.kind = .forLoop init test post body) (nonempty : init ≠ [])
    (continued : StatementsSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment
      (init ++ [⟨.forLoop [] test post body, statement.span⟩]) initial control final) :
    StmtSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment statement initial control final := by
  intro fuel scope result loops expression compiled
  cases statement with | mk statementKind span =>
  cases kind
  cases fuel with
  | zero => simp [lowerStatement, fail] at compiled
  | succ fuel => exact continued (LoopLoweringStructure.nonempty_init nonempty compiled)

/-- A failed condition skips both loop stages while retaining its exact reason
and store after conversion to the Core boolean carrier. -/
theorem condition_fault {test : Expr} {post body : List Stmt}
    {initial final : Semantics.State σ} {reason : Semantics.Fault}
    (tested : ExprSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment test
      initial (.fault reason) final) :
    LoopSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment test post body
      initial (.fault reason) final := by
  intro scope result loops compiled covered world mapping environment store location locals globals runtime heap installed _
  let extra := Core.LocalLoop.conditionPrefix result location
  obtain ⟨extension, target, finalStore, related, evaluated, finalHeap, finalInstalled, frame⟩ :=
    tested compiled.conditionCompiled covered (locals.prepend extra) (globals.prepend extra) (runtime.prepend extra) heap installed
  cases related with | language reason =>
  have converted := ExpressionCorrespondence.condition_failure compiled.conditionConverted evaluated
  have execution : Core.Evaluates (extra ++ environment) store
      ((compiled.conditionCore.rename mapping).rename (Core.LocalLoop.shift extra.length))
      (.inLeft .bool (.word reason)) finalStore := by
    rw [Core.Expr.rename_comp]
    exact converted
  exact ⟨extension, _, finalStore, .language reason,
    Core.LocalLoop.loopBody_conditionFailure result (Core.Word.ofNatModulo 3) location execution,
    finalHeap, finalInstalled, frame⟩

/-- Compiler-checked conditions cannot produce an invalid source truth value. -/
theorem condition_invalid {test : Expr} {post body : List Stmt}
    {initial final : Semantics.State σ} {value : Semantics.Value}
    (tested : ExprSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment test
      initial (.value value) final)
    (invalid : Semantics.condition? value = none) :
    LoopSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment test post body
      initial (.fault (.invalidValue "condition")) final := by
  intro scope result loops compiled covered world mapping environment store location locals globals runtime heap installed _
  obtain ⟨_, _, _, related, _, _, _, _⟩ :=
    tested.value rfl compiled.conditionCompiled covered locals globals runtime heap installed
  obtain ⟨truth, valid⟩ := DerivationCorrespondence.condition_valid compiled.conditionConverted related
  rw [invalid] at valid
  cases valid

theorem done {test : Expr} {post body : List Stmt} {initial final : Semantics.State σ}
    {value : Semantics.Value}
    (tested : ExprSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment test initial (.value value) final)
    (truth : Semantics.condition? value = some false) :
    LoopSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment test post body initial .fallthrough final := by
  intro scope result loops compiled covered world mapping environment store location locals globals runtime heap installed _
  obtain ⟨extension, finalStore, executed, finalHeap, finalInstalled, frame⟩ :=
    test_at tested truth compiled.conditionCompiled compiled.conditionConverted covered
      (Core.LocalLoop.conditionPrefix result location) locals globals runtime heap installed
  exact ⟨extension, _, finalStore, .fallthrough,
    Core.LocalLoop.loopBody_done result (Core.Word.ofNatModulo 3) location executed,
    finalHeap, finalInstalled, frame⟩

theorem body_break {test : Expr} {post body : List Stmt}
    {initial testedState final : Semantics.State σ} {value : Semantics.Value}
    (tested : ExprSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment test initial (.value value) testedState)
    (truth : Semantics.condition? value = some true)
    (executed : StatementsSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment body testedState .breaking final) :
    LoopSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment test post body initial .fallthrough final := by
  intro scope result loops compiled covered world mapping environment store location locals globals runtime heap installed _
  obtain ⟨testExtension, testedStore, testEvaluation, testedHeap, testedInstalled, testFrame⟩ :=
    test_at tested truth compiled.conditionCompiled compiled.conditionConverted covered
      (Core.LocalLoop.conditionPrefix result location) locals globals runtime heap installed
  obtain ⟨bodyExtension, target, finalStore, related, bodyEvaluation, finalHeap, finalInstalled, bodyFrame⟩ :=
    statements_at executed compiled.bodyCompiled covered (Core.LocalLoop.bodyPrefix result location)
      (locals.extendWorld testExtension) globals runtime testedHeap testedInstalled
  cases related
  exact ⟨testExtension ++ bodyExtension, _, finalStore, .fallthrough,
    Core.LocalLoop.loopBody_bodyBreak result (Core.Word.ofNatModulo 3) location testEvaluation bodyEvaluation,
    by simpa only [List.append_assoc] using finalHeap,
    finalInstalled, ClosuresPreserved.trans testFrame bodyFrame⟩

theorem body_stop {test : Expr} {post body : List Stmt}
    {initial testedState final : Semantics.State σ} {value : Semantics.Value} {control : Semantics.Control}
    (tested : ExprSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment test initial (.value value) testedState)
    (truth : Semantics.condition? value = some true)
    (executed : StatementsSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment body testedState control final)
    (stopped : (∃ value, control = .returned value) ∨ (∃ reason, control = .fault reason)) :
    LoopSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment test post body initial control final := by
  intro scope result loops compiled covered world mapping environment store location locals globals runtime heap installed _
  obtain ⟨testExtension, testedStore, testEvaluation, testedHeap, testedInstalled, testFrame⟩ :=
    test_at tested truth compiled.conditionCompiled compiled.conditionConverted covered
      (Core.LocalLoop.conditionPrefix result location) locals globals runtime heap installed
  obtain ⟨bodyExtension, target, finalStore, related, bodyEvaluation, finalHeap, finalInstalled, bodyFrame⟩ :=
    statements_at executed compiled.bodyCompiled covered (Core.LocalLoop.bodyPrefix result location)
      (locals.extendWorld testExtension) globals runtime testedHeap testedInstalled
  rcases stopped with ⟨source, rfl⟩ | ⟨reason, rfl⟩
  · cases related with
    | returned valueRelated =>
        exact ⟨testExtension ++ bodyExtension, _, finalStore, .returned valueRelated,
          Core.LocalLoop.loopBody_bodyReturn result (Core.Word.ofNatModulo 3) location testEvaluation bodyEvaluation,
          by simpa only [List.append_assoc] using finalHeap,
          finalInstalled, ClosuresPreserved.trans testFrame bodyFrame⟩
  · cases related with
    | language reason =>
        exact ⟨testExtension ++ bodyExtension, _, finalStore, .language reason,
          Core.LocalLoop.loopBody_bodyFailure result (Core.Word.ofNatModulo 3) location testEvaluation bodyEvaluation,
          by simpa only [List.append_assoc] using finalHeap,
          finalInstalled, ClosuresPreserved.trans testFrame bodyFrame⟩

private theorem progress_value {result : Core.Ty} {control : Semantics.Control} {value : Core.Value}
    (related : ControlRel result control value)
    (progress : control = .fallthrough ∨ control = .continuing) :
    ∃ flag, value = Core.LocalLoop.advanceValue result flag := by
  rcases progress with rfl | rfl
  · cases related; exact ⟨false, rfl⟩
  · cases related; exact ⟨true, rfl⟩

theorem step {test : Expr} {post body : List Stmt}
    {initial testedState bodyState postState final : Semantics.State σ}
    {value : Semantics.Value} {bodyControl postControl control : Semantics.Control}
    (tested : ExprSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment test initial (.value value) testedState)
    (truth : Semantics.condition? value = some true)
    (bodyExecuted : StatementsSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment body testedState bodyControl bodyState)
    (bodyContinues : bodyControl = .fallthrough ∨ bodyControl = .continuing)
    (postExecuted : StatementsSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment post bodyState postControl postState)
    (postContinues : postControl = .fallthrough ∨ postControl = .continuing)
    (continued : LoopSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment test post body postState control final) :
    LoopSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment test post body initial control final := by
  intro scope result loops compiled covered world mapping environment store location locals globals runtime heap installed self
  obtain ⟨testExtension, testedStore, testEvaluation, testedHeap, testedInstalled, testFrame⟩ :=
    test_at tested truth compiled.conditionCompiled compiled.conditionConverted covered
      (Core.LocalLoop.conditionPrefix result location) locals globals runtime heap installed
  obtain ⟨bodyExtension, bodyTarget, bodyStore, bodyRelated, bodyEvaluation, bodyHeap, bodyInstalled, bodyFrame⟩ :=
    statements_at bodyExecuted compiled.bodyCompiled covered
      (Core.LocalLoop.bodyPrefix result location)
      (locals.extendWorld testExtension) globals runtime testedHeap testedInstalled
  obtain ⟨bodyFlag, rfl⟩ := progress_value bodyRelated bodyContinues
  obtain ⟨postExtension, postTarget, postStore, postRelated, postEvaluation, postHeap, postInstalled, postFrame⟩ :=
    statements_at postExecuted compiled.postCompiled covered
      (Core.LocalLoop.postPrefix result location bodyFlag)
      ((locals.extendWorld testExtension).extendWorld bodyExtension) globals runtime bodyHeap bodyInstalled
  simp only [Core.LocalLoop.postPrefix_length] at postEvaluation
  obtain ⟨postFlag, rfl⟩ := progress_value postRelated postContinues
  have retained := postFrame (bodyFrame (testFrame self))
  obtain ⟨nextExtension, target, finalStore, related, nextEvaluation, finalHeap, finalInstalled, nextFrame⟩ :=
    continued compiled covered
      (((locals.extendWorld testExtension).extendWorld bodyExtension).extendWorld postExtension)
      globals runtime postHeap postInstalled retained
  exact ⟨testExtension ++ bodyExtension ++ postExtension ++ nextExtension, target, finalStore, related,
    Core.LocalLoop.loopBody_step result (Core.Word.ofNatModulo 3) location bodyFlag postFlag
      testEvaluation bodyEvaluation postEvaluation retained nextEvaluation,
    by simpa only [List.append_assoc] using finalHeap, finalInstalled,
    ClosuresPreserved.trans testFrame (ClosuresPreserved.trans bodyFrame
      (ClosuresPreserved.trans postFrame nextFrame))⟩

theorem post_break {test : Expr} {post body : List Stmt}
    {initial testedState bodyState final : Semantics.State σ}
    {value : Semantics.Value} {bodyControl : Semantics.Control}
    (tested : ExprSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment test initial (.value value) testedState)
    (truth : Semantics.condition? value = some true)
    (bodyExecuted : StatementsSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment body testedState bodyControl bodyState)
    (bodyContinues : bodyControl = .fallthrough ∨ bodyControl = .continuing)
    (postExecuted : StatementsSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment post bodyState .breaking final) :
    LoopSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment test post body initial .fallthrough final := by
  intro scope result loops compiled covered world mapping environment store location locals globals runtime heap installed _
  obtain ⟨testExtension, testedStore, testEvaluation, testedHeap, testedInstalled, testFrame⟩ :=
    test_at tested truth compiled.conditionCompiled compiled.conditionConverted covered
      (Core.LocalLoop.conditionPrefix result location) locals globals runtime heap installed
  obtain ⟨bodyExtension, bodyTarget, bodyStore, bodyRelated, bodyEvaluation, bodyHeap, bodyInstalled, bodyFrame⟩ :=
    statements_at bodyExecuted compiled.bodyCompiled covered
      (Core.LocalLoop.bodyPrefix result location)
      (locals.extendWorld testExtension) globals runtime testedHeap testedInstalled
  obtain ⟨bodyFlag, rfl⟩ := progress_value bodyRelated bodyContinues
  obtain ⟨postExtension, postTarget, finalStore, postRelated, postEvaluation, finalHeap, finalInstalled, postFrame⟩ :=
    statements_at postExecuted compiled.postCompiled covered
      (Core.LocalLoop.postPrefix result location bodyFlag)
      ((locals.extendWorld testExtension).extendWorld bodyExtension) globals runtime bodyHeap bodyInstalled
  simp only [Core.LocalLoop.postPrefix_length] at postEvaluation
  cases postRelated
  exact ⟨testExtension ++ bodyExtension ++ postExtension, _, finalStore, .fallthrough,
    Core.LocalLoop.loopBody_postBreak result (Core.Word.ofNatModulo 3) location bodyFlag
      testEvaluation bodyEvaluation postEvaluation,
    by simpa only [List.append_assoc] using finalHeap, finalInstalled,
    ClosuresPreserved.trans testFrame (ClosuresPreserved.trans bodyFrame postFrame)⟩

theorem post_stop {test : Expr} {post body : List Stmt}
    {initial testedState bodyState final : Semantics.State σ}
    {value : Semantics.Value} {bodyControl control : Semantics.Control}
    (tested : ExprSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment test initial (.value value) testedState)
    (truth : Semantics.condition? value = some true)
    (bodyExecuted : StatementsSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment body testedState bodyControl bodyState)
    (bodyContinues : bodyControl = .fallthrough ∨ bodyControl = .continuing)
    (postExecuted : StatementsSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment post bodyState control final)
    (stopped : (∃ value, control = .returned value) ∨ (∃ reason, control = .fault reason)) :
    LoopSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment test post body initial control final := by
  intro scope result loops compiled covered world mapping environment store location locals globals runtime heap installed _
  obtain ⟨testExtension, testedStore, testEvaluation, testedHeap, testedInstalled, testFrame⟩ :=
    test_at tested truth compiled.conditionCompiled compiled.conditionConverted covered
      (Core.LocalLoop.conditionPrefix result location) locals globals runtime heap installed
  obtain ⟨bodyExtension, bodyTarget, bodyStore, bodyRelated, bodyEvaluation, bodyHeap, bodyInstalled, bodyFrame⟩ :=
    statements_at bodyExecuted compiled.bodyCompiled covered
      (Core.LocalLoop.bodyPrefix result location)
      (locals.extendWorld testExtension) globals runtime testedHeap testedInstalled
  obtain ⟨bodyFlag, rfl⟩ := progress_value bodyRelated bodyContinues
  obtain ⟨postExtension, postTarget, finalStore, postRelated, postEvaluation, finalHeap, finalInstalled, postFrame⟩ :=
    statements_at postExecuted compiled.postCompiled covered
      (Core.LocalLoop.postPrefix result location bodyFlag)
      ((locals.extendWorld testExtension).extendWorld bodyExtension) globals runtime bodyHeap bodyInstalled
  simp only [Core.LocalLoop.postPrefix_length] at postEvaluation
  rcases stopped with ⟨source, rfl⟩ | ⟨reason, rfl⟩
  · cases postRelated with
    | returned related =>
        exact ⟨testExtension ++ bodyExtension ++ postExtension, _, finalStore, .returned related,
          Core.LocalLoop.loopBody_postReturn result (Core.Word.ofNatModulo 3) location bodyFlag
            testEvaluation bodyEvaluation postEvaluation,
          by simpa only [List.append_assoc] using finalHeap, finalInstalled,
          ClosuresPreserved.trans testFrame (ClosuresPreserved.trans bodyFrame postFrame)⟩
  · cases postRelated with
    | language reason =>
        exact ⟨testExtension ++ bodyExtension ++ postExtension, _, finalStore, .language reason,
          Core.LocalLoop.loopBody_postFailure result (Core.Word.ofNatModulo 3) location bodyFlag
            testEvaluation bodyEvaluation postEvaluation,
          by simpa only [List.append_assoc] using finalHeap, finalInstalled,
          ClosuresPreserved.trans testFrame (ClosuresPreserved.trans bodyFrame postFrame)⟩

end Solcore.Frontend.RustHull.LoopDerivationCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.MatchDerivationCorrespondence
/-! Independent match alternatives drive the actual emitted pattern tests and
binder allocation. Rejected alternatives keep the heap; a selected alternative
allocates exactly its source binder before running the existing statement IH. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.MatchDerivationCorrespondence
open Correspondence DerivationCorrespondence StatementCorrespondence

/-- The scrutinee is already evaluated and resides at the compiler's temporary
slot. The relation follows the particular independent alternative derivation. -/
def AlternativesSimulation {σ : Type} {model : StateModel σ} {slots : List EffectSlot} (signatures : List Signature)
    (codes : List GlobalCode) (locations : Nat → Nat) (captured : Core.Environment)
    (sourceEnvironment : Semantics.Environment) (sourceType : Ty) (sourceValue : Semantics.Value)
    (alternatives : List Alt) (initial : Semantics.State σ) (control : Semantics.Control)
    (final : Semantics.State σ) : Prop :=
  ∀ {typeFuel targetType}, lowerType typeFuel sourceType = .ok targetType →
  ∀ {fuel scope result loops expression},
    lowerAlternatives fuel signatures scope result loops targetType alternatives = .ok expression →
    ScopeCoverage sourceEnvironment scope →
  ∀ {world mapping environment store targetValue},
    ValueRel targetType sourceValue targetValue → environment[mapping 0]? = some targetValue →
    EnvironmentRel world sourceEnvironment scope mapping environment →
    GlobalEnvironmentRel codes locations scope mapping environment →
    EffectEnvironmentRel slots scope mapping environment →
    StateRel model world initial store → InstalledGlobals codes locations captured store →
    ∃ extension target finalStore,
      ControlRel result control target ∧ Core.Evaluates environment store (expression.rename mapping) target finalStore ∧
      StateRel model (world ++ extension) final finalStore ∧
      InstalledGlobals codes locations captured finalStore ∧ ClosuresPreserved store finalStore

def AlternativesMotive {supported : String → Prop} {σ : Type} {model : StateModel σ} {slots : List EffectSlot} (functions : List Function) (signatures : List Signature)
    (codes : List GlobalCode) (locations : Nat → Nat) (captured : Core.Environment)
    (sourceEnvironment : Semantics.Environment) (sourceType : Ty) (sourceValue : Semantics.Value)
    (alternatives : List Alt) (initial : Semantics.State σ) (control : Semantics.Control)
    (final : Semantics.State σ) : Prop :=
  (∀ alternative ∈ alternatives, ∀ statement ∈ alternative.body, ExecutableStatement supported functions statement) →
  AlternativesSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment sourceType sourceValue
    alternatives initial control final

private theorem alternatives_components {fuel : Nat} {signatures : List Signature} {scope : Scope}
    {result target : Core.Ty} {loops : Nat} {alternative : Alt} {rest : List Alt} {expression : Core.Expr}
    (compiled : lowerAlternatives (fuel + 1) signatures scope result loops target
      (alternative :: rest) = .ok expression) :
    ∃ payload test body next,
      alternative.binder.startsWith Effects.reservedPrefix = false ∧
      testPattern target alternative.pat.kind = .ok (payload, test) ∧
      lowerStatements fuel signatures ((scope.temporary payload).addLocal alternative.binder payload)
        result loops alternative.body = .ok body ∧
      lowerAlternatives fuel signatures scope result loops target rest = .ok next ∧
      expression = .caseE (test (.var 0)) (next.weakenAt 0)
        (.letE (Core.OptionalCell.allocateInitialized payload (.var 0)) body) := by
  simp only [lowerAlternatives] at compiled
  have allowed : alternative.binder.startsWith Effects.reservedPrefix = false := by
    cases found : alternative.binder.startsWith Effects.reservedPrefix
    · rfl
    · simp [found, fail, Bind.bind, Except.bind] at compiled
  simp only [allowed, Bool.false_eq_true, ↓reduceIte] at compiled
  obtain ⟨⟨payload, test⟩, tested, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨body, bodyCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨next, nextCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
  cases returned
  exact ⟨payload, test, body, next, allowed, tested, bodyCompiled, nextCompiled, rfl⟩

private theorem statement_components {fuel : Nat} {signatures : List Signature} {scope : Scope}
    {result : Core.Ty} {loops : Nat} {target : Ty} {scrutinee : Expr} {alternatives : List Alt}
    {span : Option Span} {expression : Core.Expr}
    (compiled : lowerStatement (fuel + 1) signatures scope result loops
      ⟨.matchStmt target scrutinee alternatives, span⟩ = .ok expression) :
    ∃ targetType value arms,
      lowerType fuel target = .ok targetType ∧
      lowerExpression fuel signatures scope scrutinee = .ok value ∧
      targetType = value.type ∧
      lowerAlternatives fuel signatures (scope.temporary targetType) result loops targetType alternatives = .ok arms ∧
      expression = Core.LanguageResult.bind (Core.LocalLoop.controlType result) value.expression arms := by
  simp only [lowerStatement] at compiled
  obtain ⟨targetType, typeCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨value, valueCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨checked, typeChecked, compiled⟩ := lower_bind_eq_ok.mp compiled
  cases checked
  obtain ⟨arms, armsCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
  cases returned
  exact ⟨targetType, value, arms, typeCompiled, valueCompiled,
    expectType_eq_of_ok typeChecked, armsCompiled, rfl⟩

variable {σ : Type} {model : StateModel σ} {slots : List EffectSlot} {signatures : List Signature} {codes : List GlobalCode}
  {locations : Nat → Nat} {captured : Core.Environment} {sourceEnvironment : Semantics.Environment}

/-- Exhausted alternatives fall through without allocating a binder. -/
theorem nil {sourceType : Ty} {sourceValue : Semantics.Value} {state : Semantics.State σ} :
    AlternativesSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment sourceType sourceValue
      [] state .fallthrough state := by
  intro typeFuel targetType _ fuel scope result loops expression compiled _ world mapping environment store
    targetValue _ _ _ _ _ heap installed
  cases fuel with
  | zero => simp [lowerAlternatives, fail] at compiled
  | succ fuel =>
      simp only [lowerAlternatives] at compiled
      cases compiled
      exact ⟨[], _, store, .fallthrough, by
        simpa only [rename_fallthrough] using Core.LocalLoop.fallthrough_evaluates result environment store,
        by simpa only [List.append_nil] using heap, installed, ClosuresPreserved.refl store⟩

/-- A selected alternative binds its actual payload and retains the added cell
through arbitrary calls, loops, return or language failure in its body. -/
theorem matched {sourceType : Ty} {sourceValue payload : Semantics.Value}
    {alternative : Alt} {rest : List Alt} {initial final : Semantics.State σ} {control : Semantics.Control}
    (selected : Semantics.patternPayload? sourceType alternative.pat.kind sourceValue = some payload)
    (continued : StatementsSimulation (model := model) (slots := slots) signatures codes locations captured
      ((alternative.binder, initial.heap.length) :: sourceEnvironment) alternative.body
      (Semantics.allocate initial payload).2 control final) :
    AlternativesSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment sourceType sourceValue
      (alternative :: rest) initial control final := by
  intro typeFuel targetType typeCompiled fuel scope result loops expression compiled covered world mapping environment store
    targetValue related found locals globals runtime heap installed
  cases fuel with
  | zero => simp [lowerAlternatives, fail] at compiled
  | succ fuel =>
      obtain ⟨payloadType, test, body, next, allowed, patternCompiled, bodyCompiled, _, rfl⟩ :=
        alternatives_components compiled
      obtain ⟨observed, patternRelated, patternEvaluated⟩ :=
        PatternCorrespondence.test_preserves (value := .var 0) (mapping := mapping)
          (store := store) typeCompiled related patternCompiled (.var found)
      rw [selected] at patternRelated
      cases patternRelated with
      | matched payloadRelated =>
          rename_i targetPayload
          have allocated := heap.allocate payloadRelated
          have entry : (world ++ [(payloadType, store.length)])[initial.heap.length]? =
              some (payloadType, store.length) := by
            rw [← heap.length_eq, List.getElem?_concat_length]
          have bodyLocals :=
            ((locals.extendWorld [(payloadType, store.length)]).temporary payloadType targetPayload).addLocal
              alternative.binder payloadType initial.heap.length store.length entry
          have bodyGlobals := (globals.temporary payloadType targetPayload).addLocal
            alternative.binder payloadType (.cellRef (Core.OptionalCell.cellType payloadType) store.length) allowed
          obtain ⟨extension, target, finalStore, controlRelated, bodyEvaluated, finalHeap, finalInstalled, frame⟩ :=
            continued bodyCompiled
              ((covered.temporary payloadType).addLocal alternative.binder payloadType initial.heap.length) bodyLocals bodyGlobals
              ((runtime.temporary payloadType targetPayload).addLocal alternative.binder payloadType
                (.cellRef (Core.OptionalCell.cellType payloadType) store.length) allowed) allocated (installed.append _)
          refine ⟨[(payloadType, store.length)] ++ extension, target, finalStore, controlRelated,
            ?_, ?_, finalInstalled, ClosuresPreserved.trans (ClosuresPreserved.append _ _) frame⟩
          · exact .caseRight patternEvaluated
              (.letE (Core.OptionalCell.allocateInitialized_evaluates (.var rfl)) bodyEvaluated)
          · simpa only [List.append_assoc] using finalHeap

/-- Rejected patterns introduce only the case binder, whose renaming preserves
the same scrutinee and lexical environment for the remaining alternatives. -/
theorem next {sourceType : Ty} {sourceValue : Semantics.Value}
    {alternative : Alt} {rest : List Alt} {initial final : Semantics.State σ} {control : Semantics.Control}
    (rejected : Semantics.patternPayload? sourceType alternative.pat.kind sourceValue = none)
    (continued : AlternativesSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment sourceType sourceValue
      rest initial control final) :
    AlternativesSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment sourceType sourceValue
      (alternative :: rest) initial control final := by
  intro typeFuel targetType typeCompiled fuel scope result loops expression compiled covered world mapping environment store
    targetValue related found locals globals runtime heap installed
  cases fuel with
  | zero => simp [lowerAlternatives, fail] at compiled
  | succ fuel =>
      obtain ⟨payloadType, test, body, next, _, patternCompiled, _, nextCompiled, rfl⟩ :=
        alternatives_components compiled
      obtain ⟨observed, patternRelated, patternEvaluated⟩ :=
        PatternCorrespondence.test_preserves (value := .var 0) (mapping := mapping)
          (store := store) typeCompiled related patternCompiled (.var found)
      rw [rejected] at patternRelated
      cases patternRelated with
      | missed =>
          have shiftedFound : (Core.Value.unit :: environment)[1 + mapping 0]? = some targetValue := by
            simpa [Nat.add_comm] using found
          obtain ⟨extension, target, finalStore, controlRelated, nextEvaluated, finalHeap, finalInstalled, frame⟩ :=
            continued typeCompiled nextCompiled covered related shiftedFound
              (locals.prepend [.unit]) (globals.prepend [.unit]) (runtime.prepend [.unit]) heap installed
          refine ⟨extension, target, finalStore, controlRelated, ?_, finalHeap, finalInstalled, frame⟩
          apply Core.Evaluates.caseLeft patternEvaluated
          have renamed : (next.weakenAt 0).rename (Core.Renaming.lift mapping) =
              next.rename (fun index => 1 + mapping index) := by
            rw [← Core.Expr.rename_insertion, Core.Expr.rename_comp]
            congr 1
            funext index
            simp [Core.Renaming.comp, Core.Renaming.insertion, Core.Renaming.lift, Nat.add_comm]
          simpa only [renamed, List.length_cons, List.length_nil, Nat.zero_add,
            List.cons_append, List.nil_append] using nextEvaluated

/-- The actual match compiler first evaluates the scrutinee, then runs the
independent alternative derivation in its exact temporary scope. -/
theorem statement {statement : Stmt} {sourceType : Ty} {scrutinee : Expr} {alternatives : List Alt}
    {initial middle final : Semantics.State σ} {sourceValue : Semantics.Value} {control : Semantics.Control}
    (kind : statement.kind = .matchStmt sourceType scrutinee alternatives)
    (tested : ExprSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment scrutinee initial (.value sourceValue) middle)
    (selected : AlternativesSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment sourceType sourceValue
      alternatives middle control final) :
    StmtSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment statement initial control final := by
  intro fuel scope result loops expression compiled covered world mapping environment store locals globals runtime heap installed
  cases statement with | mk statementKind span =>
  cases kind
  cases fuel with
  | zero => simp [lowerStatement, fail] at compiled
  | succ fuel =>
      obtain ⟨targetType, value, arms, typeCompiled, valueCompiled, same, armsCompiled, rfl⟩ :=
        statement_components compiled
      obtain ⟨firstExtension, targetValue, middleStore, related, evaluated, middleHeap, middleInstalled, firstFrame⟩ :=
        tested.value rfl valueCompiled covered locals globals runtime heap installed
      obtain ⟨extension, target, finalStore, controlRelated, armsEvaluated, finalHeap, finalInstalled, frame⟩ :=
        selected typeCompiled armsCompiled (covered.temporary targetType) (same ▸ related) rfl
          ((locals.extendWorld firstExtension).temporary targetType targetValue)
          (globals.temporary targetType targetValue) (runtime.temporary targetType targetValue) middleHeap middleInstalled
      exact ⟨firstExtension ++ extension, target, finalStore, controlRelated,
        Core.LanguageResult.bind_success _ evaluated armsEvaluated,
        by simpa only [List.append_assoc] using finalHeap, finalInstalled, firstFrame.trans frame⟩

/-- A failed scrutinee skips every pattern and binder allocation. -/
theorem fault {statement : Stmt} {sourceType : Ty} {scrutinee : Expr} {alternatives : List Alt}
    {initial final : Semantics.State σ} {reason : Semantics.Fault}
    (kind : statement.kind = .matchStmt sourceType scrutinee alternatives)
    (tested : ExprSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment scrutinee initial (.fault reason) final) :
    StmtSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment statement initial (.fault reason) final := by
  intro fuel scope result loops expression compiled covered world mapping environment store locals globals runtime heap installed
  cases statement with | mk statementKind span =>
  cases kind
  cases fuel with
  | zero => simp [lowerStatement, fail] at compiled
  | succ fuel =>
      obtain ⟨targetType, value, arms, _, valueCompiled, _, _, rfl⟩ := statement_components compiled
      obtain ⟨extension, targetValue, finalStore, related, evaluated, finalHeap, finalInstalled, frame⟩ :=
        tested valueCompiled covered locals globals runtime heap installed
      cases related with | language reason =>
      exact ⟨extension, _, finalStore, .language reason,
        Core.LanguageResult.bind_failure _ evaluated, finalHeap, finalInstalled, frame⟩

end Solcore.Frontend.RustHull.MatchDerivationCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RevertCorrespondence
/-! The revert boundary used by the common recursive proof. Hull's explicit
revert is an external effect: the effect specification of the statement
simulates the actual `Effects.revertMessage` code, which writes the message
and exits through the revert termination. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.DerivationCorrespondence
open Correspondence ScalarExecution

def RevertPreservation {σ : Type} (supported : String → Prop) (model : StateModel σ)
    (slots : List EffectSlot) (effects : Semantics.ExternalSemantics σ) : Prop :=
  ∀ {message : String} {initial : Semantics.State σ} {control : Semantics.Control} {final : σ},
    supported "revert" → effects.revert message initial.external control final →
    ∀ {scope exit}, Effects.revertMessage scope message = .ok exit →
    ∀ {world mapping environment store},
      EffectEnvironmentRel slots scope mapping environment → StateRel model world initial store →
      ∃ reason finalStore, control = .fault (.language reason) ∧
        Core.Evaluates environment store (exit.rename mapping) (.inLeft .unit (.word reason)) finalStore ∧
        StateRel model world {initial with external := final} finalStore ∧ ClosuresPreserved store finalStore

theorem RevertPreservation.empty {σ : Type} (model : StateModel σ)
    (slots : List EffectSlot) (effects : Semantics.ExternalSemantics σ) :
    RevertPreservation (fun _ => False) model slots effects := by
  intro message initial control final impossible
  cases impossible

/-- Effects without a revert rule meet the obligation vacuously. -/
theorem RevertPreservation.unreachable {σ : Type} {supported : String → Prop} {model : StateModel σ}
    {slots : List EffectSlot} {effects : Semantics.ExternalSemantics σ}
    (unreachable : ∀ message state control final, effects.revert message state control final → False) :
    RevertPreservation supported model slots effects := by
  intro message initial control final _ reverted
  exact (unreachable _ _ _ _ reverted).elim

/-- An eligible revert statement simulates its lowering: the actual exit code
fails with the termination reason and the statement propagates it. -/
theorem RevertPreservation.statement {supported : String → Prop} {σ : Type} {model : StateModel σ}
    {slots : List EffectSlot} {effects : Semantics.ExternalSemantics σ} {signatures : List Signature}
    {codes : List GlobalCode} {locations : Nat → Nat} {captured : Core.Environment}
    {sourceEnvironment : Semantics.Environment}
    (reverting : RevertPreservation supported model slots effects) {span : Option Span} {message : String}
    {state : Semantics.State σ} {control : Semantics.Control} {final : σ}
    (available : supported "revert") (executed : effects.revert message state.external control final) :
    StmtSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment
      ⟨.revert message, span⟩ state control {state with external := final} := by
  intro fuel scope result loops expression compiled covered world mapping environment store _ _ runtime heap installed
  cases fuel with
  | zero => simp [lowerStatement, fail] at compiled
  | succ fuel =>
      simp only [lowerStatement] at compiled
      obtain ⟨exit, exitCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
      cases returned
      obtain ⟨reason, finalStore, rfl, exitEvaluated, finalHeap, closures⟩ :=
        reverting available executed exitCompiled runtime heap
      exact ⟨[], _, finalStore, .language reason, Core.LanguageResult.bind_failure _ exitEvaluated,
        by simpa only [List.append_nil] using finalHeap, installed.preserved closures, closures⟩

end Solcore.Frontend.RustHull.DerivationCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.YulCorrespondence
/-! The assembly boundary used by the common recursive proof. An eligible
inline Yul block is an external effect: the effect specification of the block
simulates the actual `YulLowering.lowerStatements` code of the statement. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.DerivationCorrespondence
open Correspondence ScalarExecution

def AssemblyPreservation {σ : Type} (supported : String → Prop) (model : StateModel σ)
    (slots : List EffectSlot) (effects : Semantics.ExternalSemantics σ) : Prop :=
  ∀ {functions : List Function} {sourceEnvironment : Semantics.Environment} {body : List YulStmt}
    {initial : Semantics.State σ} {control : Semantics.Control} {final : Semantics.State σ},
    YulFragment.Eligible supported body →
    effects.assembly functions sourceEnvironment body initial control final →
    ∀ {signatures : List Signature} {codes : List GlobalCode} {locations : Nat → Nat}
      {captured : Core.Environment} {span : Option Span},
      StmtSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment
        ⟨.assembly body, span⟩ initial control final

theorem AssemblyPreservation.empty {σ : Type} (model : StateModel σ)
    (slots : List EffectSlot) (effects : Semantics.ExternalSemantics σ) :
    AssemblyPreservation (fun _ => False) model slots effects := by
  intro functions sourceEnvironment body initial control final eligible
  exact (YulFragment.Eligible.empty eligible).elim

/-- Effects without an assembly rule meet the obligation vacuously. -/
theorem AssemblyPreservation.unreachable {σ : Type} {supported : String → Prop} {model : StateModel σ}
    {slots : List EffectSlot} {effects : Semantics.ExternalSemantics σ}
    (unreachable : ∀ functions environment body initial control final,
      effects.assembly functions environment body initial control final → False) :
    AssemblyPreservation supported model slots effects := by
  intro functions sourceEnvironment body initial control final _ assembled
  exact (unreachable _ _ _ _ _ _ assembled).elim

end Solcore.Frontend.RustHull.DerivationCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.DerivationProgramCorrespondence
/-! Finite independent Hull execution drives the mutual simulation proof.
Recursive function calls use their actual finite child derivations, without
restricting the program's call graph by a static rank. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.DerivationProgramCorrespondence
open Correspondence DerivationCorrespondence ScalarExecution

theorem function_preserves_effects {supported : String → Prop} {σ : Type} {model : StateModel σ} {slots : List EffectSlot} {effects : Semantics.ExternalSemantics σ}
    {fuel : Nat} {functions : List Function} {signatures : List Signature} {scope : Scope}
    {codes : List GlobalCode} {locations : Nat → Nat} {captured : Core.Environment}
    (signaturesCompiled : functions.mapM (signature fuel) = .ok signatures)
    (codesCompiled : CompiledGlobals fuel signatures scope (functions.zip signatures).reverse codes)
    (unique : (signatures.map Signature.name).Nodup)
    (covered : ScopeCoverage [] scope)
    (globals : GlobalEnvironmentRel codes locations scope Core.Renaming.id captured)
    (runtime : EffectEnvironmentRel slots scope Core.Renaming.id captured)
    (external : ExternalCallPreservation supported model slots effects)
    (reverting : RevertPreservation supported model slots effects)
    (assembling : AssemblyPreservation supported model slots effects)
    (eligible : ExecutableProgram supported functions)
    {function : Function} {sources : List Semantics.Value} {initial final : Semantics.State σ}
    {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction functions effects function sources initial result final) :
    FunctionMotive (model := model) functions signatures codes locations captured function sources initial result final := by
  refine Semantics.EvalFunction.rec
    (motive_1 := fun env expression initial result final _ =>
      ExprMotive (supported := supported) (model := model) (slots := slots) functions signatures codes locations captured env expression initial result final)
    (motive_2 := fun env expressions initial result final _ =>
      ExprsMotive (supported := supported) (model := model) (slots := slots) functions signatures codes locations captured env expressions initial result final)
    (motive_3 := fun name _ sources initial result final _ =>
      CallSimulation (model := model) functions signatures codes locations captured name sources initial result final)
    (motive_4 := fun function sources initial result final _ =>
      FunctionMotive (model := model) functions signatures codes locations captured function sources initial result final)
    (motive_5 := fun env statement initial control final _ =>
      StmtMotive (supported := supported) (model := model) (slots := slots) functions signatures codes locations captured env statement initial control final)
    (motive_6 := fun env statements initial control final _ =>
      StatementsMotive (supported := supported) (model := model) (slots := slots) functions signatures codes locations captured env statements initial control final)
    (motive_7 := fun env test post body initial control final _ =>
      LoopDerivationCorrespondence.LoopMotive (supported := supported) (model := model) (slots := slots) functions signatures codes locations captured
        env test post body initial control final)
    (motive_8 := fun env target value alternatives initial control final _ =>
      MatchDerivationCorrespondence.AlternativesMotive (supported := supported) (model := model) (slots := slots) functions signatures codes locations captured
        env target value alternatives initial control final)
    ?word
    ?bool
    ?unit
    ?var
    ?pair
    ?pairFault
    ?fst
    ?snd
    ?inl
    ?inr
    ?inK
    ?call
    ?callFault
    ?ifTrue
    ?ifFalse
    ?ifFault
    ?ifInvalid
    ?nil
    ?cons
    ?fault
    ?function
    ?primitive
    ?external
    ?body
    ?arity
    ?declare
    ?declareInvalid
    ?assign
    ?assignFault
    ?assignInvalid
    ?expression
    ?expressionFault
    ?returned
    ?returnFault
    ?block
    ?forInit
    ?forLoop
    ?breaking
    ?continuing
    ?matchStmt
    ?matchFault
    ?assembly
    ?revert
    ?comment
    ?nil_1
    ?declare_1
    ?declareInvalid_1
    ?next
    ?stop
    ?done
    ?conditionFault
    ?conditionInvalid
    ?step
    ?bodyBreak
    ?bodyStop
    ?postBreak
    ?postStop
    ?nil_2
    ?matched
    ?next_1
    evaluated

  case word =>
    intro env expression state text kind _
    exact DerivationCorrespondence.word kind
  case bool =>
    intro env expression state value kind _
    exact DerivationCorrespondence.bool kind
  case unit =>
    intro env expression state kind _
    exact DerivationCorrespondence.unit kind
  case var =>
    intro env expression state name kind _
    exact DerivationCorrespondence.var kind
  case pair =>
    intro env expression initial middle final left right leftValue rightResult kind first second firstIH secondIH accepted
    cases expression with | mk type expressionKind span =>
    cases kind
    cases accepted with
    | pair leftAccepted rightAccepted =>
        exact DerivationCorrespondence.pair (firstIH leftAccepted) (secondIH rightAccepted) type span
  case fst =>
    intro env expression initial final operand result kind operandEvaluated operandIH accepted
    cases expression with | mk type expressionKind span =>
    cases kind
    cases accepted with
    | fst operandAccepted => exact projection (operandIH operandAccepted) false type span
  case snd =>
    intro env expression initial final operand result kind operandEvaluated operandIH accepted
    cases expression with | mk type expressionKind span =>
    cases kind
    cases accepted with
    | snd operandAccepted => exact projection (operandIH operandAccepted) true type span
  case inl =>
    intro env expression initial final target operand result kind operandEvaluated operandIH accepted
    cases expression with | mk type expressionKind span =>
    cases kind
    cases accepted with
    | inl operandAccepted => exact injection (operandIH operandAccepted) false type target span
  case inr =>
    intro env expression initial final target operand result kind operandEvaluated operandIH accepted
    cases expression with | mk type expressionKind span =>
    cases kind
    cases accepted with
    | inr operandAccepted => exact injection (operandIH operandAccepted) true type target span
  case inK =>
    intro env expression initial final index target operand result kind operandEvaluated operandIH accepted
    cases expression with | mk type expressionKind span =>
    cases kind
    cases accepted with
    | inK operandAccepted => exact indexedInjection (operandIH operandAccepted) index type target span
  case call =>
    intro env expression initial middle final name arguments values result kind argumentsEvaluated called argumentsIH callIH accepted
    cases expression with | mk type expressionKind span =>
    cases kind
    have argumentsAccepted : ∀ argument ∈ arguments, ExecutableExpression supported functions argument := by
      cases accepted <;> assumption
    intro executionFuel executionScope lowered
    exact DerivationCallCorrespondence.call signaturesCompiled codesCompiled accepted external called
      (argumentsIH argumentsAccepted) callIH
  case ifTrue =>
    intro env expression initial middle final target condition yes no value result kind tested truth selected conditionIH branchIH accepted
    cases expression with | mk type expressionKind span =>
    cases kind
    cases accepted with
    | conditional conditionAccepted yesAccepted noAccepted =>
        exact conditional true truth (conditionIH conditionAccepted) (branchIH yesAccepted) type target span
  case ifFalse =>
    intro env expression initial middle final target condition yes no value result kind tested truth selected conditionIH branchIH accepted
    cases expression with | mk type expressionKind span =>
    cases kind
    cases accepted with
    | conditional conditionAccepted yesAccepted noAccepted =>
        exact conditional false truth (conditionIH conditionAccepted) (branchIH noAccepted) type target span
  case nil =>
    intro env state _
    exact DerivationCallCorrespondence.arguments_nil signatures codes locations captured env state
  case cons =>
    intro env expression rest initial middle final value values head tail headIH tailIH accepted
    exact DerivationCallCorrespondence.arguments_cons tail
      (headIH (accepted expression (List.mem_cons_self ..)))
      (tailIH (fun expression member => accepted expression (List.mem_cons_of_mem _ member)))
  case function =>
    intro name type arguments initial final function result selected called calledIH
    exact DerivationCallCorrespondence.call_function selected calledIH
  case primitive =>
    intro name type arguments state result absent computed
    exact DerivationCallCorrespondence.call_not_function absent
  case external =>
    intro name type arguments state result external absent notPrimitive called
    exact DerivationCallCorrespondence.call_not_function absent
  case body =>
    intro function arguments initial allocated final env control bound executed continued
    intro name code index selected signatureSelected codeFound
    obtain ⟨signatureCompiled, functionCompiled⟩ :=
      compiledFunction_at signaturesCompiled codesCompiled unique selected signatureSelected codeFound
    exact DerivationFunctionCorrespondence.function_simulation signatureCompiled functionCompiled covered globals runtime bound
      (continued (eligible function (List.mem_of_find?_eq_some selected)))
  case pairFault =>
    intro env expression initial final left right reason kind first firstIH accepted
    cases expression with | mk type expressionKind span =>
    cases kind
    cases accepted with
    | pair leftAccepted _ => exact pair_fault (firstIH leftAccepted) type span
  case callFault =>
    intro env expression initial final name arguments reason kind evaluated argumentsIH accepted
    cases expression with | mk type expressionKind span =>
    cases kind
    have argumentsAccepted : ∀ argument ∈ arguments, ExecutableExpression supported functions argument := by
      cases accepted <;> assumption
    intro executionFuel executionScope lowered
    exact DerivationCallCorrespondence.call_fault signaturesCompiled codesCompiled accepted
      (argumentsIH argumentsAccepted)
  case ifFault =>
    intro env expression initial final target condition yes no reason kind tested testIH accepted
    cases expression with | mk type expressionKind span =>
    cases kind
    cases accepted with
    | conditional testAccepted _ _ => exact conditional_fault (testIH testAccepted) type target span
  case fault =>
    intro env expression rest initial final reason evaluated headIH accepted
    exact DerivationCallCorrespondence.arguments_fault (headIH (accepted expression (List.mem_cons_self ..)))
  case ifInvalid =>
    intro env expression initial final target condition yes no value kind tested invalid testIH accepted
    cases expression with | mk type expressionKind span =>
    cases kind
    cases accepted with
    | conditional testAccepted _ _ =>
        exact conditional_invalid (testIH testAccepted) invalid type target span
  case arity =>
    intro function arguments state mismatch name code index selected signatureSelected codeFound
    obtain ⟨signatureCompiled, _⟩ :=
      compiledFunction_at signaturesCompiled codesCompiled unique selected signatureSelected codeFound
    exact DerivationFunctionCorrespondence.arity signatureCompiled mismatch
  case declareInvalid =>
    intro env statement initial name type kind zero _
    exact DerivationStatementCorrespondence.declared_invalid kind zero
  case declareInvalid_1 =>
    intro env statement rest name type state kind zero _
    exact DerivationStatementCorrespondence.declare_invalid kind zero
  case assignFault =>
    intro env statement lhs rhs initial final reason kind evaluated rhsIH accepted
    cases statement with | mk statementKind span =>
    cases kind
    simp only [ExecutableStatement] at accepted
    exact DerivationStatementCorrespondence.assign_fault rfl (rhsIH accepted)
  case assignInvalid =>
    intro env statement lhs rhs initial middle value reason kind evaluated invalid rhsIH accepted
    cases statement with | mk statementKind span =>
    cases kind
    simp only [ExecutableStatement] at accepted
    exact DerivationStatementCorrespondence.assign_invalid rfl (rhsIH accepted) invalid
  case expressionFault =>
    intro env statement value initial final reason kind evaluated valueIH accepted
    cases statement with | mk statementKind span =>
    cases kind
    exact DerivationStatementCorrespondence.expression_fault rfl
      (valueIH (by simpa only [ExecutableStatement] using accepted))
  case returnFault =>
    intro env statement value initial final reason kind evaluated valueIH accepted
    cases statement with | mk statementKind span =>
    cases kind
    exact DerivationStatementCorrespondence.return_fault rfl
      (valueIH (by simpa only [ExecutableStatement] using accepted))
  case matchFault =>
    intro env statement target expression alternatives initial final reason kind evaluated exprIH accepted
    cases statement with | mk statementKind span =>
    cases kind
    have parts : ExecutableExpression supported functions expression ∧
        (∀ alternative ∈ alternatives, ∀ statement ∈ alternative.body, ExecutableStatement supported functions statement) := by
      simpa only [ExecutableStatement] using accepted
    intro executionFuel executionScope resultType loops coreExpression
    exact MatchDerivationCorrespondence.fault (statement := ⟨.matchStmt target expression alternatives, span⟩) rfl (exprIH parts.1)
  case nil_2 =>
    intro env target value state _
    exact MatchDerivationCorrespondence.nil
  case matched =>
    intro env target value alternative rest initial final payload control selected executed bodyIH accepted
    exact MatchDerivationCorrespondence.matched selected
      (bodyIH (accepted alternative (List.mem_cons_self ..)))
  case next_1 =>
    intro env target value alternative rest initial final control rejected executed tailIH accepted
    exact MatchDerivationCorrespondence.next rejected
      (tailIH (fun other member => accepted other (List.mem_cons_of_mem _ member)))
  case matchStmt =>
    intro env statement target expression alternatives initial middle final value control
      kind evaluated selected exprIH altIH accepted
    cases statement with | mk statementKind span =>
    cases kind
    have parts : ExecutableExpression supported functions expression ∧
        (∀ alternative ∈ alternatives, ∀ statement ∈ alternative.body, ExecutableStatement supported functions statement) := by
      simpa only [ExecutableStatement] using accepted
    intro executionFuel executionScope resultType loops coreExpression
    exact MatchDerivationCorrespondence.statement (statement := ⟨.matchStmt target expression alternatives, span⟩) rfl (exprIH parts.1) (altIH parts.2)
  case assembly =>
    intro env statement body initial final control kind executed accepted
    cases statement with | mk statementKind span =>
    cases kind
    simp only [ExecutableStatement] at accepted
    exact assembling accepted executed
  case revert =>
    intro env statement message state external control kind executed accepted
    cases statement with | mk statementKind span =>
    cases kind
    simp only [ExecutableStatement] at accepted
    exact reverting.statement accepted executed
  case block =>
    intro env statement body initial final control kind evaluated bodyIH accepted
    cases statement with | mk statementKind span =>
    cases kind
    exact DerivationStatementCorrespondence.block rfl
      (bodyIH (by simpa only [ExecutableStatement] using accepted))
  case forInit =>
    intro env statement init test post body initial final control kind nonempty evaluated initIH accepted
    cases statement with | mk statementKind span =>
    cases kind
    have parts : (∀ statement ∈ init, ExecutableStatement supported functions statement) ∧
        ExecutableExpression supported functions test ∧
        (∀ statement ∈ post, ExecutableStatement supported functions statement) ∧
        (∀ statement ∈ body, ExecutableStatement supported functions statement) := by
      simpa only [ExecutableStatement] using accepted
    apply LoopDerivationCorrespondence.initialized_statement rfl nonempty
    apply initIH
    intro member selected
    rcases List.mem_append.mp selected with selected | selected
    · exact parts.1 member selected
    · simp only [List.mem_singleton] at selected
      subst member
      simpa only [ExecutableStatement, List.not_mem_nil, false_implies, implies_true, true_and] using parts.2
  case forLoop =>
    intro env statement test post body initial final control kind evaluated loopIH accepted
    cases statement with | mk statementKind span =>
    cases kind
    have parts : (∀ statement ∈ ([] : List Stmt), ExecutableStatement supported functions statement) ∧
        ExecutableExpression supported functions test ∧
        (∀ statement ∈ post, ExecutableStatement supported functions statement) ∧
        (∀ statement ∈ body, ExecutableStatement supported functions statement) := by
      simpa only [ExecutableStatement] using accepted
    intro executionFuel executionScope resultType loops coreExpression
    exact LoopDerivationCorrespondence.statement (statement := ⟨.forLoop [] test post body, span⟩) rfl (loopIH parts.2.1 parts.2.2.1 parts.2.2.2)
  case breaking =>
    intro env statement state kind _
    exact DerivationStatementCorrespondence.breaking kind
  case continuing =>
    intro env statement state kind _
    exact DerivationStatementCorrespondence.continuing kind
  case done =>
    intro env test post body initial final value tested truth testIH testEligible _ _
    exact LoopDerivationCorrespondence.done (testIH testEligible) truth
  case conditionFault =>
    intro env test post body initial final reason tested testIH testEligible _ _
    exact LoopDerivationCorrespondence.condition_fault (testIH testEligible)
  case conditionInvalid =>
    intro env test post body initial final value tested invalid testIH testEligible _ _
    exact LoopDerivationCorrespondence.condition_invalid (testIH testEligible) invalid
  case step =>
    intro env test post body initial testedState bodyState postState final value bodyControl postControl control
      tested truth bodyEvaluated bodyContinues postEvaluated postContinues next
      testIH bodyIH postIH nextIH testEligible postEligible bodyEligible
    exact LoopDerivationCorrespondence.step (testIH testEligible) truth
      (bodyIH bodyEligible) bodyContinues (postIH postEligible) postContinues
      (nextIH testEligible postEligible bodyEligible)
  case bodyBreak =>
    intro env test post body initial testedState final value tested truth bodyEvaluated
      testIH bodyIH testEligible _ bodyEligible
    exact LoopDerivationCorrespondence.body_break (testIH testEligible) truth (bodyIH bodyEligible)
  case bodyStop =>
    intro env test post body initial testedState final value control tested truth bodyEvaluated stopped
      testIH bodyIH testEligible _ bodyEligible
    exact LoopDerivationCorrespondence.body_stop (testIH testEligible) truth (bodyIH bodyEligible) stopped
  case postBreak =>
    intro env test post body initial testedState bodyState final value bodyControl tested truth
      bodyEvaluated bodyContinues postEvaluated testIH bodyIH postIH testEligible postEligible bodyEligible
    exact LoopDerivationCorrespondence.post_break (testIH testEligible) truth
      (bodyIH bodyEligible) bodyContinues (postIH postEligible)
  case postStop =>
    intro env test post body initial testedState bodyState final value bodyControl control tested truth
      bodyEvaluated bodyContinues postEvaluated stopped testIH bodyIH postIH testEligible postEligible bodyEligible
    exact LoopDerivationCorrespondence.post_stop (testIH testEligible) truth
      (bodyIH bodyEligible) bodyContinues (postIH postEligible) stopped
  case declare =>
    intro env statement initial name type value kind zero _
    exact DerivationStatementCorrespondence.declared kind zero
  case assign =>
    intro env statement lhs rhs initial middle final value kind evaluated assigned rhsIH accepted
    cases statement with | mk statementKind span =>
    cases kind
    simp only [ExecutableStatement] at accepted
    exact DerivationStatementCorrespondence.assign rfl (rhsIH accepted) assigned
  case expression =>
    intro env statement value initial final sourceValue kind evaluated valueIH accepted
    cases statement with | mk statementKind span =>
    cases kind
    have valueAccepted : ExecutableExpression supported functions value := by
      simpa only [ExecutableStatement] using accepted
    intro executionFuel executionScope resultType loops coreExpression
    exact DerivationStatementCorrespondence.expression_statement (statement := ⟨.expression value, span⟩) rfl (valueIH valueAccepted)
  case returned =>
    intro env statement value initial final sourceValue kind evaluated valueIH accepted
    cases statement with | mk statementKind span =>
    cases kind
    have valueAccepted : ExecutableExpression supported functions value := by
      simpa only [ExecutableStatement] using accepted
    intro executionFuel executionScope resultType loops coreExpression
    exact DerivationStatementCorrespondence.returned (statement := ⟨.returnStmt value, span⟩) rfl (valueIH valueAccepted)
  case comment =>
    intro env statement state text kind _
    exact DerivationStatementCorrespondence.comment kind
  case nil_1 =>
    intro env state _
    exact DerivationStatementCorrespondence.nil
  case declare_1 =>
    intro env statement rest initial final name type value control kind zero evaluated continued accepted
    exact DerivationStatementCorrespondence.declare kind zero
      (continued (fun statement member => accepted statement (List.mem_cons_of_mem _ member)))
  case next =>
    intro env statement rest initial middle final control notDeclaration head tail headIH tailIH accepted
    exact DerivationStatementCorrespondence.next notDeclaration
      (headIH (accepted statement (List.mem_cons_self ..)))
      (tailIH (fun statement member => accepted statement (List.mem_cons_of_mem _ member)))
  case stop =>
    intro env statement rest initial final control notDeclaration head stopped headIH accepted
    exact DerivationStatementCorrespondence.stop notDeclaration
      (headIH (accepted statement (List.mem_cons_self ..))) stopped

theorem function_preserves {σ : Type} {model : StateModel σ} {slots : List EffectSlot} {effects : Semantics.ExternalSemantics σ}
    {fuel : Nat} {functions : List Function} {signatures : List Signature} {scope : Scope}
    {codes : List GlobalCode} {locations : Nat → Nat} {captured : Core.Environment}
    (signaturesCompiled : functions.mapM (signature fuel) = .ok signatures)
    (codesCompiled : CompiledGlobals fuel signatures scope (functions.zip signatures).reverse codes)
    (unique : (signatures.map Signature.name).Nodup)
    (covered : ScopeCoverage [] scope)
    (globals : GlobalEnvironmentRel codes locations scope Core.Renaming.id captured)
    (runtime : EffectEnvironmentRel slots scope Core.Renaming.id captured)
    (eligible : RecursiveProgram functions)
    {function : Function} {sources : List Semantics.Value} {initial final : Semantics.State σ}
    {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction functions effects function sources initial result final) :
    FunctionMotive (model := model) functions signatures codes locations captured function sources initial result final :=
  function_preserves_effects signaturesCompiled codesCompiled unique covered globals runtime
    (ExternalCallPreservation.empty model slots effects) (RevertPreservation.empty model slots effects)
    (AssemblyPreservation.empty model slots effects) eligible evaluated

end Solcore.Frontend.RustHull.DerivationProgramCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.YulBlockCorrespondence
/-! The connected inline Yul fragment through the actual `YulLowering`
builders. The proof follows the source derivation: `let` allocates the fresh
cell the lowering allocates, an assignment writes the variable's cell, a
variable reads it, and a call binds its argument words from right to left
before the builtin code runs. A nested block, `if` or `switch` is joined to the
rest of its list by `LocalLoop.sequence`; its bodies are lowered in the
enclosing context, so their locals end with them, and any control other than
fallthrough stops the list. The code of an effect builtin is a separate
obligation, `BuiltinStep`, which the frame model meets; the word primitives
compile to pure Core code, which `primitive_step` proves for every model. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.YulBlockCorrespondence
open Core Correspondence StatementCorrespondence

/-- The continuation `lowerStatements` gives a block. -/
abbrev finish (resultType : Core.Ty) : YulLowering.Context → LowerM Core.Expr :=
  fun _ => pure (LocalLoop.fallthrough resultType)

theorem distinct_single (name : YulName) : YulLowering.distinctNames [name] = true := by
  simp only [YulLowering.distinctNames, List.map_cons, List.map_nil, decide_eq_true_eq]
  rfl

theorem words_checked {lowered : List Lowered} {done : PUnit}
    (checked : (forIn lowered PUnit.unit fun argument _ => do
        expectType Core.Ty.word argument.type
        pure (ForInStep.yield PUnit.unit) : LowerM PUnit) = .ok done) :
    ∀ argument ∈ lowered, argument.type = .word := by
  induction lowered with
  | nil => intro argument member; cases member
  | cons head rest restChecked =>
      simp only [List.forIn_cons] at checked
      obtain ⟨step, stepped, checked⟩ := lower_bind_eq_ok.mp checked
      obtain ⟨_, typed, stepped⟩ := lower_bind_eq_ok.mp stepped
      cases stepped
      intro argument member
      rcases List.mem_cons.mp member with rfl | member
      · exact (expectType_eq_of_ok typed).symm
      · exact restChecked checked argument member

/-- The accepted lowering of a builtin call: the argument lowerings, the actual
builtin code over word temporaries, and the right-to-left argument binds. -/
theorem expr_call {fuel : Nat} {context : YulLowering.Context} {name : YulName} {arguments : List YulExpr}
    {span : Option Span} {lowered : Lowered}
    (compiled : YulLowering.lowerExpr (fuel + 1) context ⟨.call name arguments, span⟩ = .ok lowered)
    (noFunctions : context.functions = []) (notUser : name.name.startsWith "usr$" = false)
    (builtin : Effects.supports name.name = true) :
    ∃ loweredArguments effect, arguments.mapM (YulLowering.lowerExpr fuel context) = .ok loweredArguments ∧
      (∀ argument ∈ loweredArguments, argument.type = .word) ∧
      Effects.lowerBuiltin (loweredArguments.foldl (fun scope _ => scope.temporary .word) context.scope)
        name.name ((List.range loweredArguments.length).map Core.Expr.var) = .ok effect ∧
      lowered = ⟨effect.type, YulLowering.bindArguments effect.type effect.expression 0 loweredArguments.reverse⟩ := by
  by_cases reserved : name.name.startsWith Effects.reservedPrefix
  · simp only [YulLowering.lowerExpr, reserved, ↓reduceIte] at compiled
    simp [fail, Bind.bind, Except.bind] at compiled
  · simp only [YulLowering.lowerExpr, reserved, Bool.false_eq_true, ↓reduceIte, noFunctions, List.find?_nil,
      notUser, builtin] at compiled
    obtain ⟨loweredArguments, argumentsCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
    obtain ⟨_, checked, compiled⟩ := lower_bind_eq_ok.mp compiled
    split at compiled
    · cases compiled
    obtain ⟨effect, effectCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
    cases compiled
    exact ⟨loweredArguments, effect, argumentsCompiled, words_checked checked, effectCompiled, rfl⟩

/-- The accepted lowering of a call of a word primitive: the argument
lowerings, the actual `RustYulPrimitives` code over word temporaries, and the
right-to-left argument binds. -/
theorem expr_primitive {fuel : Nat} {context : YulLowering.Context} {name : YulName} {arguments : List YulExpr}
    {span : Option Span} {lowered : Lowered}
    (compiled : YulLowering.lowerExpr (fuel + 1) context ⟨.call name arguments, span⟩ = .ok lowered)
    (noFunctions : context.functions = []) (notUser : name.name.startsWith "usr$" = false)
    (notEffect : Effects.supports name.name = false) :
    ∃ loweredArguments primitive, arguments.mapM (YulLowering.lowerExpr fuel context) = .ok loweredArguments ∧
      (∀ argument ∈ loweredArguments, argument.type = .word) ∧
      RustYulPrimitives.compile name.name ((List.range loweredArguments.length).map Core.Expr.var) =
        .ok primitive ∧
      lowered = ⟨primitive.type, YulLowering.bindArguments primitive.type
        (LanguageResult.success primitive.expression) 0 loweredArguments.reverse⟩ := by
  by_cases reserved : name.name.startsWith Effects.reservedPrefix
  · simp only [YulLowering.lowerExpr, reserved, ↓reduceIte] at compiled
    simp [fail, Bind.bind, Except.bind] at compiled
  · simp only [YulLowering.lowerExpr, reserved, Bool.false_eq_true, ↓reduceIte, noFunctions, List.find?_nil,
      notUser, notEffect] at compiled
    obtain ⟨loweredArguments, argumentsCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
    obtain ⟨_, checked, compiled⟩ := lower_bind_eq_ok.mp compiled
    split at compiled
    · cases compiled
    split at compiled
    · rename_i value primitiveCompiled
      obtain ⟨primitive, chosen, compiled⟩ := lower_bind_eq_ok.mp compiled
      cases chosen
      cases compiled
      exact ⟨loweredArguments, value, argumentsCompiled, words_checked checked, primitiveCompiled, rfl⟩
    · obtain ⟨_, failed, _⟩ := lower_bind_eq_ok.mp compiled
      cases failed

theorem expr_literal {fuel : Nat} {context : YulLowering.Context} {literal : YulLit} {span : Option Span}
    {lowered : Lowered}
    (compiled : YulLowering.lowerExpr (fuel + 1) context ⟨.literal literal, span⟩ = .ok lowered) :
    ∃ word, YulLowering.literalWord literal = .ok word ∧ lowered = ⟨.word, LanguageResult.success (.word word)⟩ := by
  simp only [YulLowering.lowerExpr] at compiled
  obtain ⟨word, parsed, compiled⟩ := lower_bind_eq_ok.mp compiled
  cases compiled
  exact ⟨word, parsed, rfl⟩

theorem expr_ident {fuel : Nat} {context : YulLowering.Context} {name : YulName} {span : Option Span}
    {lowered : Lowered}
    (compiled : YulLowering.lowerExpr (fuel + 1) context ⟨.ident name, span⟩ = .ok lowered) :
    ∃ binding index, context.scope.lookup name.name = .ok (binding, index) ∧ binding.type = .word ∧
      lowered = ⟨binding.type, if binding.reference then OptionalCell.read binding.type (.var index) (Word.ofNatModulo 1)
        else LanguageResult.success (.var index)⟩ := by
  by_cases reserved : name.name.startsWith Effects.reservedPrefix
  · simp only [YulLowering.lowerExpr, reserved, ↓reduceIte] at compiled
    simp [fail, Bind.bind, Except.bind] at compiled
  · simp only [YulLowering.lowerExpr, reserved, Bool.false_eq_true, ↓reduceIte] at compiled
    obtain ⟨value, read, compiled⟩ := lower_bind_eq_ok.mp compiled
    obtain ⟨_, typed, compiled⟩ := lower_bind_eq_ok.mp compiled
    cases compiled
    unfold Scope.read at read
    obtain ⟨⟨binding, index⟩, looked, read⟩ := lower_bind_eq_ok.mp read
    cases read
    exact ⟨binding, index, looked, (expectType_eq_of_ok typed).symm, rfl⟩

theorem sequence_nil {fuel : Nat} {context : YulLowering.Context} {resultType : Core.Ty} {inLoop : Bool}
    {code : Core.Expr}
    (compiled : YulLowering.lowerSequence fuel context resultType inLoop [] (finish resultType) = .ok code) :
    code = LocalLoop.fallthrough resultType := by
  cases fuel with
  | zero => cases compiled
  | succ fuel =>
      simp only [YulLowering.lowerSequence] at compiled
      exact (Except.ok.inj compiled).symm

theorem sequence_letValue {fuel : Nat} {context : YulLowering.Context} {resultType : Core.Ty} {inLoop : Bool}
    {name : YulName} {value : YulExpr} {span : Option Span} {rest : List YulStmt} {code : Core.Expr}
    (compiled : YulLowering.lowerSequence fuel context resultType inLoop
      (⟨.letDecl [name] (some value), span⟩ :: rest) (finish resultType) = .ok code) :
    ∃ previous lowered continuation, fuel = previous + 1 ∧
      name.name.startsWith Effects.reservedPrefix = false ∧
      YulLowering.lowerExpr previous context value = .ok lowered ∧ lowered.type = .word ∧
      YulLowering.lowerSequence previous ((context.temporary .word).addLocal name.name) resultType inLoop rest
        (finish resultType) = .ok continuation ∧
      code = LanguageResult.bind (LocalLoop.controlType resultType) lowered.expression
        (.letE (OptionalCell.allocateInitialized .word (.var 0)) continuation) := by
  cases fuel with
  | zero => cases compiled
  | succ fuel =>
  by_cases reserved : name.name.startsWith Effects.reservedPrefix
  · simp only [YulLowering.lowerSequence, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, distinct_single,
      Bool.not_true, List.forIn_cons, List.forIn_nil, reserved] at compiled
    simp [fail, Bind.bind, Except.bind] at compiled
  · simp only [YulLowering.lowerSequence, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, distinct_single,
      Bool.not_true, List.forIn_cons, List.forIn_nil, reserved, pure_bind] at compiled
    obtain ⟨lowered, valueCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
    obtain ⟨_, typed, compiled⟩ := lower_bind_eq_ok.mp compiled
    have wordType : lowered.type = .word := (expectType_eq_of_ok typed).symm
    obtain ⟨continuation, continuationCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
    cases compiled
    rw [wordType] at continuationCompiled
    exact ⟨fuel, lowered, continuation, rfl, by simpa using reserved, valueCompiled, wordType, continuationCompiled, rfl⟩

theorem sequence_letZero {fuel : Nat} {context : YulLowering.Context} {resultType : Core.Ty} {inLoop : Bool}
    {name : YulName} {span : Option Span} {rest : List YulStmt} {code : Core.Expr}
    (compiled : YulLowering.lowerSequence fuel context resultType inLoop
      (⟨.letDecl [name] none, span⟩ :: rest) (finish resultType) = .ok code) :
    ∃ previous continuation, fuel = previous + 1 ∧
      name.name.startsWith Effects.reservedPrefix = false ∧
      YulLowering.lowerSequence previous (context.addLocal name.name) resultType inLoop rest
        (finish resultType) = .ok continuation ∧
      code = .letE (OptionalCell.allocateInitialized .word (.word Word.zero)) continuation := by
  cases fuel with
  | zero => cases compiled
  | succ fuel =>
  by_cases reserved : name.name.startsWith Effects.reservedPrefix
  · simp only [YulLowering.lowerSequence, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, distinct_single,
      Bool.not_true, List.forIn_cons, List.forIn_nil, reserved] at compiled
    simp [fail, Bind.bind, Except.bind] at compiled
  · simp only [YulLowering.lowerSequence, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, distinct_single,
      Bool.not_true, List.forIn_cons, List.forIn_nil, reserved, pure_bind] at compiled
    obtain ⟨continuation, continuationCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
    cases compiled
    exact ⟨fuel, continuation, rfl, by simpa using reserved, continuationCompiled, rfl⟩

theorem sequence_expression {fuel : Nat} {context : YulLowering.Context} {resultType : Core.Ty} {inLoop : Bool}
    {value : YulExpr} {span : Option Span} {rest : List YulStmt} {code : Core.Expr}
    (compiled : YulLowering.lowerSequence fuel context resultType inLoop
      (⟨.expression value, span⟩ :: rest) (finish resultType) = .ok code) :
    ∃ previous lowered next, fuel = previous + 1 ∧
      YulLowering.lowerExpr previous context value = .ok lowered ∧ lowered.type = .unit ∧
      YulLowering.lowerSequence previous context resultType inLoop rest (finish resultType) = .ok next ∧
      code = LocalSequence.discard (LocalLoop.controlType resultType) lowered.expression next := by
  cases fuel with
  | zero => cases compiled
  | succ fuel =>
      simp only [YulLowering.lowerSequence] at compiled
      obtain ⟨lowered, valueCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
      obtain ⟨_, typed, compiled⟩ := lower_bind_eq_ok.mp compiled
      obtain ⟨next, nextCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
      cases compiled
      exact ⟨fuel, lowered, next, rfl, valueCompiled, (expectType_eq_of_ok typed).symm, nextCompiled, rfl⟩

theorem sequence_assign {fuel : Nat} {context : YulLowering.Context} {resultType : Core.Ty} {inLoop : Bool}
    {name : YulName} {value : YulExpr} {span : Option Span} {rest : List YulStmt} {code : Core.Expr}
    (compiled : YulLowering.lowerSequence fuel context resultType inLoop
      (⟨.assign [name] value, span⟩ :: rest) (finish resultType) = .ok code) :
    ∃ previous lowered next binding index, fuel = previous + 1 ∧
      YulLowering.lowerExpr previous context value = .ok lowered ∧ lowered.type = .word ∧
      YulLowering.lowerSequence previous context resultType inLoop rest (finish resultType) = .ok next ∧
      context.scope.lookup name.name = .ok (binding, index) ∧ binding.reference = true ∧ binding.type = .word ∧
      code = LanguageResult.bind (LocalLoop.controlType resultType) lowered.expression
        (.letE (.storeCell (.var (index + 1)) (.inRight .unit (.var 0))) ((next.weakenAt 0).weakenAt 0)) := by
  cases fuel with
  | zero => cases compiled
  | succ fuel =>
      simp only [YulLowering.lowerSequence] at compiled
      obtain ⟨lowered, valueCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
      obtain ⟨next, nextCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
      simp only [YulLowering.assignMany, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] at compiled
      obtain ⟨_, typed, compiled⟩ := lower_bind_eq_ok.mp compiled
      obtain ⟨writes, written, compiled⟩ := lower_bind_eq_ok.mp compiled
      cases compiled
      have zipped : [name].zipIdx = [(name, 0)] := rfl
      simp only [zipped, List.mapM_cons, List.mapM_nil] at written
      obtain ⟨write, writeCompiled, written⟩ := lower_bind_eq_ok.mp written
      obtain ⟨others, othersDone, written⟩ := lower_bind_eq_ok.mp written
      cases othersDone
      cases written
      by_cases reserved : name.name.startsWith Effects.reservedPrefix
      · simp only [reserved, ↓reduceIte] at writeCompiled
        simp [fail, Bind.bind, Except.bind] at writeCompiled
      · simp only [reserved, Bool.false_eq_true, ↓reduceIte] at writeCompiled
        obtain ⟨⟨binding, index⟩, looked, writeCompiled⟩ := lower_bind_eq_ok.mp writeCompiled
        by_cases reference : binding.reference = true
        · simp only [reference, ↓reduceIte] at writeCompiled
          obtain ⟨_, bindingTyped, writeCompiled⟩ := lower_bind_eq_ok.mp writeCompiled
          cases writeCompiled
          exact ⟨fuel, lowered, next, binding, index, rfl, valueCompiled, (expectType_eq_of_ok typed).symm,
            nextCompiled, looked, reference, (expectType_eq_of_ok bindingTyped).symm, rfl⟩
        · simp only [reference, Bool.false_eq_true, ↓reduceIte] at writeCompiled
          simp [fail, Bind.bind, Except.bind] at writeCompiled

theorem declarations_empty {supported : String → Prop} {statements : List YulStmt}
    (eligible : ∀ statement ∈ statements, YulFragment.StatementEligible supported statement) :
    YulLowering.declarations statements = .ok [] := by
  unfold YulLowering.declarations
  rw [List.filterMap_eq_nil_iff.mpr ?_]
  · rfl
  · intro statement member
    cases eligible statement member <;> rfl

/-- A body of the fragment declares no local functions, so its lowering is its
statement sequence in the same context. -/
theorem block_sequence {supported : String → Prop} {fuel : Nat} {context : YulLowering.Context}
    {resultType : Core.Ty} {inLoop : Bool} {statements : List YulStmt} {code : Core.Expr}
    (eligible : ∀ statement ∈ statements, YulFragment.StatementEligible supported statement)
    (compiled : YulLowering.lowerBlock fuel context resultType inLoop statements (finish resultType) = .ok code) :
    ∃ previous, YulLowering.lowerSequence previous context resultType inLoop statements (finish resultType) =
      .ok code := by
  cases fuel with
  | zero => cases compiled
  | succ fuel =>
      simp only [YulLowering.lowerBlock] at compiled
      obtain ⟨functions, declared, compiled⟩ := lower_bind_eq_ok.mp compiled
      rw [declarations_empty eligible] at declared
      cases declared
      obtain ⟨closures, closed, compiled⟩ := lower_bind_eq_ok.mp compiled
      simp only [List.mapM_nil] at closed
      cases closed
      obtain ⟨body, bodyCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
      cases compiled
      exact ⟨fuel, bodyCompiled⟩

theorem statements_sequence {supported : String → Prop} {fuel : Nat} {scope : Scope} {resultType : Core.Ty}
    {statements : List YulStmt} {signatures : List Signature} {code : Core.Expr}
    (eligible : ∀ statement ∈ statements, YulFragment.StatementEligible supported statement)
    (compiled : YulLowering.lowerStatements fuel scope resultType statements signatures = .ok code) :
    ∃ previous, YulLowering.lowerSequence previous {scope, hullFunctions := signatures} resultType false statements
      (finish resultType) = .ok code := by
  unfold YulLowering.lowerStatements at compiled
  obtain ⟨_, _, compiled⟩ := lower_bind_eq_ok.mp compiled
  exact block_sequence eligible compiled

/-- The case keys and lowered bodies of a `switch`. -/
inductive Arms (fuel : Nat) (context : YulLowering.Context) (resultType : Core.Ty) (inLoop : Bool) :
    List YulCase → List (Word × Core.Expr) → Prop where
  | nil : Arms fuel context resultType inLoop [] []
  | cons {arm : YulCase} {key : Word} {code : Core.Expr} {cases : List YulCase}
      {branches : List (Word × Core.Expr)} (keyed : YulLowering.literalWord arm.lit = .ok key)
      (lowered : YulLowering.lowerBlock fuel context resultType inLoop arm.body (finish resultType) = .ok code)
      (tail : Arms fuel context resultType inLoop cases branches) :
      Arms fuel context resultType inLoop (arm :: cases) ((key, code) :: branches)

theorem arms_of_mapM {fuel : Nat} {context : YulLowering.Context} {resultType : Core.Ty} {inLoop : Bool}
    {lower : YulCase → LowerM (Word × Core.Expr)}
    (characterized : ∀ {arm : YulCase} {key : Word} {code : Core.Expr}, lower arm = .ok (key, code) →
      YulLowering.literalWord arm.lit = .ok key ∧
        YulLowering.lowerBlock fuel context resultType inLoop arm.body (finish resultType) = .ok code) :
    ∀ {cases : List YulCase} {branches : List (Word × Core.Expr)}, cases.mapM lower = .ok branches →
      Arms fuel context resultType inLoop cases branches
  | [], branches, mapped => by
      simp only [List.mapM_nil] at mapped
      cases mapped
      exact .nil
  | arm :: cases, branches, mapped => by
      simp only [List.mapM_cons] at mapped
      obtain ⟨⟨key, code⟩, first, mapped⟩ := lower_bind_eq_ok.mp mapped
      obtain ⟨others, rest, mapped⟩ := lower_bind_eq_ok.mp mapped
      cases mapped
      obtain ⟨keyed, lowered⟩ := characterized first
      exact .cons keyed lowered (arms_of_mapM characterized rest)

/-- The lowered code of a statement with nested bodies, before
`LocalLoop.sequence` joins it to the rest of the list. -/
def CompoundLowering (fuel : Nat) (context : YulLowering.Context) (resultType : Core.Ty) (inLoop : Bool) :
    YulStmt → Core.Expr → Prop
  | ⟨.block body, _⟩, head => YulLowering.lowerBlock fuel context resultType inLoop body (finish resultType) = .ok head
  | ⟨.ifThen condition body, _⟩, head => ∃ lowered tested branch,
      YulLowering.lowerExpr fuel context condition = .ok lowered ∧ YulLowering.condition lowered = .ok tested ∧
      YulLowering.lowerBlock fuel context resultType inLoop body (finish resultType) = .ok branch ∧
      head = LocalLoop.conditional resultType tested branch (LocalLoop.fallthrough resultType)
  | ⟨.switch value cases defaultBody, _⟩, head => ∃ lowered branches defaultCode,
      YulLowering.lowerExpr fuel context value = .ok lowered ∧ lowered.type = .word ∧
      Arms fuel context resultType inLoop cases branches ∧
      YulLowering.lowerBlock fuel context resultType inLoop (defaultBody.getD []) (finish resultType) =
        .ok defaultCode ∧
      head = LanguageResult.bind (LocalLoop.controlType resultType) lowered.expression
        (YulLowering.switchBranches branches defaultCode)
  | _, _ => False

def IsCompound : YulStmt → Prop
  | ⟨.block _, _⟩ | ⟨.ifThen _ _, _⟩ | ⟨.switch _ _ _, _⟩ => True
  | _ => False

theorem sequence_compound {fuel : Nat} {context : YulLowering.Context} {resultType : Core.Ty} {inLoop : Bool}
    {statement : YulStmt} {rest : List YulStmt} {code : Core.Expr} (compound : IsCompound statement)
    (compiled : YulLowering.lowerSequence fuel context resultType inLoop (statement :: rest) (finish resultType) =
      .ok code) :
    ∃ previous head next, fuel = previous + 1 ∧ CompoundLowering previous context resultType inLoop statement head ∧
      YulLowering.lowerSequence previous context resultType inLoop rest (finish resultType) = .ok next ∧
      code = LocalLoop.sequence resultType head next := by
  cases fuel with
  | zero => cases compiled
  | succ fuel =>
  obtain ⟨kind, span⟩ := statement
  cases kind
  all_goals try exact False.elim compound
  case block body =>
    simp only [YulLowering.lowerSequence] at compiled
    obtain ⟨head, headCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
    obtain ⟨next, nextCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
    cases compiled
    exact ⟨fuel, head, next, rfl, headCompiled, nextCompiled, rfl⟩
  case ifThen condition body =>
    simp only [YulLowering.lowerSequence] at compiled
    obtain ⟨lowered, loweredCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
    obtain ⟨tested, testedCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
    obtain ⟨branch, branchCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
    obtain ⟨next, nextCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
    cases compiled
    exact ⟨fuel, _, next, rfl, ⟨lowered, tested, branch, loweredCompiled, testedCompiled, branchCompiled, rfl⟩,
      nextCompiled, rfl⟩
  case switch value cases defaultBody =>
    simp only [YulLowering.lowerSequence] at compiled
    obtain ⟨lowered, loweredCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
    obtain ⟨_, typed, compiled⟩ := lower_bind_eq_ok.mp compiled
    obtain ⟨branches, branchesCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
    split at compiled
    · obtain ⟨defaultCode, defaultCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
      obtain ⟨next, nextCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
      cases compiled
      refine ⟨fuel, _, next, rfl, ⟨lowered, branches, defaultCode, loweredCompiled, (expectType_eq_of_ok typed).symm,
        arms_of_mapM ?_ branchesCompiled, defaultCompiled, rfl⟩, nextCompiled, rfl⟩
      intro arm key code mapped
      obtain ⟨_, keyed, mapped⟩ := lower_bind_eq_ok.mp mapped
      obtain ⟨_, lowered, mapped⟩ := lower_bind_eq_ok.mp mapped
      cases mapped
      exact ⟨keyed, lowered⟩
    · simp [fail, Bind.bind, Except.bind] at compiled

theorem condition_components {lowered : Lowered} {tested : Core.Expr}
    (compiled : YulLowering.condition lowered = .ok tested) :
    lowered.type = .word ∧ tested = LanguageResult.bind .bool lowered.expression
      (LanguageResult.success (.unary .boolNot (.binary .wordEq (.var 0) (.word Word.zero)))) := by
  unfold YulLowering.condition at compiled
  obtain ⟨_, typed, compiled⟩ := lower_bind_eq_ok.mp compiled
  cases compiled
  exact ⟨(expectType_eq_of_ok typed).symm, rfl⟩

/-- The argument lowerings of a call, each a word. -/
inductive Lowers (fuel : Nat) (context : YulLowering.Context) : List YulExpr → List Lowered → Prop where
  | nil : Lowers fuel context [] []
  | cons {expression : YulExpr} {lowered : Lowered} {expressions : List YulExpr} {loweredArguments : List Lowered}
      (head : YulLowering.lowerExpr fuel context expression = .ok lowered) (typed : lowered.type = .word)
      (tail : Lowers fuel context expressions loweredArguments) :
      Lowers fuel context (expression :: expressions) (lowered :: loweredArguments)

theorem Lowers.concat {fuel : Nat} {context : YulLowering.Context} :
    ∀ {expressions : List YulExpr} {loweredArguments : List Lowered}, Lowers fuel context expressions loweredArguments →
      ∀ {expression : YulExpr} {lowered : Lowered}, YulLowering.lowerExpr fuel context expression = .ok lowered →
        lowered.type = .word → Lowers fuel context (expressions ++ [expression]) (loweredArguments ++ [lowered])
  | _, _, .nil, _, _, head, typed => .cons head typed .nil
  | _, _, .cons first firstTyped tail, _, _, head, typed => .cons first firstTyped (tail.concat head typed)

theorem Lowers.reverse {fuel : Nat} {context : YulLowering.Context} :
    ∀ {expressions : List YulExpr} {loweredArguments : List Lowered}, Lowers fuel context expressions loweredArguments →
      Lowers fuel context expressions.reverse loweredArguments.reverse
  | _, _, .nil => .nil
  | _, _, .cons head typed tail => by
      simp only [List.reverse_cons]
      exact tail.reverse.concat head typed

theorem lowers_of_mapM {fuel : Nat} {context : YulLowering.Context} :
    ∀ {expressions : List YulExpr} {loweredArguments : List Lowered},
      expressions.mapM (YulLowering.lowerExpr fuel context) = .ok loweredArguments →
      (∀ lowered ∈ loweredArguments, lowered.type = .word) → Lowers fuel context expressions loweredArguments
  | [], loweredArguments, mapped, _ => by
      simp only [List.mapM_nil] at mapped
      cases mapped
      exact .nil
  | expression :: expressions, loweredArguments, mapped, typed => by
      simp only [List.mapM_cons] at mapped
      obtain ⟨lowered, head, mapped⟩ := lower_bind_eq_ok.mp mapped
      obtain ⟨others, tail, mapped⟩ := lower_bind_eq_ok.mp mapped
      cases mapped
      exact .cons head (typed lowered (List.mem_cons.mpr (.inl rfl)))
        (lowers_of_mapM tail fun other member => typed other (List.mem_cons.mpr (.inr member)))

/-- The renaming under `count` Core binders. -/
def liftN (mapping : Renaming) : Nat → Renaming
  | 0 => mapping
  | count + 1 => (liftN mapping count).lift

theorem liftN_below (mapping : Renaming) : ∀ {count index : Nat}, index < count → liftN mapping count index = index
  | count + 1, 0, _ => rfl
  | count + 1, index + 1, below => by
      show liftN mapping count index + 1 = index + 1
      rw [liftN_below mapping (Nat.lt_of_succ_lt_succ below)]

theorem liftN_add (mapping : Renaming) : ∀ (count index : Nat), liftN mapping count (index + count) = mapping index + count
  | 0, _ => rfl
  | count + 1, index => by
      show liftN mapping count (index + count) + 1 = mapping index + (count + 1)
      rw [liftN_add mapping count index]
      rfl

/-- An argument lowered in the call's scope and bound under `count` earlier
argument words. -/
theorem shifted_rename (expression : Core.Expr) (mapping : Renaming) (count : Nat) :
    (expression.rename (· + count)).rename (liftN mapping count) =
      expression.rename (fun index => count + mapping index) := by
  rw [Expr.rename_comp]
  congr 1
  funext index
  show liftN mapping count (index + count) = count + mapping index
  rw [liftN_add, Nat.add_comm]

theorem weakened_once (expression : Core.Expr) (mapping : Renaming) :
    (expression.weakenAt 0).rename mapping.lift = expression.rename (fun index => 1 + mapping index) := by
  rw [LocalLoop.rename_weaken_zero, LocalLoop.weaken_zero, Expr.rename_comp]
  rfl

theorem weakened_twice (expression : Core.Expr) (mapping : Renaming) :
    ((expression.weakenAt 0).weakenAt 0).rename mapping.lift.lift =
      expression.rename (fun index => 2 + mapping index) := by
  rw [LocalLoop.rename_weaken_zero, LocalLoop.rename_weaken_zero, LocalLoop.weaken_zero, LocalLoop.weaken_zero,
    LocalLoop.rename_shift, Expr.rename_comp]
  rfl

theorem renamed_weakened (expression : Core.Expr) (mapping : Renaming) :
    (expression.rename mapping).weakenAt 0 = expression.rename (fun index => 1 + mapping index) := by
  rw [LocalLoop.weaken_zero, Expr.rename_comp]
  rfl

/-- Builtin argument temporaries hide no effect slot. -/
theorem temporaries_lookup {α : Type} : ∀ (items : List α) (scope : Scope) {name : String} {binding : Binding}
    {index : Nat}, (items.foldl (fun scope _ => scope.temporary .word) scope).lookup name = .ok (binding, index) →
    ∃ previous, scope.lookup name = .ok (binding, previous) ∧ index = previous + items.length
  | [], _, _, _, index, looked => ⟨index, looked, rfl⟩
  | _ :: rest, scope, name, binding, _, looked => by
      obtain ⟨middle, middleLooked, rfl⟩ := temporaries_lookup rest (scope.temporary .word) looked
      rw [Scope.temporary, scope_lookup_cons] at middleLooked
      simp only [Option.none_beq_some, Bool.false_eq_true, ↓reduceIte] at middleLooked
      cases previous : scope.lookup name with
      | error error => simp only [previous] at middleLooked; contradiction
      | ok found =>
          rcases found with ⟨oldBinding, oldIndex⟩
          simp only [previous, Except.ok.injEq, Prod.mk.injEq] at middleLooked
          obtain ⟨rfl, rfl⟩ := middleLooked
          refine ⟨oldIndex, rfl, ?_⟩
          simp only [List.length_cons]
          omega

theorem temporaries_related {slots : List EffectSlot} {scope : Scope} {mapping : Renaming}
    {environment : Environment} (related : EffectEnvironmentRel slots scope mapping environment)
    {α : Type} (items : List α) (values : Environment) (length : values.length = items.length) :
    EffectEnvironmentRel slots (items.foldl (fun scope _ => scope.temporary .word) scope)
      (liftN mapping items.length) (values ++ environment) := by
  intro slot member binding index looked
  obtain ⟨previous, previousLooked, rfl⟩ := temporaries_lookup items scope looked
  rw [liftN_add, ← length, List.getElem?_append_right (Nat.le_add_left _ _), Nat.add_sub_cancel]
  exact related slot member binding previous previousLooked

theorem word_result {source : Word} {target : Value} (related : ResultRel .word (.value (.word source)) target) :
    target = .inRight .word (.word source) := by
  cases related with
  | value related =>
      cases related
      rfl

theorem unit_result {target : Value} (related : ResultRel .unit (.value .unit) target) :
    target = .inRight .word .unit := by
  cases related with
  | value related =>
      cases related
      rfl

theorem literal_word {literal : YulLit} {lowered source : Word}
    (compiled : YulLowering.literalWord literal = .ok lowered)
    (evaluated : YulSemantics.literalWord? literal = some source) : lowered = source := by
  cases literal with
  | number text | hex text =>
      have parsed := Correspondence.parseWord_some_of_ok compiled
      exact Option.some.inj (parsed.symm.trans evaluated)
  | bool value =>
      exact (Except.ok.inj compiled).symm.trans (Option.some.inj evaluated)
  | string text => cases evaluated

theorem literal_word_some {literal : YulLit} {word : Word} (compiled : YulLowering.literalWord literal = .ok word)
    (notString : ∀ text, literal ≠ .string text) : YulSemantics.literalWord? literal = some word := by
  cases literal with
  | number text | hex text => exact Correspondence.parseWord_some_of_ok compiled
  | bool value => exact congrArg some (Except.ok.inj compiled)
  | string text => exact (notString text rfl).elim

theorem select_mem {word : Word} : ∀ {cases : List YulCase} {body : List YulStmt},
    YulSemantics.select word cases = some body → ∃ arm ∈ cases, arm.body = body
  | [], _, selected => by cases selected
  | arm :: rest, body, selected => by
      simp only [YulSemantics.select] at selected
      split at selected
      · cases selected
        exact ⟨arm, List.mem_cons.mpr (.inl rfl), rfl⟩
      · obtain ⟨other, member, same⟩ := select_mem selected
        exact ⟨other, List.mem_cons.mpr (.inr member), same⟩

/-- The chain of case tests reaches the body of the first case whose key is the
scrutinee word. -/
theorem switch_selected {fuel : Nat} {context : YulLowering.Context} {resultType : Core.Ty} {inLoop : Bool}
    {mapping : Renaming} {environment : Environment} {word : Word} :
    ∀ {cases : List YulCase} {branches : List (Word × Core.Expr)} {body : List YulStmt},
      Arms fuel context resultType inLoop cases branches → (∀ arm ∈ cases, ∀ text, arm.lit ≠ .string text) →
      YulSemantics.select word cases = some body →
      ∃ code, YulLowering.lowerBlock fuel context resultType inLoop body (finish resultType) = .ok code ∧
        ∀ {defaultCode : Core.Expr} {store finalStore : Store} {result : Value},
          Evaluates (.word word :: environment) store (code.rename (fun index => 1 + mapping index)) result
            finalStore →
          Evaluates (.word word :: environment) store
            ((YulLowering.switchBranches branches defaultCode).rename mapping.lift) result finalStore
  | _, _, _, .nil, _, selected => by cases selected
  | arm :: _, (key, code) :: _, _, .cons keyed lowered tail, literals, selected => by
      have source := literal_word_some keyed (literals arm (List.mem_cons.mpr (.inl rfl)))
      simp only [YulSemantics.select] at selected
      by_cases same : YulSemantics.literalWord? arm.lit = some word
      · rw [if_pos same] at selected
        cases selected
        have equal : key = word := Option.some.inj (source.symm.trans same)
        subst equal
        refine ⟨code, lowered, fun evaluated => ?_⟩
        apply Evaluates.ifTrue (.binary (.var rfl) .word (by simp [BinaryOp.apply]))
        rw [weakened_once]
        exact evaluated
      · rw [if_neg same] at selected
        obtain ⟨found, foundLowered, chain⟩ :=
          switch_selected tail (fun other member => literals other (List.mem_cons.mpr (.inr member))) selected
        refine ⟨found, foundLowered, fun evaluated => ?_⟩
        have different : word ≠ key := fun equal => same (equal ▸ source)
        apply Evaluates.ifFalse (.binary (.var rfl) .word (by simp [BinaryOp.apply, different]))
        exact chain evaluated

/-- Without a matching case the chain of case tests reaches the default body. -/
theorem switch_unselected {fuel : Nat} {context : YulLowering.Context} {resultType : Core.Ty} {inLoop : Bool}
    {mapping : Renaming} {environment : Environment} {word : Word} :
    ∀ {cases : List YulCase} {branches : List (Word × Core.Expr)},
      Arms fuel context resultType inLoop cases branches → (∀ arm ∈ cases, ∀ text, arm.lit ≠ .string text) →
      YulSemantics.select word cases = none →
      ∀ {defaultCode : Core.Expr} {store finalStore : Store} {result : Value},
        Evaluates (.word word :: environment) store (defaultCode.rename (fun index => 1 + mapping index)) result
          finalStore →
        Evaluates (.word word :: environment) store
          ((YulLowering.switchBranches branches defaultCode).rename mapping.lift) result finalStore
  | _, _, .nil, _, _, defaultCode, _, _, _, evaluated => by
      show Evaluates _ _ ((defaultCode.weakenAt 0).rename mapping.lift) _ _
      rw [weakened_once]
      exact evaluated
  | arm :: _, (key, _) :: _, .cons keyed _ tail, literals, unselected, _, _, _, _, evaluated => by
      have source := literal_word_some keyed (literals arm (List.mem_cons.mpr (.inl rfl)))
      simp only [YulSemantics.select] at unselected
      by_cases same : YulSemantics.literalWord? arm.lit = some word
      · rw [if_pos same] at unselected
        cases unselected
      · rw [if_neg same] at unselected
        have different : word ≠ key := fun equal => same (equal ▸ source)
        apply Evaluates.ifFalse (.binary (.var rfl) .word (by simp [BinaryOp.apply, different]))
        exact switch_unselected tail (fun other member => literals other (List.mem_cons.mpr (.inr member)))
          unselected evaluated

theorem condition_evaluates {environment : Environment} {store finalStore : Store} {mapping : Renaming}
    {expression : Core.Expr} {word : Word}
    (evaluated : Evaluates environment store (expression.rename mapping) (.inRight .word (.word word)) finalStore) :
    Evaluates environment store ((LanguageResult.bind .bool expression
        (LanguageResult.success (.unary .boolNot (.binary .wordEq (.var 0) (.word Word.zero))))).rename mapping)
      (.inRight .word (.bool (!(word == Word.zero)))) finalStore :=
  LanguageResult.bind_success .bool evaluated
    (LanguageResult.success_evaluates (.unary (.binary (.var rfl) .word rfl) rfl))

/-- A nested statement that falls through continues with the rest of the list
under the three binders of `LocalLoop.sequence`. -/
theorem sequence_next {type : Core.Ty} {first next : Core.Expr} {mapping : Renaming} {environment : Environment}
    {initial middle final : Store} {result : Value}
    (firstEvaluated : Evaluates environment initial (first.rename mapping) (LocalLoop.fallthroughValue type) middle)
    (nextEvaluated : Evaluates
      (.unit :: .inLeft type .unit :: .inLeft LocalLoop.transferType (.inLeft type .unit) :: environment)
      middle (next.rename (fun index => 3 + mapping index)) result final) :
    Evaluates environment initial ((LocalLoop.sequence type first next).rename mapping) result final :=
  StatementCorrespondence.sequence_fallthrough firstEvaluated (by simpa only [Nat.add_comm] using nextEvaluated)

/-- Any other control of a nested statement stops the list. -/
theorem sequence_stopped {type : Core.Ty} {first next : Core.Expr} {mapping : Renaming} {environment : Environment}
    {initial final : Store} {control : Semantics.Control} {target : Value}
    (related : ControlRel type control target) (stopped : control ≠ .fallthrough)
    (evaluated : Evaluates environment initial (first.rename mapping) target final) :
    Evaluates environment initial ((LocalLoop.sequence type first next).rename mapping) target final := by
  rw [rename_sequence]
  cases related with
  | fallthrough => exact (stopped rfl).elim
  | returned _ => exact LocalLoop.sequence_returned _ evaluated
  | breaking => exact LocalLoop.sequence_transfer _ evaluated
  | continuing => exact LocalLoop.sequence_transfer _ evaluated
  | language reason => exact LocalLoop.sequence_failure _ evaluated

theorem Compound.isCompound {environment : Semantics.Environment} {statement : YulStmt}
    {initial final : YulSemantics.State} {control : Semantics.Control}
    (compound : YulSemantics.Compound environment statement initial control final) : IsCompound statement := by
  cases compound <;> trivial

/-- A builtin of the fragment is lowered either by `Effects.lowerBuiltin` or as a
pure `RustYulPrimitives` operation. -/
theorem builtin_named {name : String} (named : name ∈ YulSemantics.builtins) :
    name.startsWith Effects.reservedPrefix = false ∧ name.startsWith "usr$" = false ∧
      ((name ∈ YulSemantics.effectBuiltins ∧ Effects.supports name = true) ∨
        (name ∈ YulFragment.primitives ∧ Effects.supports name = false)) := by
  simp only [YulSemantics.builtins, YulSemantics.effectBuiltins, YulFragment.primitives, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at named
  rcases named with (rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl | rfl) <;> decide +kernel

theorem Builtin.named {name : String} {words : List Word} {frame next : RuntimeEffectsSemantics.State}
    {result : Semantics.Result Semantics.Value} (computed : YulSemantics.Builtin name words frame result next) :
    name ∈ YulSemantics.builtins := by
  cases computed <;> decide

/-- The Core code of a two-argument word primitive, over the innermost values in
source order. -/
def binaryCode (body : Core.Expr) : Core.Expr :=
  .apply (.lambda .word .word (.apply (.lambda .word .word body) (.var 1))) (.var 1)

/-- The Core code of a one-argument word primitive. -/
def unaryCode (body : Core.Expr) : Core.Expr :=
  .apply (.lambda .word .word body) (.var 0)

theorem binaryCode_evaluates {body : Core.Expr} {mapping : Renaming} {environment : Environment}
    {store : Store} {left right : Word} {result : Value} (first : mapping 0 = 0) (second : mapping 1 = 1)
    (evaluated : Evaluates (.word left :: .word right :: .word left :: .word right :: environment) store
      (body.rename mapping.lift.lift) result store) :
    Evaluates (.word left :: .word right :: environment) store ((binaryCode body).rename mapping) result store := by
  apply Evaluates.apply .lambda (.var (by show (_ :: _ :: environment)[mapping 1]? = _; rw [second]; rfl))
  apply Evaluates.apply .lambda
    (.var (by show (_ :: _ :: _ :: environment)[mapping 0 + 1]? = _; rw [first]; rfl))
  exact evaluated

theorem unaryCode_evaluates {body : Core.Expr} {mapping : Renaming} {environment : Environment}
    {store : Store} {value : Word} {result : Value} (first : mapping 0 = 0)
    (evaluated : Evaluates (.word value :: .word value :: environment) store (body.rename mapping.lift) result store) :
    Evaluates (.word value :: environment) store ((unaryCode body).rename mapping) result store := by
  apply Evaluates.apply .lambda (.var (by show (_ :: environment)[mapping 0]? = _; rw [first]; rfl))
  exact evaluated

/-- The word primitives run their actual `RustYulPrimitives` code over the
argument words and leave the frame unchanged, in every effect model. -/
theorem primitive_step {name : String} {words : List Word} {frame next : RuntimeEffectsSemantics.State}
    {result : Semantics.Result Semantics.Value} (computed : YulSemantics.Builtin name words frame result next)
    (primitive : name ∈ YulFragment.primitives) {lowered : RustYulPrimitives.Lowered}
    (compiled : RustYulPrimitives.compile name ((List.range words.length).map Core.Expr.var) = .ok lowered)
    {mapping : Renaming} {environment : Environment} {store : Store}
    (fixed : ∀ index < words.length, mapping index = index) :
    next = frame ∧ ∃ target, ResultRel lowered.type result target ∧
      Evaluates (words.map Value.word ++ environment) store
        ((LanguageResult.success lowered.expression).rename mapping) target store := by
  cases computed with
  | mload => exact absurd primitive (by decide)
  | msize => exact absurd primitive (by decide)
  | mstore => exact absurd primitive (by decide)
  | mstore8 => exact absurd primitive (by decide)
  | returned => exact absurd primitive (by decide)
  | reverted => exact absurd primitive (by decide)
  | @add _ left right =>
      have code : RustYulPrimitives.compile "add" [.var 0, .var 1] =
          .ok ⟨.word, binaryCode (.binary .wordAdd (.var 0) (.var 1))⟩ := rfl
      rw [show (List.range [left, right].length).map Core.Expr.var = [.var 0, .var 1] from rfl, code] at compiled
      cases compiled
      exact ⟨rfl, _, .value (.word _), LanguageResult.success_evaluates
        (binaryCode_evaluates (fixed 0 (by simp)) (fixed 1 (by simp)) (.binary (.var rfl) (.var rfl) rfl))⟩
  | @sub _ left right =>
      have code : RustYulPrimitives.compile "sub" [.var 0, .var 1] =
          .ok ⟨.word, binaryCode (.binary .wordSub (.var 0) (.var 1))⟩ := rfl
      rw [show (List.range [left, right].length).map Core.Expr.var = [.var 0, .var 1] from rfl, code] at compiled
      cases compiled
      exact ⟨rfl, _, .value (.word _), LanguageResult.success_evaluates
        (binaryCode_evaluates (fixed 0 (by simp)) (fixed 1 (by simp)) (.binary (.var rfl) (.var rfl) rfl))⟩
  | @lt _ left right =>
      have code : RustYulPrimitives.compile "lt" [.var 0, .var 1] =
          .ok ⟨.word, binaryCode (.ifE (.binary .wordGt (.var 1) (.var 0)) (.word (Word.ofNatModulo 1))
            (.word Word.zero))⟩ := rfl
      rw [show (List.range [left, right].length).map Core.Expr.var = [.var 0, .var 1] from rfl, code] at compiled
      cases compiled
      refine ⟨rfl, _, .value (.word _), LanguageResult.success_evaluates
        (binaryCode_evaluates (fixed 0 (by simp)) (fixed 1 (by simp)) ?_)⟩
      by_cases below : left < right
      · rw [if_pos below]
        exact .ifTrue (.binary (.var rfl) (.var rfl) (by simp [BinaryOp.apply, below])) .word
      · rw [if_neg below]
        exact .ifFalse (.binary (.var rfl) (.var rfl) (by simp [BinaryOp.apply, below])) .word
  | @gt _ left right =>
      have code : RustYulPrimitives.compile "gt" [.var 0, .var 1] =
          .ok ⟨.word, binaryCode (.ifE (.binary .wordGt (.var 0) (.var 1)) (.word (Word.ofNatModulo 1))
            (.word Word.zero))⟩ := rfl
      rw [show (List.range [left, right].length).map Core.Expr.var = [.var 0, .var 1] from rfl, code] at compiled
      cases compiled
      refine ⟨rfl, _, .value (.word _), LanguageResult.success_evaluates
        (binaryCode_evaluates (fixed 0 (by simp)) (fixed 1 (by simp)) ?_)⟩
      by_cases above : left > right
      · rw [if_pos above]
        exact .ifTrue (.binary (.var rfl) (.var rfl) (by simp [BinaryOp.apply, above])) .word
      · rw [if_neg above]
        exact .ifFalse (.binary (.var rfl) (.var rfl) (by simp [BinaryOp.apply, above])) .word
  | @eq _ left right =>
      have code : RustYulPrimitives.compile "eq" [.var 0, .var 1] =
          .ok ⟨.word, binaryCode (.ifE (.binary .wordEq (.var 0) (.var 1)) (.word (Word.ofNatModulo 1))
            (.word Word.zero))⟩ := rfl
      rw [show (List.range [left, right].length).map Core.Expr.var = [.var 0, .var 1] from rfl, code] at compiled
      cases compiled
      refine ⟨rfl, _, .value (.word _), LanguageResult.success_evaluates
        (binaryCode_evaluates (fixed 0 (by simp)) (fixed 1 (by simp)) ?_)⟩
      by_cases same : left = right
      · rw [if_pos same]
        exact .ifTrue (.binary (.var rfl) (.var rfl) (by simp [BinaryOp.apply, same])) .word
      · rw [if_neg same]
        exact .ifFalse (.binary (.var rfl) (.var rfl) (by simp [BinaryOp.apply, same])) .word
  | @iszero _ value =>
      have code : RustYulPrimitives.compile "iszero" [.var 0] =
          .ok ⟨.word, unaryCode (.ifE (.binary .wordEq (.var 0) (.word Word.zero)) (.word (Word.ofNatModulo 1))
            (.word Word.zero))⟩ := rfl
      rw [show (List.range [value].length).map Core.Expr.var = [.var 0] from rfl, code] at compiled
      cases compiled
      refine ⟨rfl, _, .value (.word _), LanguageResult.success_evaluates (unaryCode_evaluates (fixed 0 (by simp)) ?_)⟩
      by_cases zero : value = Word.zero
      · rw [if_pos zero]
        exact .ifTrue (.binary (.var rfl) .word (by simp [BinaryOp.apply, zero])) .word
      · rw [if_neg zero]
        exact .ifFalse (.binary (.var rfl) .word (by simp [BinaryOp.apply, zero])) .word

/-- The builtin obligation of an effect model: the actual code of an effect
builtin over its argument words, bound as the innermost Core values, simulates
`YulSemantics.Builtin`. -/
def BuiltinStep (model : StateModel RuntimeCallEffectsSemantics.State) (slots : List EffectSlot) : Prop :=
  ∀ {name : String} {words : List Word} {state : YulSemantics.State} {result : Semantics.Result Semantics.Value}
    {next : RuntimeEffectsSemantics.State} {scope : Scope} {effect : Lowered} {mapping : Renaming}
    {environment : Environment} {world : World} {store : Store},
    name ∈ YulSemantics.effectBuiltins →
    YulSemantics.Builtin name words (YulSemantics.frame state) result next →
    Effects.lowerBuiltin scope name ((List.range words.length).map Core.Expr.var) = .ok effect →
    EffectEnvironmentRel slots scope mapping (words.map Value.word ++ environment) →
    (∀ index < words.length, mapping index = index) →
    StateRel model world state store →
    ∃ target finalStore, ResultRel effect.type result target ∧
      Evaluates (words.map Value.word ++ environment) store (effect.expression.rename mapping) target finalStore ∧
      StateRel model world (YulSemantics.withFrame state next) finalStore ∧ ClosuresPreserved store finalStore

section Simulation
variable {model : StateModel RuntimeCallEffectsSemantics.State} {slots : List EffectSlot}

/-- An accepted expression lowering simulates the source evaluation. -/
def ExpressionGoal (model : StateModel RuntimeCallEffectsSemantics.State) (slots : List EffectSlot)
    (sourceEnvironment : Semantics.Environment) (expression : YulExpr) (initial : YulSemantics.State)
    (result : Semantics.Result Semantics.Value) (final : YulSemantics.State) : Prop :=
  ∀ {fuel : Nat} {context : YulLowering.Context} {lowered : Lowered}, context.functions = [] →
    YulLowering.lowerExpr fuel context expression = .ok lowered →
    ∀ {world : World} {mapping : Renaming} {environment : Environment} {store : Store},
      EnvironmentRel world sourceEnvironment context.scope mapping environment →
      EffectEnvironmentRel slots context.scope mapping environment →
      StateRel model world initial store →
      ∃ target finalStore, ResultRel lowered.type result target ∧
        Evaluates environment store (lowered.expression.rename mapping) target finalStore ∧
        StateRel model world final finalStore ∧ ClosuresPreserved store finalStore

/-- Argument binds under the words `bound` before them: their words reach the
body, or their first fault stops it. -/
def ArgumentsGoal (model : StateModel RuntimeCallEffectsSemantics.State) (slots : List EffectSlot)
    (sourceEnvironment : Semantics.Environment) (expressions : List YulExpr) (initial : YulSemantics.State) :
    Semantics.Result (List Word) → YulSemantics.State → Prop
  | .value words, final =>
      ∀ {fuel : Nat} {context : YulLowering.Context} {loweredArguments : List Lowered}, context.functions = [] →
        Lowers fuel context expressions loweredArguments →
        ∀ {world : World} {mapping : Renaming} {environment : Environment} {store : Store},
          EnvironmentRel world sourceEnvironment context.scope mapping environment →
          EffectEnvironmentRel slots context.scope mapping environment →
          StateRel model world initial store → ∀ (bound : Environment) (type : Core.Ty) (body : Core.Expr),
          ∃ middleStore, words.length = loweredArguments.length ∧ StateRel model world final middleStore ∧
            ClosuresPreserved store middleStore ∧
            ∀ {result : Value} {finalStore : Store},
              Evaluates ((words.map Value.word).reverse ++ bound ++ environment) middleStore
                (body.rename (liftN mapping (bound.length + words.length))) result finalStore →
              Evaluates (bound ++ environment) store
                ((YulLowering.bindArguments type body bound.length loweredArguments).rename (liftN mapping bound.length))
                result finalStore
  | .fault reason, final =>
      ∀ {fuel : Nat} {context : YulLowering.Context} {loweredArguments : List Lowered}, context.functions = [] →
        Lowers fuel context expressions loweredArguments →
        ∀ {world : World} {mapping : Renaming} {environment : Environment} {store : Store},
          EnvironmentRel world sourceEnvironment context.scope mapping environment →
          EffectEnvironmentRel slots context.scope mapping environment →
          StateRel model world initial store → ∀ (bound : Environment) (type : Core.Ty) (body : Core.Expr),
          ∃ reasonWord finalStore, reason = .language reasonWord ∧ StateRel model world final finalStore ∧
            ClosuresPreserved store finalStore ∧
            Evaluates (bound ++ environment) store
              ((YulLowering.bindArguments type body bound.length loweredArguments).rename (liftN mapping bound.length))
              (.inLeft type (.word reasonWord)) finalStore

theorem expression_simulation (step : BuiltinStep model slots) {sourceEnvironment : Semantics.Environment}
    {expression : YulExpr} {initial final : YulSemantics.State} {result : Semantics.Result Semantics.Value}
    (evaluated : YulSemantics.Eval sourceEnvironment expression initial result final) :
    ExpressionGoal model slots sourceEnvironment expression initial result final := by
  refine YulSemantics.Eval.rec
    (motive_1 := fun expression initial result final _ =>
      ExpressionGoal model slots sourceEnvironment expression initial result final)
    (motive_2 := fun expressions initial result final _ =>
      ArgumentsGoal model slots sourceEnvironment expressions initial result final)
    ?literal ?ident ?call ?callFault ?nil ?cons ?tailFault ?headFault evaluated
  case literal =>
    intro literal span state word evaluated fuel context lowered _ compiled world mapping environment store _ _
      stateRelated
    cases fuel with
    | zero => cases compiled
    | succ fuel =>
        obtain ⟨loweredWord, parsed, rfl⟩ := expr_literal compiled
        cases literal_word parsed evaluated
        exact ⟨_, store, .value (.word _), LanguageResult.success_evaluates .word, stateRelated,
          ClosuresPreserved.refl store⟩
  case ident =>
    intro name span state location word found read fuel context lowered _ compiled world mapping environment store
      environmentRelated _ stateRelated
    cases fuel with
    | zero => cases compiled
    | succ fuel =>
        obtain ⟨binding, index, looked, wordType, rfl⟩ := expr_ident compiled
        obtain ⟨cellLocation, targetValue, reference, targetFound, cellRead, valueRelated⟩ :=
          environmentRelated.read stateRelated.toHeapRel found looked read
        rw [wordType] at targetFound valueRelated
        cases valueRelated
        simp only [reference, ↓reduceIte]
        rw [wordType]
        exact ⟨_, store, .value (.word word), OptionalCell.read_success _ (.var targetFound) cellRead, stateRelated,
          ClosuresPreserved.refl store⟩
  case call =>
    intro name arguments span initial middle words result next _ computed argumentsSimulated
      fuel context lowered noFunctions compiled world mapping environment store environmentRelated runtime stateRelated
    cases fuel with
    | zero => cases compiled
    | succ fuel =>
        obtain ⟨_, notUser, kind⟩ := builtin_named (Builtin.named computed)
        rcases kind with ⟨effectNamed, builtin⟩ | ⟨primitiveNamed, notEffect⟩
        · obtain ⟨loweredArguments, effect, argumentsCompiled, typed, effectCompiled, rfl⟩ :=
            expr_call compiled noFunctions notUser builtin
          obtain ⟨middleStore, lengthEq, middleState, firstFrame, continued⟩ :=
            argumentsSimulated noFunctions (lowers_of_mapM argumentsCompiled typed).reverse environmentRelated runtime
              stateRelated [] effect.type effect.expression
          have count : words.reverse.length = loweredArguments.length := by simpa using lengthEq
          obtain ⟨target, finalStore, related, effectEvaluated, finalState, lastFrame⟩ :=
            step effectNamed computed (by rw [count]; exact effectCompiled)
              (temporaries_related runtime loweredArguments (words.reverse.map Value.word) (by simpa using count))
              (fun index below => liftN_below mapping (count ▸ below)) middleState
          refine ⟨target, finalStore, related, continued ?_, finalState, firstFrame.trans lastFrame⟩
          have sameLength : ([] : Environment).length + words.length = loweredArguments.length := by
            simpa using count
          rw [sameLength, List.append_nil, ← List.map_reverse]
          exact effectEvaluated
        · obtain ⟨loweredArguments, primitive, argumentsCompiled, typed, primitiveCompiled, rfl⟩ :=
            expr_primitive compiled noFunctions notUser notEffect
          obtain ⟨middleStore, lengthEq, middleState, firstFrame, continued⟩ :=
            argumentsSimulated noFunctions (lowers_of_mapM argumentsCompiled typed).reverse environmentRelated runtime
              stateRelated [] primitive.type (LanguageResult.success primitive.expression)
          have count : words.reverse.length = loweredArguments.length := by simpa using lengthEq
          obtain ⟨rfl, target, related, primitiveEvaluated⟩ :=
            primitive_step (environment := environment) (store := middleStore) computed primitiveNamed
              (by rw [count]; exact primitiveCompiled) (fun index below => liftN_below mapping (count ▸ below))
          refine ⟨target, middleStore, related, continued ?_, middleState, firstFrame⟩
          have sameLength : ([] : Environment).length + words.length = loweredArguments.length := by
            simpa using count
          rw [sameLength, List.append_nil, ← List.map_reverse]
          exact primitiveEvaluated
  case callFault =>
    intro name arguments span initial final reason named _ argumentsSimulated
      fuel context lowered noFunctions compiled world mapping environment store environmentRelated runtime stateRelated
    cases fuel with
    | zero => cases compiled
    | succ fuel =>
        obtain ⟨_, notUser, kind⟩ := builtin_named named
        rcases kind with ⟨_, builtin⟩ | ⟨_, notEffect⟩
        · obtain ⟨loweredArguments, effect, argumentsCompiled, typed, _, rfl⟩ :=
            expr_call compiled noFunctions notUser builtin
          obtain ⟨reasonWord, finalStore, rfl, finalState, frame, faulted⟩ :=
            argumentsSimulated noFunctions (lowers_of_mapM argumentsCompiled typed).reverse environmentRelated runtime
              stateRelated [] effect.type effect.expression
          exact ⟨_, finalStore, .language reasonWord, faulted, finalState, frame⟩
        · obtain ⟨loweredArguments, primitive, argumentsCompiled, typed, _, rfl⟩ :=
            expr_primitive compiled noFunctions notUser notEffect
          obtain ⟨reasonWord, finalStore, rfl, finalState, frame, faulted⟩ :=
            argumentsSimulated noFunctions (lowers_of_mapM argumentsCompiled typed).reverse environmentRelated runtime
              stateRelated [] primitive.type (LanguageResult.success primitive.expression)
          exact ⟨_, finalStore, .language reasonWord, faulted, finalState, frame⟩
  case nil =>
    intro state fuel context loweredArguments _ lowers world mapping environment store _ _ stateRelated bound type body
    cases lowers
    exact ⟨store, rfl, stateRelated, ClosuresPreserved.refl store, fun evaluated => evaluated⟩
  case cons =>
    intro argument rest initial middle final word words _ _ headSimulated tailSimulated
      fuel context loweredArguments noFunctions lowers world mapping environment store environmentRelated runtime
      stateRelated bound type body
    cases lowers with
    | cons headCompiled headTyped tailLowers =>
    obtain ⟨headTarget, headStore, headRelated, headEvaluated, headState, headFrame⟩ :=
      headSimulated noFunctions headCompiled (environmentRelated.prepend bound) (runtime.prepend bound) stateRelated
    rw [headTyped] at headRelated
    obtain rfl := word_result headRelated
    obtain ⟨middleStore, lengthEq, middleState, tailFrame, continued⟩ :=
      tailSimulated noFunctions tailLowers environmentRelated runtime headState (.word word :: bound) type body
    refine ⟨middleStore, by simp [lengthEq], middleState, headFrame.trans tailFrame, ?_⟩
    intro result finalStore evaluated
    have reshaped : Evaluates ((words.map Value.word).reverse ++ (Value.word word :: bound) ++ environment) middleStore
        (body.rename (liftN mapping ((Value.word word :: bound).length + words.length))) result finalStore := by
      have indexEq : (Value.word word :: bound).length + words.length = bound.length + (word :: words).length := by
        simp only [List.length_cons]
        omega
      rw [indexEq]
      simpa only [List.map_cons, List.reverse_cons, List.append_assoc, List.singleton_append] using evaluated
    exact LanguageResult.bind_success type (by rw [shifted_rename]; exact headEvaluated) (continued reshaped)
  case tailFault =>
    intro argument rest initial middle final word reason _ _ headSimulated tailSimulated
      fuel context loweredArguments noFunctions lowers world mapping environment store environmentRelated runtime
      stateRelated bound type body
    cases lowers with
    | cons headCompiled headTyped tailLowers =>
    obtain ⟨headTarget, headStore, headRelated, headEvaluated, headState, headFrame⟩ :=
      headSimulated noFunctions headCompiled (environmentRelated.prepend bound) (runtime.prepend bound) stateRelated
    rw [headTyped] at headRelated
    obtain rfl := word_result headRelated
    obtain ⟨reasonWord, finalStore, rfl, finalState, tailFrame, tailEvaluated⟩ :=
      tailSimulated noFunctions tailLowers environmentRelated runtime headState (.word word :: bound) type body
    exact ⟨reasonWord, finalStore, rfl, finalState, headFrame.trans tailFrame,
      LanguageResult.bind_success type (by rw [shifted_rename]; exact headEvaluated) tailEvaluated⟩
  case headFault =>
    intro argument rest initial final reason _ headSimulated
      fuel context loweredArguments noFunctions lowers world mapping environment store environmentRelated runtime
      stateRelated bound type body
    cases lowers with
    | cons headCompiled headTyped tailLowers =>
    obtain ⟨headTarget, finalStore, headRelated, headEvaluated, finalState, frame⟩ :=
      headSimulated noFunctions headCompiled (environmentRelated.prepend bound) (runtime.prepend bound) stateRelated
    cases headRelated with
    | language reasonWord =>
        exact ⟨reasonWord, finalStore, rfl, finalState, frame,
          LanguageResult.bind_failure type (by rw [shifted_rename]; exact headEvaluated)⟩

/-- An accepted statement list simulates the source run. -/
def RunGoal (model : StateModel RuntimeCallEffectsSemantics.State) (slots : List EffectSlot)
    (supported : String → Prop) (resultType : Core.Ty) (sourceEnvironment : Semantics.Environment)
    (body : List YulStmt) (initial : YulSemantics.State) (control : Semantics.Control)
    (final : YulSemantics.State) : Prop :=
  ∀ {fuel : Nat} {context : YulLowering.Context} {inLoop : Bool} {code : Core.Expr}, context.functions = [] →
    (∀ statement ∈ body, YulFragment.StatementEligible supported statement) →
    YulLowering.lowerSequence fuel context resultType inLoop body (finish resultType) = .ok code →
    ∀ {world : World} {mapping : Renaming} {environment : Environment} {store : Store},
      EnvironmentRel world sourceEnvironment context.scope mapping environment →
      EffectEnvironmentRel slots context.scope mapping environment →
      StateRel model world initial store →
      ∃ extension target finalStore, ControlRel resultType control target ∧
        Evaluates environment store (code.rename mapping) target finalStore ∧
        StateRel model (world ++ extension) final finalStore ∧ ClosuresPreserved store finalStore

/-- The code of an accepted statement with nested bodies simulates its source
run. -/
def CompoundGoal (model : StateModel RuntimeCallEffectsSemantics.State) (slots : List EffectSlot)
    (supported : String → Prop) (resultType : Core.Ty) (sourceEnvironment : Semantics.Environment)
    (statement : YulStmt) (initial : YulSemantics.State) (control : Semantics.Control)
    (final : YulSemantics.State) : Prop :=
  ∀ {fuel : Nat} {context : YulLowering.Context} {inLoop : Bool} {head : Core.Expr}, context.functions = [] →
    YulFragment.StatementEligible supported statement →
    CompoundLowering fuel context resultType inLoop statement head →
    ∀ {world : World} {mapping : Renaming} {environment : Environment} {store : Store},
      EnvironmentRel world sourceEnvironment context.scope mapping environment →
      EffectEnvironmentRel slots context.scope mapping environment →
      StateRel model world initial store →
      ∃ extension target finalStore, ControlRel resultType control target ∧
        Evaluates environment store (head.rename mapping) target finalStore ∧
        StateRel model (world ++ extension) final finalStore ∧ ClosuresPreserved store finalStore

theorem sequence_simulation (step : BuiltinStep model slots) {supported : String → Prop} {resultType : Core.Ty}
    {sourceEnvironment : Semantics.Environment} {body : List YulStmt} {initial final : YulSemantics.State}
    {control : Semantics.Control} (executed : YulSemantics.Run sourceEnvironment body initial control final) :
    RunGoal model slots supported resultType sourceEnvironment body initial control final := by
  refine YulSemantics.Run.rec
    (motive_1 := fun sourceEnvironment body initial control final _ =>
      RunGoal model slots supported resultType sourceEnvironment body initial control final)
    (motive_2 := fun sourceEnvironment statement initial control final _ =>
      CompoundGoal model slots supported resultType sourceEnvironment statement initial control final)
    ?nil ?letValue ?letZero ?letFault ?assign ?assignFault ?expression ?expressionFault ?compound ?compoundStop
    ?block ?ifTrue ?ifFalse ?ifFault ?switchCase ?switchDefault ?switchFault executed
  case nil =>
    intro sourceEnvironment state fuel context inLoop code _ _ compiled world mapping environment store _ _
      stateRelated
    obtain rfl := sequence_nil compiled
    exact ⟨[], _, store, .fallthrough, LocalLoop.fallthrough_evaluates _ _ _,
      by simpa only [List.append_nil] using stateRelated, ClosuresPreserved.refl store⟩
  case letValue =>
    intro sourceEnvironment name value span rest initial middle final control word evaluated _ tailSimulated
      fuel context inLoop code noFunctions eligible compiled world mapping environment store environmentRelated runtime
      stateRelated
    obtain ⟨previous, lowered, continuation, rfl, allowed, valueCompiled, wordType, continuationCompiled, rfl⟩ :=
      sequence_letValue compiled
    obtain ⟨valueTarget, middleStore, valueRelated, valueEvaluated, middleState, firstFrame⟩ :=
      expression_simulation step evaluated noFunctions valueCompiled environmentRelated runtime stateRelated
    rw [wordType] at valueRelated
    obtain rfl := word_result valueRelated
    have entry : (world ++ [(Core.Ty.word, middleStore.length)])[middle.heap.length]? =
        some (Core.Ty.word, middleStore.length) := by
      rw [← middleState.length_eq, List.getElem?_concat_length]
    obtain ⟨extension, target, finalStore, related, tailEvaluated, finalState, lastFrame⟩ :=
      tailSimulated (context := (context.temporary .word).addLocal name.name)
        (by simp [YulLowering.Context.addLocal, YulLowering.Context.temporary, YulLowering.Context.push, noFunctions])
        (fun other member => eligible other (List.mem_cons.mpr (.inr member)))
        continuationCompiled
        (((environmentRelated.extendWorld [(.word, middleStore.length)]).temporary .word (.word word)).addLocal
          name.name .word middle.heap.length middleStore.length entry)
        ((runtime.temporary .word (.word word)).addLocal name.name .word
          (.cellRef (OptionalCell.cellType .word) middleStore.length) allowed)
        (middleState.allocate (.word word))
    refine ⟨[(.word, middleStore.length)] ++ extension, target, finalStore, related, ?_,
      by simpa only [List.append_assoc] using finalState,
      firstFrame.trans (ClosuresPreserved.trans (ClosuresPreserved.append _ _) lastFrame)⟩
    exact LanguageResult.bind_success _ valueEvaluated
      (Evaluates.letE (OptionalCell.allocateInitialized_evaluates (.var rfl)) tailEvaluated)
  case letZero =>
    intro sourceEnvironment name span rest initial final control _ tailSimulated
      fuel context inLoop code noFunctions eligible compiled world mapping environment store environmentRelated runtime
      stateRelated
    obtain ⟨previous, continuation, rfl, allowed, continuationCompiled, rfl⟩ := sequence_letZero compiled
    have entry : (world ++ [(Core.Ty.word, store.length)])[initial.heap.length]? =
        some (Core.Ty.word, store.length) := by
      rw [← stateRelated.length_eq, List.getElem?_concat_length]
    obtain ⟨extension, target, finalStore, related, tailEvaluated, finalState, lastFrame⟩ :=
      tailSimulated (context := context.addLocal name.name)
        (by simp [YulLowering.Context.addLocal, YulLowering.Context.push, noFunctions])
        (fun other member => eligible other (List.mem_cons.mpr (.inr member)))
        continuationCompiled
        ((environmentRelated.extendWorld [(.word, store.length)]).addLocal name.name .word initial.heap.length
          store.length entry)
        (runtime.addLocal name.name .word (.cellRef (OptionalCell.cellType .word) store.length) allowed)
        (stateRelated.allocate (.word Word.zero))
    refine ⟨[(.word, store.length)] ++ extension, target, finalStore, related, ?_,
      by simpa only [List.append_assoc] using finalState, ClosuresPreserved.trans (ClosuresPreserved.append _ _) lastFrame⟩
    exact Evaluates.letE (OptionalCell.allocateInitialized_evaluates .word) tailEvaluated
  case letFault =>
    intro sourceEnvironment name value span rest initial final reason evaluated
      fuel context inLoop code noFunctions _ compiled world mapping environment store environmentRelated runtime
      stateRelated
    obtain ⟨previous, lowered, continuation, rfl, _, valueCompiled, _, _, rfl⟩ := sequence_letValue compiled
    obtain ⟨valueTarget, finalStore, valueRelated, valueEvaluated, finalState, frame⟩ :=
      expression_simulation step evaluated noFunctions valueCompiled environmentRelated runtime stateRelated
    cases valueRelated with
    | language reasonWord =>
        exact ⟨[], _, finalStore, .language reasonWord, LanguageResult.bind_failure _ valueEvaluated,
          by simpa only [List.append_nil] using finalState, frame⟩
  case assign =>
    intro sourceEnvironment name value span rest initial middle final control word location evaluated found _
      tailSimulated fuel context inLoop code noFunctions eligible compiled world mapping environment store
      environmentRelated runtime stateRelated
    obtain ⟨previous, lowered, next, binding, index, rfl, valueCompiled, wordType, nextCompiled, looked, reference,
      bindingWord, rfl⟩ := sequence_assign compiled
    obtain ⟨valueTarget, middleStore, valueRelated, valueEvaluated, middleState, firstFrame⟩ :=
      expression_simulation step evaluated noFunctions valueCompiled environmentRelated runtime stateRelated
    rw [wordType] at valueRelated
    obtain rfl := word_result valueRelated
    obtain ⟨cellLocation, entry, _, targetFound⟩ := environmentRelated name.name location binding index found looked
    rw [bindingWord] at entry targetFound
    obtain ⟨_, oldValue, _, oldRead, _⟩ := middleState.cell location .word cellLocation entry
    have written : middleStore.write? cellLocation (.inRight .unit (.word word)) =
        some (middleStore.set cellLocation (.inRight .unit (.word word))) :=
      Store.write?_eq_some_iff.mpr ⟨middleState.location_bound entry, rfl⟩
    have nextEnvironment : EnvironmentRel world sourceEnvironment context.scope (fun index => 2 + mapping index)
        (.unit :: .word word :: environment) := environmentRelated.prepend [.unit, .word word]
    have nextRuntime : EffectEnvironmentRel slots context.scope (fun index => 2 + mapping index)
        (.unit :: .word word :: environment) := runtime.prepend [.unit, .word word]
    obtain ⟨extension, target, finalStore, related, tailEvaluated, finalState, lastFrame⟩ :=
      tailSimulated noFunctions (fun other member => eligible other (List.mem_cons.mpr (.inr member))) nextCompiled
        nextEnvironment nextRuntime (middleState.write entry (.word word) written)
    refine ⟨extension, target, finalStore, related, ?_, finalState,
      firstFrame.trans (ClosuresPreserved.trans (ClosuresPreserved.write middleState.toHeapRel entry written) lastFrame)⟩
    have continued : Evaluates (.unit :: .word word :: environment)
        (middleStore.set cellLocation (.inRight .unit (.word word)))
        (((next.weakenAt 0).weakenAt 0).rename mapping.lift.lift) target finalStore := by
      rw [weakened_twice]
      exact tailEvaluated
    exact LanguageResult.bind_success _ valueEvaluated
      (Evaluates.letE (Evaluates.storeCell (.var targetFound) oldRead (.inRight (.var rfl)) written) continued)
  case assignFault =>
    intro sourceEnvironment name value span rest initial final reason evaluated
      fuel context inLoop code noFunctions _ compiled world mapping environment store environmentRelated runtime
      stateRelated
    obtain ⟨previous, lowered, next, binding, index, rfl, valueCompiled, _, _, _, _, _, rfl⟩ :=
      sequence_assign compiled
    obtain ⟨valueTarget, finalStore, valueRelated, valueEvaluated, finalState, frame⟩ :=
      expression_simulation step evaluated noFunctions valueCompiled environmentRelated runtime stateRelated
    cases valueRelated with
    | language reasonWord =>
        exact ⟨[], _, finalStore, .language reasonWord, LanguageResult.bind_failure _ valueEvaluated,
          by simpa only [List.append_nil] using finalState, frame⟩
  case expression =>
    intro sourceEnvironment value span rest initial middle final control evaluated _ tailSimulated
      fuel context inLoop code noFunctions eligible compiled world mapping environment store environmentRelated runtime
      stateRelated
    obtain ⟨previous, lowered, next, rfl, valueCompiled, unitType, nextCompiled, rfl⟩ :=
      sequence_expression compiled
    obtain ⟨valueTarget, middleStore, valueRelated, valueEvaluated, middleState, firstFrame⟩ :=
      expression_simulation step evaluated noFunctions valueCompiled environmentRelated runtime stateRelated
    rw [unitType] at valueRelated
    obtain rfl := unit_result valueRelated
    have nextEnvironment : EnvironmentRel world sourceEnvironment context.scope (fun index => 1 + mapping index)
        (.unit :: environment) := environmentRelated.prepend [.unit]
    have nextRuntime : EffectEnvironmentRel slots context.scope (fun index => 1 + mapping index)
        (.unit :: environment) := runtime.prepend [.unit]
    obtain ⟨extension, target, finalStore, related, tailEvaluated, finalState, lastFrame⟩ :=
      tailSimulated noFunctions (fun other member => eligible other (List.mem_cons.mpr (.inr member))) nextCompiled
        nextEnvironment nextRuntime middleState
    refine ⟨extension, target, finalStore, related, ?_, finalState, firstFrame.trans lastFrame⟩
    have continued : Evaluates (.unit :: environment) middleStore ((next.weakenAt 0).rename mapping.lift) target
        finalStore := by
      rw [weakened_once]
      exact tailEvaluated
    exact LanguageResult.bind_success _ valueEvaluated continued
  case expressionFault =>
    intro sourceEnvironment value span rest initial final reason evaluated
      fuel context inLoop code noFunctions _ compiled world mapping environment store environmentRelated runtime
      stateRelated
    obtain ⟨previous, lowered, next, rfl, valueCompiled, _, _, rfl⟩ := sequence_expression compiled
    obtain ⟨valueTarget, finalStore, valueRelated, valueEvaluated, finalState, frame⟩ :=
      expression_simulation step evaluated noFunctions valueCompiled environmentRelated runtime stateRelated
    cases valueRelated with
    | language reasonWord =>
        exact ⟨[], _, finalStore, .language reasonWord, LanguageResult.bind_failure _ valueEvaluated,
          by simpa only [List.append_nil] using finalState, frame⟩
  case compound =>
    intro sourceEnvironment statement rest initial middle final control headDerivation _ headSimulated
      tailSimulated fuel context inLoop code noFunctions eligible compiled world mapping environment store
      environmentRelated runtime stateRelated
    obtain ⟨previous, head, next, rfl, headLowered, nextCompiled, rfl⟩ :=
      sequence_compound (Compound.isCompound headDerivation) compiled
    obtain ⟨firstExtension, firstTarget, middleStore, firstRelated, firstEvaluated, middleState, firstFrame⟩ :=
      headSimulated noFunctions (eligible _ (List.mem_cons.mpr (.inl rfl))) headLowered environmentRelated runtime
        stateRelated
    cases firstRelated
    obtain ⟨extension, target, finalStore, related, nextEvaluated, finalState, lastFrame⟩ :=
      tailSimulated noFunctions (fun other member => eligible other (List.mem_cons.mpr (.inr member))) nextCompiled
        ((environmentRelated.extendWorld firstExtension).prepend
          [.unit, .inLeft resultType .unit, .inLeft LocalLoop.transferType (.inLeft resultType .unit)])
        (runtime.prepend [.unit, .inLeft resultType .unit, .inLeft LocalLoop.transferType (.inLeft resultType .unit)])
        middleState
    exact ⟨firstExtension ++ extension, target, finalStore, related, sequence_next firstEvaluated nextEvaluated,
      by simpa only [List.append_assoc] using finalState, firstFrame.trans lastFrame⟩
  case compoundStop =>
    intro sourceEnvironment statement rest initial final control headDerivation stopped headSimulated
      fuel context inLoop code noFunctions eligible compiled world mapping environment store environmentRelated runtime
      stateRelated
    obtain ⟨previous, head, next, rfl, headLowered, _, rfl⟩ :=
      sequence_compound (Compound.isCompound headDerivation) compiled
    obtain ⟨extension, target, finalStore, related, evaluated, finalState, frame⟩ :=
      headSimulated noFunctions (eligible _ (List.mem_cons.mpr (.inl rfl))) headLowered environmentRelated runtime
        stateRelated
    exact ⟨extension, target, finalStore, related, sequence_stopped related stopped evaluated, finalState, frame⟩
  case block =>
    intro sourceEnvironment body span initial final control _ innerSimulated
      fuel context inLoop head noFunctions eligible lowered world mapping environment store environmentRelated runtime
      stateRelated
    cases eligible with
    | block bodyEligible =>
    obtain ⟨_, sequenced⟩ := block_sequence bodyEligible lowered
    exact innerSimulated noFunctions bodyEligible sequenced environmentRelated runtime stateRelated
  case ifTrue =>
    intro sourceEnvironment condition body span initial middle final control word evaluated nonzero _
      branchSimulated fuel context inLoop head noFunctions eligible lowered world mapping environment store
      environmentRelated runtime stateRelated
    cases eligible with
    | ifThen _ bodyEligible =>
    obtain ⟨loweredCondition, tested, branchCode, conditionCompiled, testedCompiled, branchCompiled, rfl⟩ := lowered
    obtain ⟨wordType, rfl⟩ := condition_components testedCompiled
    obtain ⟨conditionTarget, middleStore, conditionRelated, conditionEvaluated, middleState, firstFrame⟩ :=
      expression_simulation step evaluated noFunctions conditionCompiled environmentRelated runtime stateRelated
    rw [wordType] at conditionRelated
    obtain rfl := word_result conditionRelated
    obtain ⟨_, sequenced⟩ := block_sequence bodyEligible branchCompiled
    obtain ⟨extension, target, finalStore, related, branchEvaluated, finalState, lastFrame⟩ :=
      branchSimulated noFunctions bodyEligible sequenced (environmentRelated.prepend [.bool true])
        (runtime.prepend [.bool true]) middleState
    refine ⟨extension, target, finalStore, related, ?_, finalState, firstFrame.trans lastFrame⟩
    have flag : (!(word == Word.zero)) = true := by simpa using nonzero
    have tested := condition_evaluates (mapping := mapping) conditionEvaluated
    rw [flag] at tested
    rw [LocalLoop.conditional_rename]
    exact LocalControl.choose_true _ tested (by rw [renamed_weakened]; exact branchEvaluated)
  case ifFalse =>
    intro sourceEnvironment condition body span initial final evaluated
      fuel context inLoop head noFunctions _ lowered world mapping environment store environmentRelated runtime
      stateRelated
    obtain ⟨loweredCondition, tested, branchCode, conditionCompiled, testedCompiled, _, rfl⟩ := lowered
    obtain ⟨wordType, rfl⟩ := condition_components testedCompiled
    obtain ⟨conditionTarget, finalStore, conditionRelated, conditionEvaluated, finalState, frame⟩ :=
      expression_simulation step evaluated noFunctions conditionCompiled environmentRelated runtime stateRelated
    rw [wordType] at conditionRelated
    obtain rfl := word_result conditionRelated
    refine ⟨[], _, finalStore, .fallthrough, ?_, by simpa only [List.append_nil] using finalState, frame⟩
    have flag : (!(Word.zero == Word.zero)) = false := by decide
    have tested := condition_evaluates (mapping := mapping) conditionEvaluated
    rw [flag] at tested
    rw [LocalLoop.conditional_rename]
    exact LocalControl.choose_false _ tested (by
      simpa only [LocalLoop.weaken_zero, LocalLoop.fallthrough_rename] using
        LocalLoop.fallthrough_evaluates resultType (.bool false :: environment) finalStore)
  case ifFault =>
    intro sourceEnvironment condition body span initial final reason evaluated
      fuel context inLoop head noFunctions _ lowered world mapping environment store environmentRelated runtime
      stateRelated
    obtain ⟨loweredCondition, tested, branchCode, conditionCompiled, testedCompiled, _, rfl⟩ := lowered
    obtain ⟨_, rfl⟩ := condition_components testedCompiled
    obtain ⟨conditionTarget, finalStore, conditionRelated, conditionEvaluated, finalState, frame⟩ :=
      expression_simulation step evaluated noFunctions conditionCompiled environmentRelated runtime stateRelated
    cases conditionRelated with
    | language reasonWord =>
        refine ⟨[], _, finalStore, .language reasonWord, ?_, by simpa only [List.append_nil] using finalState, frame⟩
        rw [LocalLoop.conditional_rename]
        exact LocalControl.choose_failure _ (LanguageResult.bind_failure .bool conditionEvaluated)
  case switchCase =>
    intro sourceEnvironment value cases defaultBody span initial middle final control word body evaluated selected _
      branchSimulated fuel context inLoop head noFunctions eligible lowered world mapping environment store
      environmentRelated runtime stateRelated
    cases eligible with
    | switch _ literals arms _ =>
    obtain ⟨loweredValue, branches, defaultCode, valueCompiled, wordType, armsLowered, _, rfl⟩ := lowered
    obtain ⟨valueTarget, middleStore, valueRelated, valueEvaluated, middleState, firstFrame⟩ :=
      expression_simulation step evaluated noFunctions valueCompiled environmentRelated runtime stateRelated
    rw [wordType] at valueRelated
    obtain rfl := word_result valueRelated
    obtain ⟨code, codeLowered, chain⟩ :=
      switch_selected (mapping := mapping) (environment := environment) armsLowered literals selected
    obtain ⟨arm, armMember, rfl⟩ := select_mem selected
    obtain ⟨_, sequenced⟩ := block_sequence (arms arm armMember) codeLowered
    obtain ⟨extension, target, finalStore, related, branchEvaluated, finalState, lastFrame⟩ :=
      branchSimulated noFunctions (arms arm armMember) sequenced (environmentRelated.prepend [.word word])
        (runtime.prepend [.word word]) middleState
    exact ⟨extension, target, finalStore, related, LanguageResult.bind_success _ valueEvaluated (chain branchEvaluated),
      finalState, firstFrame.trans lastFrame⟩
  case switchDefault =>
    intro sourceEnvironment value cases defaultBody span initial middle final control word evaluated unselected _
      branchSimulated fuel context inLoop head noFunctions eligible lowered world mapping environment store
      environmentRelated runtime stateRelated
    cases eligible with
    | switch _ literals _ defaults =>
    obtain ⟨loweredValue, branches, defaultCode, valueCompiled, wordType, armsLowered, defaultCompiled, rfl⟩ := lowered
    obtain ⟨valueTarget, middleStore, valueRelated, valueEvaluated, middleState, firstFrame⟩ :=
      expression_simulation step evaluated noFunctions valueCompiled environmentRelated runtime stateRelated
    rw [wordType] at valueRelated
    obtain rfl := word_result valueRelated
    obtain ⟨_, sequenced⟩ := block_sequence defaults defaultCompiled
    obtain ⟨extension, target, finalStore, related, branchEvaluated, finalState, lastFrame⟩ :=
      branchSimulated noFunctions defaults sequenced (environmentRelated.prepend [.word word])
        (runtime.prepend [.word word]) middleState
    exact ⟨extension, target, finalStore, related, LanguageResult.bind_success _ valueEvaluated
      (switch_unselected armsLowered literals unselected branchEvaluated), finalState, firstFrame.trans lastFrame⟩
  case switchFault =>
    intro sourceEnvironment value cases defaultBody span initial final reason evaluated
      fuel context inLoop head noFunctions _ lowered world mapping environment store environmentRelated runtime
      stateRelated
    obtain ⟨loweredValue, branches, defaultCode, valueCompiled, _, _, _, rfl⟩ := lowered
    obtain ⟨valueTarget, finalStore, valueRelated, valueEvaluated, finalState, frame⟩ :=
      expression_simulation step evaluated noFunctions valueCompiled environmentRelated runtime stateRelated
    cases valueRelated with
    | language reasonWord =>
        exact ⟨[], _, finalStore, .language reasonWord, LanguageResult.bind_failure _ valueEvaluated,
          by simpa only [List.append_nil] using finalState, frame⟩

/-- An eligible block simulates its actual `lowerStatements` code. -/
theorem block_simulation (step : BuiltinStep model slots) {supported : String → Prop} {resultType : Core.Ty}
    {sourceEnvironment : Semantics.Environment} {body : List YulStmt} {initial final : YulSemantics.State}
    {control : Semantics.Control} (eligible : YulFragment.Eligible supported body)
    (executed : YulSemantics.Run sourceEnvironment body initial control final)
    {fuel : Nat} {scope : Scope} {signatures : List Signature} {code : Core.Expr}
    (compiled : YulLowering.lowerStatements fuel scope resultType body signatures = .ok code)
    {world : World} {mapping : Renaming} {environment : Environment} {store : Store}
    (environmentRelated : EnvironmentRel world sourceEnvironment scope mapping environment)
    (runtime : EffectEnvironmentRel slots scope mapping environment)
    (stateRelated : StateRel model world initial store) :
    ∃ extension target finalStore, ControlRel resultType control target ∧
      Evaluates environment store (code.rename mapping) target finalStore ∧
      StateRel model (world ++ extension) final finalStore ∧ ClosuresPreserved store finalStore := by
  obtain ⟨_, sequenced⟩ := statements_sequence eligible.2 compiled
  exact sequence_simulation (supported := supported) step executed rfl eligible.2 sequenced environmentRelated runtime
    stateRelated

end Simulation

/-- Effects whose assembly rule is the fragment's run meet the assembly
obligation once their builtins do. -/
theorem assembly_preserves {supported : String → Prop} {model : StateModel RuntimeCallEffectsSemantics.State}
    {slots : List EffectSlot} {effects : Semantics.ExternalSemantics RuntimeCallEffectsSemantics.State}
    (assembled : ∀ {functions environment body initial control final},
      effects.assembly functions environment body initial control final →
        YulSemantics.Run environment body initial control final)
    (step : BuiltinStep model slots) :
    DerivationCorrespondence.AssemblyPreservation supported model slots effects := by
  intro functions sourceEnvironment body initial control final eligible executed signatures codes locations captured span
  intro fuel scope result loops expression compiled _ world mapping environment store environmentRelated _ runtime
    stateRelated installed
  cases fuel with
  | zero => simp [lowerStatement, fail] at compiled
  | succ fuel =>
      simp only [lowerStatement] at compiled
      obtain ⟨extension, target, finalStore, related, evaluated, finalState, closures⟩ :=
        block_simulation step eligible (assembled executed) compiled environmentRelated runtime stateRelated
      exact ⟨extension, target, finalStore, related, evaluated, finalState, installed.preserved closures, closures⟩

end Solcore.Frontend.RustHull.YulBlockCorrespondence
end
