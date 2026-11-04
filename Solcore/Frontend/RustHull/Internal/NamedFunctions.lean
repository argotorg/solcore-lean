import Solcore.Frontend.RustHull.Internal.LoweringFacts
import Solcore.Frontend.RustHull.Internal.Statements

/-!
# Named functions

Function installation, parameter initialization and calls to named functions within one compiled
program.
-/

section
-- leanmerge: from Solcore.Frontend.RustHull.NamedFunctionCorrespondence
/-! Named Hull functions connected to actual compilation and public execution.
The first connected family is the Word identity function, for every Word input.
Its source evaluation is derived independently; no hypothesis asserts that a
source body already corresponds to its compiled Core expression. -/
set_option autoImplicit false
set_option maxRecDepth 4096

namespace Solcore.Frontend.RustHull.Correspondence

def wordIdentityFunction : Function := {
  name := "identity"
  args := [{name := "value", ty := .word}]
  ret := .word
  body := [⟨.returnStmt ⟨.word, .var "value", none⟩, none⟩]
}

def wordIdentityProgram : Program := {
  entryPoints := ["identity"]
  functions := [wordIdentityFunction]
  objects := []
}

def wordIdentitySignature : Signature := ⟨"identity", [.word], .word⟩

def wordIdentityBody : Core.Expr :=
    .letE (Core.OptionalCell.allocateInitialized .word (.var 0))
      (Core.LocalControl.finish .word
        (Core.LocalLoop.toControl .word
          (Core.LocalLoop.sequence .word
            (Core.LocalLoop.returnValue .word
              (Core.OptionalCell.read .word (.var 0) (Core.Word.ofNatModulo 1)))
            (Core.LocalLoop.fallthrough .word)) (Core.Word.ofNatModulo 5))
        (Core.LanguageResult.failure .word (.word (Core.Word.ofNatModulo 4))))

def wordIdentityClosure : Core.Expr :=
  .lambda .word (Core.LanguageResult.resultType .word) wordIdentityBody

def wordIdentityInvocation : Core.Expr :=
  Core.LanguageResult.bind .word
    (Core.OptionalCell.read wordIdentitySignature.functionType (.var 0) (Core.Word.ofNatModulo 1))
    (.apply (.var 0) (.var 2))

def wordIdentityCompiled : Compiled :=
  ⟨"identity", [.word], .word,
    .lambda .word (Core.LanguageResult.resultType .word)
      (.letE (Core.OptionalCell.allocate wordIdentitySignature.functionType)
        (.letE (.storeCell (.var 0) (.inRight .unit wordIdentityClosure))
          (wordIdentityInvocation.weakenAt 0)))⟩

private theorem value_not_reserved : "value".startsWith Effects.reservedPrefix = false := by decide
private theorem identity_not_reserved : "identity".startsWith Effects.reservedPrefix = false := by decide

theorem wordIdentity_read (scope : Scope) (signatures : List Signature) :
    lowerExpression 30 signatures (scope.addLocal "value" .word)
      ⟨.word, .var "value", none⟩ =
        .ok ⟨.word, Core.OptionalCell.read .word (.var 0) (Core.Word.ofNatModulo 1)⟩ := by
  simp [lowerExpression, lowerType, Scope.read, Scope.addLocal, scope_lookup_cons,
    value_not_reserved, expectType, Pure.pure, Except.pure]
  rfl

theorem wordIdentity_statements (scope : Scope) (signatures : List Signature) :
    lowerStatements 32 signatures (scope.addLocal "value" .word) .word 0 wordIdentityFunction.body =
      .ok (Core.LocalLoop.sequence .word
        (Core.LocalLoop.returnValue .word
          (Core.OptionalCell.read .word (.var 0) (Core.Word.ofNatModulo 1)))
        (Core.LocalLoop.fallthrough .word)) := by
  simp only [wordIdentityFunction, lowerStatements, lowerStatement]
  rw [wordIdentity_read]
  rfl

theorem wordIdentity_lowerFunction (scope : Scope) (signatures : List Signature) :
    lowerFunction 32 signatures scope wordIdentityFunction wordIdentitySignature = .ok wordIdentityClosure := by
  have unique : ["value"].eraseDups.length = 1 := by decide
  have reservedFalse : ¬ Effects.reservedPrefix.toList <+: ['v', 'a', 'l', 'u', 'e'] := by decide
  have statements := wordIdentity_statements (scope.temporary .word) signatures
  simp only [wordIdentityFunction] at statements
  simp [lowerFunction, wordIdentityFunction, wordIdentitySignature, unique, statements,
    reservedFalse, bundleType, projectArgument, wordIdentityClosure, wordIdentityBody,
    Pure.pure, Except.pure, Bind.bind, Except.bind]

theorem wordIdentity_typed : Core.HasType [] wordIdentityCompiled.expression
    (.function .word (Core.LanguageResult.resultType .word)) := by
  apply Core.infer_sound
  simp only [wordIdentityCompiled, wordIdentityClosure, wordIdentityBody, wordIdentityInvocation,
    wordIdentitySignature, Signature.functionType, bundleType,
    Core.OptionalCell.allocate, Core.OptionalCell.allocateInitialized, Core.OptionalCell.read,
    Core.LocalControl.finish, Core.LocalLoop.toControl, Core.LocalLoop.sequence,
    Core.LocalLoop.returnValue, Core.LocalLoop.returned, Core.LocalLoop.fallthrough,
    Core.LanguageResult.bind, Core.LanguageResult.success, Core.LanguageResult.failure,
    Core.Expr.weakenAt]
  rfl

theorem wordIdentity_compile :
    compile wordIdentityProgram "identity" 32 = .ok wordIdentityCompiled := by
  have unique : ["identity"].eraseDups.length = 1 := by decide
  have closure := wordIdentity_lowerFunction
    [⟨some (Effects.slotName "function$identity"), wordIdentitySignature.functionType, true⟩]
    [wordIdentitySignature]
  simp only [wordIdentityFunction, wordIdentitySignature] at closure
  simp [compile, assemble, wordIdentityProgram, signature, wordIdentityFunction,
    identity_not_reserved, lowerType, expectType, unique, closure, scope_lookup_cons,
    Bind.bind, Except.bind, Pure.pure, Except.pure]
  have checked := (Core.inferDetailed_iff_typing (path := [])).mpr wordIdentity_typed
  simp only [wordIdentityCompiled, wordIdentityInvocation, wordIdentitySignature] at checked
  simp only [bundleType]
  rw [checked]
  rfl

theorem wordIdentity_parameters : wordIdentityCompiled.parameters = [.word] := rfl

def wordIdentityPrepared (value : Core.Word) : ScalarExecution.Prepared :=
  ⟨wordIdentityCompiled, .word value⟩

def wordIdentityStore (value : Core.Word) : Core.Store :=
  [.inRight .unit (.closure .word (Core.LanguageResult.resultType .word) wordIdentityBody
    [.cellRef (Core.OptionalCell.cellType wordIdentitySignature.functionType) 0, .word value]),
   .inRight .unit (.word value)]

theorem wordIdentity_run (value : Core.Word) :
    ScalarExecution.run (wordIdentityPrepared value) 1000 =
      .done (.inRight .word (.word value)) (wordIdentityStore value) := by
  simp only [ScalarExecution.run, ScalarExecution.Prepared.expression, wordIdentityPrepared,
    wordIdentityCompiled, wordIdentityClosure, wordIdentityBody, wordIdentityInvocation,
    wordIdentityStore, Core.OptionalCell.allocate, Core.OptionalCell.allocateInitialized,
    Core.OptionalCell.read, Core.LocalControl.finish, Core.LocalLoop.toControl,
    Core.LocalLoop.sequence, Core.LocalLoop.returnValue, Core.LocalLoop.returned,
    Core.LocalLoop.fallthrough, Core.LanguageResult.bind, Core.LanguageResult.success,
    Core.LanguageResult.failure, Core.Expr.weakenAt]
  rfl

theorem wordIdentity_evaluates (value : Core.Word) :
    Core.Evaluates [] [] (wordIdentityPrepared value).expression
      (.inRight .word (.word value)) (wordIdentityStore value) :=
  ScalarExecution.run_done_evaluates (wordIdentity_run value)

theorem wordIdentity_source {σ : Type} (effects : Semantics.ExternalSemantics σ)
    (external : σ) (value : Core.Word) :
    Semantics.EvalFunction [wordIdentityFunction] effects wordIdentityFunction [.word value]
      ⟨[], external⟩ (.value (.word value)) ⟨[.word value], external⟩ := by
  apply Semantics.EvalFunction.body (control := .returned (.word value))
  · rfl
  · apply Semantics.EvalStatements.stop
    · intros; intro equality; cases equality
    · apply Semantics.EvalStmt.returned rfl
      have evaluated := Semantics.EvalExpr.var (functions := [wordIdentityFunction]) (effects := effects)
        (env := [("value", 0)]) (state := (⟨[.word value], external⟩ : Semantics.State σ))
        (expression := (⟨.word, .var "value", none⟩ : Expr)) rfl
      simpa [Semantics.readResult, Semantics.lookupLocation] using evaluated
    · intro equality; cases equality

theorem wordIdentity_heap (value : Core.Word) :
    HeapRel [(.word, 1)] [.word value] (wordIdentityStore value) where
  length_eq := rfl
  cell := by
    intro index type location entry
    cases index with
    | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at entry
        obtain ⟨rfl, rfl⟩ := entry.symm
        refine ⟨.word value, .word value, rfl, ?_, .word value⟩
        rfl
    | succ index => simp at entry
  distinct := by
    intro left right leftType rightType location leftEntry rightEntry
    cases left <;> cases right <;> simp_all

theorem wordIdentity_prepare {input : String} {value : Core.Word}
    (parsed : parseWord input = .ok value) :
    ScalarExecution.prepare wordIdentityProgram "identity" [input] 32 =
      .ok (wordIdentityPrepared value) := by
  simp only [ScalarExecution.prepare, wordIdentity_compile, Except.mapError, Bind.bind, Except.bind]
  rw [wordIdentity_parameters]
  change (do
    let argument ← (ScalarExecution.parseArguments [.word] [input]).mapError ScalarExecution.Error.input
    pure (ScalarExecution.Prepared.mk wordIdentityCompiled argument)) = .ok (wordIdentityPrepared value)
  simp [ScalarExecution.parseArguments, ScalarExecution.parseInput, parsed,
    Except.mapError, Bind.bind, Except.bind, wordIdentityPrepared]
  rfl

/-- The actual public parser/compiler and every finite checkpoint chain agree
with the independently derived source result and its final local heap. -/
theorem wordIdentity_preserves {σ : Type} (effects : Semantics.ExternalSemantics σ)
    (external : σ) {input : String} {value : Core.Word}
    (parsed : parseWord input = .ok value) :
    ScalarExecution.prepare wordIdentityProgram "identity" [input] 32 =
        .ok (wordIdentityPrepared value) ∧
      Semantics.EvalFunction [wordIdentityFunction] effects wordIdentityFunction [.word value]
        ⟨[], external⟩ (.value (.word value)) ⟨[.word value], external⟩ ∧
      HeapRel [(.word, 1)] [.word value] (wordIdentityStore value) ∧
      ResultRel .word (.value (.word value)) (.inRight .word (.word value)) ∧
      ∃ required, ∀ fuel additional last,
        ScalarExecution.Resumes (ScalarExecution.run (wordIdentityPrepared value) fuel) additional last →
          (last = .done (.inRight .word (.word value)) (wordIdentityStore value) ↔
            required ≤ fuel + additional) ∧
          ((∃ checkpoint, last = .outOfFuel checkpoint) ↔ fuel + additional < required) := by
  exact ⟨wordIdentity_prepare parsed, wordIdentity_source effects external value,
    wordIdentity_heap value, .value (.word value),
    ScalarExecution.evaluation_resumes_exact (wordIdentity_evaluates value)⟩

end Solcore.Frontend.RustHull.Correspondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.FunctionInstallationCorrespondence
/-! Actual argument-cell initialization for named Hull functions. Bundle
projection and initialized allocation use the same expressions as lowerFunction;
the source heap and Core heap retain their distinct location spaces. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.Correspondence
open ScalarExecution

theorem projectArgument_evaluates {values : List Core.Value} {index : Nat} {value : Core.Value}
    {environment : Core.Environment} {initial final : Core.Store} {expression : Core.Expr}
    (evaluated : Core.Evaluates environment initial expression (bundleValues values) final)
    (found : values[index]? = some value) :
    Core.Evaluates environment initial (projectArgument index values.length expression) value final := by
  induction values generalizing index expression with
  | nil => simp at found
  | cons head tail ih =>
      cases tail with
      | nil =>
          cases index with
          | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at found; subst value; exact evaluated
          | succ index => simp at found
      | cons next rest =>
          cases index with
          | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at found
              subst value
              exact .first evaluated
          | succ index =>
              exact ih (.second evaluated) found

/-- This is the exact fold used by lowerFunction, with an explicit index
offset for induction through earlier argument allocations. -/
def parameterCode (total start : Nat) (types : List Core.Ty) (body : Core.Expr) : Core.Expr :=
  (types.zipIdx start).foldr (fun (type, index) body =>
    .letE (Core.OptionalCell.allocateInitialized type
      (projectArgument index total (.var index))) body) body

/-- Deterministic allocation of argument cells, retaining all existing cells
and adding the new references to the lexical environment in source order. -/
inductive ParameterCells : List Core.Ty → List Core.Value → Core.Environment → Core.Store →
    Core.Environment → Core.Store → Prop where
  | nil {environment store} : ParameterCells [] [] environment store environment store
  | cons {type types value values environment store finalEnvironment finalStore}
      (rest : ParameterCells types values
        (.cellRef (Core.OptionalCell.cellType type) store.length :: environment)
        (store ++ [.inRight .unit value]) finalEnvironment finalStore) :
      ParameterCells (type :: types) (value :: values) environment store finalEnvironment finalStore

/-- A ParameterCells derivation executes the compiler's actual allocation
fold before entering the body. It does not replace it with a host initializer. -/
theorem ParameterCells.evaluates {types : List Core.Ty} {values allValues : List Core.Value}
    {environment finalEnvironment : Core.Environment} {initial allocated final : Core.Store}
    (cells : ParameterCells types values environment initial finalEnvironment allocated)
    {start : Nat} (argument : environment[start]? = some (bundleValues allValues))
    (selected : ∀ index value, values[index]? = some value → allValues[start + index]? = some value)
    {body : Core.Expr} {result : Core.Value}
    (evaluated : Core.Evaluates finalEnvironment allocated body result final) :
    Core.Evaluates environment initial (parameterCode allValues.length start types body) result final := by
  induction cells generalizing start with
  | nil => exact evaluated
  | @cons type types value values environment store finalEnvironment finalStore rest ih =>
      simp only [parameterCode, List.zipIdx_cons, List.foldr_cons]
      apply Core.Evaluates.letE
        (Core.OptionalCell.allocateInitialized_evaluates
          (projectArgument_evaluates (.var argument) (by simpa using selected 0 value rfl)))
      apply ih (start := start + 1)
      · exact argument
      · intro index selectedValue found
        simpa only [Nat.add_assoc, Nat.add_comm 1 index] using selected (index + 1) selectedValue found
      · exact evaluated

def parameterScope (arguments : List Arg) (types : List Core.Ty) (scope : Scope) : Scope :=
  (arguments.zip types).foldl (fun scope (argument, type) => scope.addLocal argument.name type) scope

/-- The actual source binder and the argument-cell allocation agree, deriving
both local environments, both heaps and the external-state invariant. -/
theorem initialize_parameters {σ : Type} {arguments : List Arg} {types : List Core.Ty}
    {sources : List Semantics.Value} {targets : List Core.Value}
    (values : ValuesRel types sources targets) (arity : arguments.length = types.length)
    {sourceEnvironment : Semantics.Environment} {scope : Scope} {sourceState : Semantics.State σ}
    {world : World} {environment : Core.Environment} {store : Core.Store}
    (environmentRelated : EnvironmentRel world sourceEnvironment scope Core.Renaming.id environment)
    (heapRelated : HeapRel world sourceState.heap store)
    {external : σ → Core.Store → Prop} (externalRelated : external sourceState.external store)
    (frame : ∀ state store type value, external state store →
      external state (store ++ [Core.Value.inRight type value])) :
    ∃ extension sourceEnvironment' sourceState' environment' store',
      Semantics.bindArguments arguments sources sourceEnvironment sourceState = some (sourceEnvironment', sourceState') ∧
      ParameterCells types targets environment store environment' store' ∧
      EnvironmentRel (world ++ extension) sourceEnvironment' (parameterScope arguments types scope)
        Core.Renaming.id environment' ∧
      HeapRel (world ++ extension) sourceState'.heap store' ∧
      external sourceState'.external store' := by
  induction values generalizing arguments sourceEnvironment scope sourceState world environment store with
  | nil =>
      have empty : arguments = [] := List.eq_nil_of_length_eq_zero arity
      subst arguments
      exact ⟨[], sourceEnvironment, sourceState, environment, store, rfl, .nil,
        by simpa [parameterScope] using environmentRelated, by simpa using heapRelated, externalRelated⟩
  | @cons type types source sources target targets head tail ih =>
      cases arguments with
      | nil => simp at arity
      | cons argument arguments =>
          have arity' : arguments.length = types.length := Nat.succ.inj arity
          have entry : (world ++ [(type, store.length)])[sourceState.heap.length]? = some (type, store.length) := by
            rw [← heapRelated.length_eq, List.getElem?_concat_length]
          have environment' := ((environmentRelated.extendWorld [(type, store.length)]).addLocal
            argument.name type sourceState.heap.length store.length entry)
          have heap' := heapRelated.allocate head
          have external' := frame sourceState.external store .unit target externalRelated
          obtain ⟨extension, sourceEnvironment', sourceState', environment'', store', bound,
            allocated, locals, heap, external⟩ := ih arity'
              (sourceState := (Semantics.allocate sourceState source).2)
              (sourceEnvironment := (argument.name, sourceState.heap.length) :: sourceEnvironment)
              (scope := scope.addLocal argument.name type)
              (world := world ++ [(type, store.length)])
              (environment := .cellRef (Core.OptionalCell.cellType type) store.length :: environment)
              (store := store ++ [.inRight .unit target])
              (by simpa only [Core.Renaming.lift_id] using environment')
              (by simpa only [Semantics.allocate] using heap')
              (by simpa only [Semantics.allocate] using external')
          refine ⟨[(type, store.length)] ++ extension, sourceEnvironment', sourceState', environment'', store',
            ?_, .cons allocated, ?_, ?_, external⟩
          · exact bound
          · simpa only [List.append_assoc, parameterScope, List.zip_cons_cons, List.foldl_cons] using locals
          · simpa only [List.append_assoc] using heap

end Solcore.Frontend.RustHull.Correspondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.FunctionBodyCorrespondence
/-! The actual function lowerer wraps a statement control result, then allocates
the declared parameters. This module relates that result wrapper to the
independent source function boundary. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.StatementCorrespondence

open Correspondence ScalarExecution

private theorem mapM_length {α β : Type} {action : α → LowerM β}
    {inputs : List α} {outputs : List β} (accepted : inputs.mapM action = .ok outputs) :
    inputs.length = outputs.length := by
  induction inputs generalizing outputs with
  | nil => cases accepted; rfl
  | cons input rest ih =>
      simp only [List.mapM_cons] at accepted
      obtain ⟨head, _, accepted⟩ := lower_bind_eq_ok.mp accepted
      obtain ⟨tail, tailAccepted, returned⟩ := lower_bind_eq_ok.mp accepted
      cases returned
      exact congrArg Nat.succ (ih tailAccepted)

theorem signature_components {fuel : Nat} {function : Function} {own : Signature}
    (compiled : signature fuel function = .ok own) :
    function.args.length = own.parameters.length ∧ lowerType fuel function.ret = .ok own.result := by
  by_cases reserved : function.name.startsWith Effects.reservedPrefix
  · simp [signature, reserved, fail, Bind.bind, Except.bind] at compiled
  · simp only [signature, reserved, Bool.false_eq_true, ↓reduceIte] at compiled
    obtain ⟨parameters, parametersCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
    obtain ⟨result, resultCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
    cases returned
    exact ⟨mapM_length parametersCompiled, resultCompiled⟩

def finishedBody (type : Core.Ty) (statements : Core.Expr) : Core.Expr :=
  Core.LocalControl.finish type
    (Core.LocalLoop.toControl type statements (Core.Word.ofNatModulo 5))
    (if type = .unit then Core.LanguageResult.success .unit
     else Core.LanguageResult.failure type (.word (Core.Word.ofNatModulo 4)))

@[simp] theorem finishedBody_rename (type : Core.Ty) (statements : Core.Expr)
    (mapping : Core.Renaming) :
    (finishedBody type statements).rename mapping = finishedBody type (statements.rename mapping) := by
  by_cases unit : type = .unit <;>
    simp [finishedBody, unit, Core.LocalControl.finish, Core.LocalLoop.toControl,
      Core.LanguageResult.bind, Core.LanguageResult.success, Core.LanguageResult.failure,
      Core.Expr.rename, Core.Expr.weakenAt, Core.Renaming.lift]

theorem lowerFunction_components {fuel : Nat} {signatures : List Signature} {scope : Scope}
    {function : Function} {own : Signature} {expression : Core.Expr}
    (compiled : lowerFunction fuel signatures scope function own = .ok expression) :
    ∃ statements,
      lowerStatements fuel signatures
        ((function.args.zip own.parameters).foldl
          (fun scope (argument, type) => scope.addLocal argument.name type)
          (scope.temporary (bundleType own.parameters))) own.result 0 function.body = .ok statements ∧
      expression = .lambda (bundleType own.parameters) (Core.LanguageResult.resultType own.result)
        (own.parameters.zipIdx.foldr (fun (type, index) body =>
          .letE (Core.OptionalCell.allocateInitialized type
            (projectArgument index own.parameters.length (.var index))) body)
          (finishedBody own.result statements)) := by
  by_cases unique : (function.args.map (·.name)).eraseDups.length = function.args.length
  · simp only [lowerFunction, unique, ↓reduceIte] at compiled
    obtain ⟨checked, _, compiled⟩ := lower_bind_eq_ok.mp compiled
    cases checked
    obtain ⟨statements, bodyCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
    cases returned
    exact ⟨statements, bodyCompiled, rfl⟩
  · simp [lowerFunction, unique, fail, Bind.bind, Except.bind] at compiled

theorem finish_preserves {fuel : Nat} {sourceType : Ty} {type : Core.Ty}
    (typeCompiled : lowerType fuel sourceType = .ok type)
    {control : Semantics.Control} {target : Core.Value} (related : ControlRel type control target)
    {statements : Core.Expr} {mapping : Core.Renaming} {environment : Core.Environment}
    {initial final : Core.Store}
    (evaluated : Core.Evaluates environment initial (statements.rename mapping) target final) :
    ∃ result, ResultRel type (Semantics.finishFunction sourceType control) result ∧
      Core.Evaluates environment initial ((finishedBody type statements).rename mapping) result final := by
  rw [finishedBody_rename]
  cases related with
  | returned valueRelated =>
      exact ⟨_, .value valueRelated, Core.LocalControl.finish_returned _
        (Core.LocalLoop.toControl_normal _ _ evaluated)⟩
  | language reason =>
      exact ⟨_, .language reason, Core.LocalControl.finish_failure _
        (Core.LocalLoop.toControl_failure _ _ evaluated)⟩
  | breaking =>
      exact ⟨_, .language _, Core.LocalControl.finish_failure _
        (Core.LocalLoop.toControl_transfer _ _ evaluated)⟩
  | continuing =>
      exact ⟨_, .language _, Core.LocalControl.finish_failure _
        (Core.LocalLoop.toControl_transfer _ _ evaluated)⟩
  | fallthrough =>
      obtain ⟨shape, shapeFound, typeEqual⟩ := lowerType_shape typeCompiled
      by_cases unit : type = .unit
      · have shapeUnit : shape = .unit := coreType_injective (typeEqual.trans unit)
        subst shape
        subst type
        refine ⟨.inRight .word .unit, ?_, ?_⟩
        · simp only [Semantics.finishFunction, shapeFound]
          exact ResultRel.value ValueRel.unit
        · apply Core.LocalControl.finish_fallthrough _ (Core.LocalLoop.toControl_normal _ _ evaluated)
          simp only [↓reduceIte, Core.LanguageResult.success, Core.Expr.weakenAt]
          exact .inRight .unit
      · have shapeNotUnit : shape ≠ .unit := by
          intro same
          exact unit (typeEqual.symm.trans (congrArg coreType same))
        have guard : (shape == Semantics.Shape.unit) = false := by
          cases shape <;> first | contradiction | rfl
        refine ⟨.inLeft type (.word (Core.Word.ofNatModulo 4)), ?_, ?_⟩
        · simpa only [Semantics.finishFunction, shapeFound, Option.some_beq_some, guard,
            Bool.false_eq_true, ↓reduceIte] using ResultRel.language (type := type) (Core.Word.ofNatModulo 4)
        · apply Core.LocalControl.finish_fallthrough _ (Core.LocalLoop.toControl_normal _ _ evaluated)
          simp only [unit, ↓reduceIte, Core.LanguageResult.failure, Core.Expr.weakenAt]
          exact .inLeft .word

theorem straight_line_body {σ : Type} {functions : List Function}
    {effects : Semantics.ExternalSemantics σ} {signatures : List Signature}
    {external : σ → Core.Store → Prop} (frame : ExternalFrame external)
    {typeFuel fuel : Nat} {sourceType : Ty} {scope : Scope} {type : Core.Ty}
    {expression : Core.Expr} {statements : List Stmt}
    (typeCompiled : lowerType typeFuel sourceType = .ok type)
    (compiled : lowerStatements fuel signatures scope type 0 statements = .ok expression)
    (eligible : ∀ statement ∈ statements, StraightLine functions effects signatures external statement)
    {sourceEnvironment : Semantics.Environment} {initial final : Semantics.State σ}
    {control : Semantics.Control}
    (sourceEvaluated : Semantics.EvalStatements functions effects sourceEnvironment statements initial control final)
    (normal : NormalControl control)
    {world : World} {mapping : Core.Renaming} {environment : Core.Environment} {store : Core.Store}
    (environmentRelated : EnvironmentRel world sourceEnvironment scope mapping environment)
    (heapRelated : HeapRel world initial.heap store) (externalRelated : external initial.external store) :
    ∃ extension targetValue finalStore,
      ResultRel type (Semantics.finishFunction sourceType control) targetValue ∧
      Core.Evaluates environment store ((finishedBody type expression).rename mapping) targetValue finalStore ∧
      HeapRel (world ++ extension) final.heap finalStore ∧ external final.external finalStore := by
  obtain ⟨extension, controlValue, finalStore, related, evaluated, finalHeap, finalExternal⟩ :=
    straight_line_statements frame compiled eligible sourceEvaluated normal
      environmentRelated heapRelated externalRelated
  obtain ⟨value, resultRelated, finished⟩ := finish_preserves typeCompiled related evaluated
  exact ⟨extension, value, finalStore, resultRelated, finished, finalHeap, finalExternal⟩

/-- Calling the actual lowered function derives its parameter cells from the
supplied argument bundle, then preserves the independent source body execution.
No assumption supplies a preinitialized parameter environment or heap. -/
theorem lowerFunction_apply {σ : Type} {functions : List Function}
    {effects : Semantics.ExternalSemantics σ} {signatures : List Signature}
    {external : σ → Core.Store → Prop} (frame : ExternalFrame external)
    {typeFuel fuel : Nat} {scope : Scope} {function : Function} {own : Signature}
    {expression argument : Core.Expr}
    (signatureCompiled : signature typeFuel function = .ok own)
    (compiled : lowerFunction fuel signatures scope function own = .ok expression)
    (eligible : ∀ statement ∈ function.body, StraightLine functions effects signatures external statement)
    {sources : List Semantics.Value} {targets : List Core.Value}
    (values : ValuesRel own.parameters sources targets)
    {initial allocated final : Semantics.State σ} {sourceEnvironment : Semantics.Environment}
    (bound : Semantics.bindArguments function.args sources [] initial = some (sourceEnvironment, allocated))
    {control : Semantics.Control}
    (sourceEvaluated : Semantics.EvalStatements functions effects sourceEnvironment function.body allocated control final)
    (normal : NormalControl control)
    {world : World} {environment : Core.Environment} {initialStore callStore : Core.Store}
    (argumentEvaluated : Core.Evaluates environment initialStore argument (bundleValues targets) callStore)
    (heapRelated : HeapRel world initial.heap callStore)
    (externalRelated : external initial.external callStore) :
    ∃ extension targetValue finalStore,
      ResultRel own.result (Semantics.finishFunction function.ret control) targetValue ∧
      Core.Evaluates environment initialStore (.apply expression argument) targetValue finalStore ∧
      HeapRel (world ++ extension) final.heap finalStore ∧ external final.external finalStore := by
  obtain ⟨arity, resultCompiled⟩ := signature_components signatureCompiled
  obtain ⟨statements, statementsCompiled, rfl⟩ := lowerFunction_components compiled
  have emptyEnvironment : EnvironmentRel world [] (scope.temporary (bundleType own.parameters))
      Core.Renaming.id (bundleValues targets :: environment) := by
    intro name sourceLocation binding index found looked
    simp [Semantics.lookupLocation] at found
  obtain ⟨parameterExtension, sourceEnvironment', allocated', environment', store',
      sourceBound, cells, parametersRelated, allocatedHeap, allocatedExternal⟩ :=
    initialize_parameters values arity emptyEnvironment heapRelated externalRelated
      (fun _ _ _ _ hypothesis => frame.allocate hypothesis)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (bound.symm.trans sourceBound))
  obtain ⟨extension, targetValue, finalStore, related, executed, finalHeap, finalExternal⟩ :=
    straight_line_body frame resultCompiled statementsCompiled eligible sourceEvaluated normal
      parametersRelated allocatedHeap allocatedExternal
  have bodyExecuted : Core.Evaluates environment' store' (finishedBody own.result statements)
      targetValue finalStore := by
    simpa only [Core.Expr.rename_id] using executed
  have initialized := cells.evaluates (allValues := targets) (start := 0) rfl
    (fun index value found => by simpa only [Nat.zero_add] using found) bodyExecuted
  refine ⟨parameterExtension ++ extension, targetValue, finalStore, related, ?_, ?_, finalExternal⟩
  · apply Core.Evaluates.apply .lambda argumentEvaluated
    simpa only [parameterCode, values.length.2] using initialized
  · simpa only [List.append_assoc] using finalHeap

end Solcore.Frontend.RustHull.StatementCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.FunctionAssemblyCorrespondence
/-! Installation of the actual global function cell used by the scalar Hull
compiler. The source heap omits this administrative cell; the closure still
captures its real mutable reference, exactly as in assemble. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.Correspondence

def singleFunctionScope (own : Signature) : Scope :=
  [⟨some (Effects.slotName ("function$" ++ own.name)), own.functionType, true⟩]

def singleFunctionInvocation (own : Signature) : Core.Expr :=
  Core.LanguageResult.bind own.result
    (Core.OptionalCell.read own.functionType (.var 0) (Core.Word.ofNatModulo 1))
    (.apply (.var 0) (.var 2))

def singleFunctionAllocation (own : Signature) (closure : Core.Expr) : Core.Expr :=
  .letE (Core.OptionalCell.allocate own.functionType)
    (.letE (.storeCell (.var 0) (.inRight .unit closure))
      ((singleFunctionInvocation own).weakenAt 0))

theorem signature_name {fuel : Nat} {function : Function} {own : Signature}
    (compiled : signature fuel function = .ok own) : own.name = function.name := by
  by_cases reserved : function.name.startsWith Effects.reservedPrefix
  · simp [signature, reserved, fail, Bind.bind, Except.bind] at compiled
  · simp only [signature, reserved, Bool.false_eq_true, ↓reduceIte] at compiled
    obtain ⟨_, _, compiled⟩ := lower_bind_eq_ok.mp compiled
    obtain ⟨_, _, returned⟩ := lower_bind_eq_ok.mp compiled
    cases returned
    rfl

/-- Successful assembly of one function exposes the actual signature,
lowered closure, allocation, installation and entry invocation. -/
theorem assemble_single_components {fuel : Nat} {function : Function} {entry : String}
    {own : Signature} {allocated : Core.Expr}
    (compiled : assemble [function] entry [] fuel = .ok (own, allocated)) :
    entry = function.name ∧ signature fuel function = .ok own ∧
      ∃ closure, lowerFunction fuel [own] (singleFunctionScope own) function own = .ok closure ∧
        allocated = singleFunctionAllocation own closure := by
  have unique : [function.name].eraseDups.length = 1 := by
    simp [List.eraseDups_cons, List.eraseDups_nil]
  cases signatureCompiled : signature fuel function with
  | error error =>
      simp [assemble, unique, signatureCompiled, List.mapM_cons, Bind.bind, Except.bind] at compiled
  | ok own' =>
      have sourceName := signature_name signatureCompiled
      by_cases names : own'.name = entry
      · have reduced : (do
            let closure ← lowerFunction fuel [own'] (singleFunctionScope own') function own'
            pure (own', singleFunctionAllocation own' closure)) = .ok (own, allocated) := by
          cases lowered : lowerFunction fuel [own'] (singleFunctionScope own') function own' with
          | error error =>
              have lowered' := lowered
              simp only [singleFunctionScope, names] at lowered'
              simp [assemble, unique, signatureCompiled, List.mapM_cons, names,
                lowered', Bind.bind, Except.bind, Pure.pure, Except.pure] at compiled
          | ok closure =>
              have lowered' := lowered
              simp only [singleFunctionScope, names] at lowered'
              simpa [assemble, unique, signatureCompiled, List.mapM_cons, names,
                singleFunctionScope, Scope.lookup, singleFunctionAllocation, singleFunctionInvocation,
                lowered', Bind.bind, Except.bind, Pure.pure, Except.pure] using compiled
        obtain ⟨closure, closureCompiled, returned⟩ := lower_bind_eq_ok.mp reduced
        cases returned
        exact ⟨names.symm.trans sourceName, rfl, closure, closureCompiled, rfl⟩
      · simp [assemble, unique, signatureCompiled, List.mapM_cons, names, fail, Bind.bind, Except.bind, Pure.pure, Except.pure] at compiled

def singleFunctionEnvironment (own : Signature) (input : Core.Value)
    (environment : Core.Environment) (store : Core.Store) : Core.Environment :=
  .cellRef (Core.OptionalCell.cellType own.functionType) store.length :: input :: environment

def singleFunctionStore (own : Signature) (body : Core.Expr) (input : Core.Value)
    (environment : Core.Environment) (store : Core.Store) : Core.Store :=
  store ++ [.inRight .unit (.closure (bundleType own.parameters)
    (Core.LanguageResult.resultType own.result) body
    (singleFunctionEnvironment own input environment store))]

/-- Executing the actual single-function installation calls the installed
closure with the input bundle. The premise concerns its real captured
environment after installation, not an alternate interpreter. -/
theorem singleFunctionAllocation_evaluates {own : Signature} {body : Core.Expr}
    {input result : Core.Value} {environment : Core.Environment} {initial final : Core.Store}
    (evaluated : Core.Evaluates
      (input :: singleFunctionEnvironment own input environment initial)
      (singleFunctionStore own body input environment initial) body result final) :
    Core.Evaluates (input :: environment) initial
      (singleFunctionAllocation own
        (.lambda (bundleType own.parameters) (Core.LanguageResult.resultType own.result) body))
      result final := by
  have written : (initial ++ [Core.Value.inLeft own.functionType .unit]).write? initial.length
      (.inRight .unit (.closure (bundleType own.parameters)
        (Core.LanguageResult.resultType own.result) body
        (singleFunctionEnvironment own input environment initial))) =
      some (singleFunctionStore own body input environment initial) := by
    simp [Core.Store.write?, singleFunctionStore]
  have installed : Core.Evaluates (singleFunctionEnvironment own input environment initial)
      (initial ++ [.inLeft own.functionType .unit])
      (.storeCell (.var 0) (.inRight .unit
        (.lambda (bundleType own.parameters) (Core.LanguageResult.resultType own.result) body)))
      .unit (singleFunctionStore own body input environment initial) :=
    Core.Evaluates.storeCell (oldValue := .inLeft own.functionType .unit)
      (.var rfl) (by simp [Core.Store.read?]) (.inRight .lambda) written
  apply Core.Evaluates.letE (Core.OptionalCell.allocate_evaluates _ _ _)
  apply Core.Evaluates.letE installed
  have invocation : (singleFunctionInvocation own).weakenAt 0 =
      Core.LanguageResult.bind own.result
        (Core.OptionalCell.read own.functionType (.var 1) (Core.Word.ofNatModulo 1))
        (.apply (.var 0) (.var 3)) := by
    simp [singleFunctionInvocation, Core.LanguageResult.bind, Core.OptionalCell.read,
      Core.LanguageResult.failure, Core.LanguageResult.success, Core.Expr.weakenAt]
  rw [invocation]
  change Core.Evaluates (.unit :: singleFunctionEnvironment own input environment initial)
    (singleFunctionStore own body input environment initial)
    (Core.LanguageResult.bind own.result
      (Core.OptionalCell.read own.functionType (.var 1) (Core.Word.ofNatModulo 1))
      (.apply (.var 0) (.var 3))) result final
  have initialized : (singleFunctionStore own body input environment initial).read? initial.length =
      some (.inRight .unit (.closure (bundleType own.parameters)
        (Core.LanguageResult.resultType own.result) body
        (singleFunctionEnvironment own input environment initial))) := by
    simp [singleFunctionStore, Core.Store.read?]
  apply Core.LanguageResult.bind_success own.result
    (Core.OptionalCell.read_success (Core.Word.ofNatModulo 1) (.var rfl) initialized)
  exact Core.Evaluates.apply (.var rfl) (.var rfl) evaluated

/-- Connect an application proved for the actual lowered function to its
public compiler wrapper, including evaluation of the caller's argument and
installation of the global function cell. -/
theorem singleFunction_apply {own : Signature} {body argument : Core.Expr}
    {input result : Core.Value} {environment : Core.Environment}
    {initial argumentStore final : Core.Store}
    (argumentEvaluated : Core.Evaluates environment initial argument input argumentStore)
    (evaluated : Core.Evaluates
      (singleFunctionEnvironment own input environment argumentStore)
      (singleFunctionStore own body input environment argumentStore)
      (.apply (.lambda (bundleType own.parameters) (Core.LanguageResult.resultType own.result) body)
        (.var 1)) result final) :
    Core.Evaluates environment initial
      (.apply (.lambda (bundleType own.parameters) (Core.LanguageResult.resultType own.result)
        (singleFunctionAllocation own
          (.lambda (bundleType own.parameters) (Core.LanguageResult.resultType own.result) body)))
        argument) result final := by
  cases evaluated with
  | apply functionEvaluated inputEvaluated bodyEvaluated =>
      cases functionEvaluated
      cases inputEvaluated with
      | var found =>
          simp only [singleFunctionEnvironment, List.getElem?_cons_succ,
            List.getElem?_cons_zero, Option.some.injEq] at found
          subst_vars
          exact Core.Evaluates.apply .lambda argumentEvaluated
            (singleFunctionAllocation_evaluates bodyEvaluated)

end Solcore.Frontend.RustHull.Correspondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ParameterRenamingCorrespondence
/-! Argument initialization under the actual renamings used when global
closures capture administrative binders from preceding registrations. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.Correspondence
open ScalarExecution

def parameterRenaming : Nat → Core.Renaming → Core.Renaming
  | 0, mapping => mapping
  | count + 1, mapping => parameterRenaming count mapping.lift

theorem projectArgument_rename (index count : Nat) (expression : Core.Expr) (mapping : Core.Renaming) :
    (projectArgument index count expression).rename mapping =
      projectArgument index count (expression.rename mapping) := by
  induction count generalizing index expression with
  | zero => rfl
  | succ count ih =>
      cases count with
      | zero => rfl
      | succ count =>
          by_cases first : index = 0 <;> simp [projectArgument, first, Core.Expr.rename, ih]

theorem ParameterCells.evaluates_renamed {types : List Core.Ty} {values allValues : List Core.Value}
    {environment finalEnvironment : Core.Environment} {initial allocated final : Core.Store}
    (cells : ParameterCells types values environment initial finalEnvironment allocated)
    {start : Nat} {mapping : Core.Renaming}
    (argument : environment[mapping start]? = some (bundleValues allValues))
    (selected : ∀ index value, values[index]? = some value → allValues[start + index]? = some value)
    {body : Core.Expr} {result : Core.Value}
    (evaluated : Core.Evaluates finalEnvironment allocated
      (body.rename (parameterRenaming types.length mapping)) result final) :
    Core.Evaluates environment initial
      ((parameterCode allValues.length start types body).rename mapping) result final := by
  induction cells generalizing start mapping with
  | nil => exact evaluated
  | @cons type types value values environment store finalEnvironment finalStore rest ih =>
      have initializer : Core.Evaluates environment store
          ((projectArgument start allValues.length (.var start)).rename mapping) value store := by
        rw [projectArgument_rename]
        exact projectArgument_evaluates (.var argument) (by simpa using selected 0 value rfl)
      simp only [parameterCode, List.zipIdx_cons, List.foldr_cons, Core.Expr.rename]
      apply Core.Evaluates.letE (.newCell (.inRight initializer))
      apply ih (start := start + 1) (mapping := mapping.lift)
      · exact argument
      · intro index selectedValue found
        simpa only [Nat.add_assoc, Nat.add_comm 1 index] using selected (index + 1) selectedValue found
      · exact evaluated

/-- Source argument binding and real Core allocation agree under an arbitrary
renaming of the enclosing globals. Each parameter adds the same binder on
both sides and lifts that renaming once. -/
theorem initialize_parameters_renamed {σ : Type} {arguments : List Arg} {types : List Core.Ty}
    {sources : List Semantics.Value} {targets : List Core.Value}
    (values : ValuesRel types sources targets) (arity : arguments.length = types.length)
    {sourceEnvironment : Semantics.Environment} {scope : Scope} {sourceState : Semantics.State σ}
    {world : World} {mapping : Core.Renaming} {environment : Core.Environment} {store : Core.Store}
    (environmentRelated : EnvironmentRel world sourceEnvironment scope mapping environment)
    (heapRelated : HeapRel world sourceState.heap store)
    {external : σ → Core.Store → Prop} (externalRelated : external sourceState.external store)
    (frame : ∀ state store type value, external state store →
      external state (store ++ [Core.Value.inRight type value])) :
    ∃ extension sourceEnvironment' sourceState' environment' store',
      Semantics.bindArguments arguments sources sourceEnvironment sourceState = some (sourceEnvironment', sourceState') ∧
      ParameterCells types targets environment store environment' store' ∧
      EnvironmentRel (world ++ extension) sourceEnvironment' (parameterScope arguments types scope)
        (parameterRenaming types.length mapping) environment' ∧
      HeapRel (world ++ extension) sourceState'.heap store' ∧
      external sourceState'.external store' := by
  induction values generalizing arguments sourceEnvironment scope sourceState world mapping environment store with
  | nil =>
      have empty : arguments = [] := List.eq_nil_of_length_eq_zero arity
      subst arguments
      exact ⟨[], sourceEnvironment, sourceState, environment, store, rfl, .nil,
        by simpa [parameterScope, parameterRenaming] using environmentRelated,
        by simpa using heapRelated, externalRelated⟩
  | @cons type types source sources target targets head tail ih =>
      cases arguments with
      | nil => simp at arity
      | cons argument arguments =>
          have arity' : arguments.length = types.length := Nat.succ.inj arity
          have entry : (world ++ [(type, store.length)])[sourceState.heap.length]? = some (type, store.length) := by
            rw [← heapRelated.length_eq, List.getElem?_concat_length]
          have environment' := ((environmentRelated.extendWorld [(type, store.length)]).addLocal
            argument.name type sourceState.heap.length store.length entry)
          have heap' := heapRelated.allocate head
          have external' := frame sourceState.external store .unit target externalRelated
          obtain ⟨extension, sourceEnvironment', sourceState', environment'', store', bound,
            allocated, locals, heap, external⟩ := ih arity'
              (sourceState := (Semantics.allocate sourceState source).2)
              (sourceEnvironment := (argument.name, sourceState.heap.length) :: sourceEnvironment)
              (scope := scope.addLocal argument.name type)
              (world := world ++ [(type, store.length)])
              (mapping := mapping.lift)
              (environment := .cellRef (Core.OptionalCell.cellType type) store.length :: environment)
              (store := store ++ [.inRight .unit target]) environment'
              (by simpa only [Semantics.allocate] using heap')
              (by simpa only [Semantics.allocate] using external')
          refine ⟨[(type, store.length)] ++ extension, sourceEnvironment', sourceState', environment'', store',
            ?_, .cons allocated, ?_, ?_, external⟩
          · exact bound
          · simpa only [List.append_assoc, parameterScope, List.zip_cons_cons, List.foldl_cons,
              List.length_cons, parameterRenaming] using locals
          · simpa only [List.append_assoc] using heap

end Solcore.Frontend.RustHull.Correspondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.GlobalFunctionCorrespondence
/-! The allocation and installation folds used by assemble for arbitrary
function lists. Installed closures retain the administrative Unit binders
introduced by earlier stores; their bodies and environments are shifted
together. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.Correspondence

def globalAllocation (signatures : List Signature) (body : Core.Expr) : Core.Expr :=
  signatures.foldr (fun signature next =>
    .letE (Core.OptionalCell.allocate signature.functionType) next) body

def globalEnvironment : List Signature → Nat → Core.Environment → Core.Environment
  | [], _, environment => environment
  | signature :: rest, location, environment =>
      globalEnvironment rest (location + 1)
        (.cellRef (Core.OptionalCell.cellType signature.functionType) location :: environment)

def globalStore (signatures : List Signature) (store : Core.Store) : Core.Store :=
  store ++ signatures.map (fun signature => .inLeft signature.functionType .unit)

theorem globalAllocation_evaluates {signatures : List Signature} {body : Core.Expr}
    {environment : Core.Environment} {initial final : Core.Store} {result : Core.Value}
    (evaluated : Core.Evaluates (globalEnvironment signatures initial.length environment)
      (globalStore signatures initial) body result final) :
    Core.Evaluates environment initial (globalAllocation signatures body) result final := by
  induction signatures generalizing environment initial with
  | nil => simpa [globalAllocation, globalEnvironment, globalStore] using evaluated
  | cons signature rest ih =>
      apply Core.Evaluates.letE (Core.OptionalCell.allocate_evaluates _ _ _)
      apply ih
      simpa [globalEnvironment, globalStore, List.append_assoc] using evaluated

theorem globalEnvironment_eq (signatures : List Signature) (base : Nat)
    (environment : Core.Environment) :
    globalEnvironment signatures base environment =
      ((signatures.zipIdx base).map (fun (signature, location) =>
        Core.Value.cellRef (Core.OptionalCell.cellType signature.functionType) location)).reverse ++ environment := by
  induction signatures generalizing base environment with
  | nil => rfl
  | cons signature rest ih =>
      simp [globalEnvironment, List.zipIdx_cons, ih, List.append_assoc]

/-- Every declared function receives a fresh cell, and globals appear in the
reverse order used by the actual compiler's lexical scope. -/
theorem globalEnvironment_lookup {signatures : List Signature} {index : Nat} {own : Signature}
    (found : signatures.reverse[index]? = some own) (base : Nat) (environment : Core.Environment) :
    (globalEnvironment signatures base environment)[index]? =
      some (.cellRef (Core.OptionalCell.cellType own.functionType)
        (base + (signatures.length - 1 - index))) := by
  have bound : index < signatures.length := by
    have := (List.getElem?_eq_some_iff.mp found).1
    simpa using this
  rw [globalEnvironment_eq, List.getElem?_append_left (by simpa using bound)]
  rw [List.getElem?_reverse (by simpa using bound), List.getElem?_map, List.getElem?_zipIdx]
  rw [List.getElem?_reverse bound] at found
  simp only [List.length_map, List.length_zipIdx, found, Option.map_some]

theorem globalStore_lookup {signatures : List Signature} {index : Nat} {own : Signature}
    (found : signatures.reverse[index]? = some own) (store : Core.Store) :
    (globalStore signatures store).read? (store.length + (signatures.length - 1 - index)) =
      some (.inLeft own.functionType .unit) := by
  have bound : index < signatures.length := by
    have := (List.getElem?_eq_some_iff.mp found).1
    simpa using this
  rw [List.getElem?_reverse bound] at found
  simp [globalStore, Core.Store.read?, List.getElem?_append_right, found]

structure GlobalCode where
  own : Signature
  body : Core.Expr

def GlobalCode.expression (code : GlobalCode) : Core.Expr :=
  .lambda (bundleType code.own.parameters) (Core.LanguageResult.resultType code.own.result) code.body

def globalShift (offsetCount : Nat) : Core.Renaming := fun index => offsetCount + index

def installationEnvironment (environment : Core.Environment) (offsetCount : Nat) : Core.Environment :=
  List.replicate offsetCount .unit ++ environment

def GlobalCode.installedValue (code : GlobalCode) (environment : Core.Environment) (offsetCount : Nat) : Core.Value :=
  .inRight .unit (.closure (bundleType code.own.parameters)
    (Core.LanguageResult.resultType code.own.result) (code.body.rename (globalShift offsetCount).lift)
    (installationEnvironment environment offsetCount))

def globalInstallation (codes : List GlobalCode) (start : Nat) (body : Core.Expr) : Core.Expr :=
  (codes.zipIdx start).foldr (fun (code, index) next =>
    .letE (.storeCell (.var index) (.inRight .unit code.expression)) (next.weakenAt 0)) body

def installationStore (locations : Nat → Nat) (environment : Core.Environment) :
    List GlobalCode → Nat → Nat → Core.Store → Core.Store
  | [], _, _, store => store
  | code :: rest, start, offsetCount, store =>
      installationStore locations environment rest (start + 1) (offsetCount + 1)
        (store.set (locations start) (code.installedValue environment offsetCount))

@[simp] theorem installationStore_length (locations : Nat → Nat) (environment : Core.Environment)
    (codes : List GlobalCode) (start offsetCount : Nat) (store : Core.Store) :
    (installationStore locations environment codes start offsetCount store).length = store.length := by
  induction codes generalizing start offsetCount store with
  | nil => rfl
  | cons code rest ih => simp [installationStore, ih]

theorem installationStore_preserves {locations : Nat → Nat} {environment : Core.Environment}
    {codes : List GlobalCode} {start offsetCount location : Nat} {store : Core.Store}
    (untouched : ∀ index, index < codes.length → locations (start + index) ≠ location) :
    (installationStore locations environment codes start offsetCount store).read? location = store.read? location := by
  induction codes generalizing start offsetCount store with
  | nil => rfl
  | cons code rest ih =>
      rw [installationStore, ih]
      · exact List.getElem?_set_ne (by simpa using untouched 0 (by simp))
      · intro index bound
        simpa only [Nat.add_assoc, Nat.add_comm 1 index] using untouched (index + 1) (by simpa using bound)

/-- All installed cells retain the exact closure body and capture environment
after the remaining registrations. Later installations cannot overwrite it. -/
theorem installationStore_lookup {locations : Nat → Nat} {environment : Core.Environment}
    {codes : List GlobalCode} {start offsetCount index : Nat} {code : GlobalCode} {store : Core.Store}
    (found : codes[index]? = some code)
    (bounded : ∀ offset, offset < codes.length → locations (start + offset) < store.length)
    (distinct : ∀ left right, left < codes.length → right < codes.length →
      locations (start + left) = locations (start + right) → left = right) :
    (installationStore locations environment codes start offsetCount store).read? (locations (start + index)) =
      some (code.installedValue environment (offsetCount + index)) := by
  induction codes generalizing start offsetCount index store with
  | nil => simp at found
  | cons head rest ih =>
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at found
          subst head
          rw [installationStore, installationStore_preserves]
          · simpa only [Nat.add_zero, Core.Store.read?] using
              List.getElem?_set_self (l := store) (a := code.installedValue environment offsetCount)
                (by simpa using bounded 0 (by simp))
          · intro offset bound
            intro same
            have impossible := distinct (offset + 1) 0 (by simpa using bound) (by simp)
              (by simpa [Nat.add_assoc, Nat.add_comm 1 offset] using same)
            omega
      | succ index =>
          simp only [List.getElem?_cons_succ] at found
          rw [installationStore]
          have result := ih (start := start + 1) (offsetCount := offsetCount + 1)
            (store := store.set (locations start) (head.installedValue environment offsetCount)) found
            (fun offset bound => by
              simpa only [List.length_set, Nat.add_assoc, Nat.add_comm 1 offset] using
                bounded (offset + 1) (by simpa using bound))
            (fun left right leftBound rightBound equal => by
              have same := distinct (left + 1) (right + 1) (by simpa using leftBound)
                (by simpa using rightBound) (by simpa [Nat.add_assoc, Nat.add_comm 1] using equal)
              omega)
          simpa only [Nat.add_assoc, Nat.add_comm 1 index] using result

theorem installationEnvironment_succ (environment : Core.Environment) (offsetCount : Nat) :
    installationEnvironment environment (offsetCount + 1) =
      .unit :: installationEnvironment environment offsetCount := by
  simp [installationEnvironment, List.replicate_succ]

theorem installationEnvironment_lookup {environment : Core.Environment} {index : Nat} {value : Core.Value}
    (found : environment[index]? = some value) (offsetCount : Nat) :
    (installationEnvironment environment offsetCount)[globalShift offsetCount index]? = some value := by
  simp [installationEnvironment, globalShift, List.getElem?_append_right, found]

theorem globalShift_succ (offsetCount : Nat) :
    Core.Renaming.comp (Core.Renaming.insertion 0) (globalShift offsetCount) =
      globalShift (offsetCount + 1) := by
  funext index
  simp [Core.Renaming.comp, Core.Renaming.insertion, globalShift, Nat.add_assoc, Nat.add_comm 1 index]

theorem weaken_globalShift (expression : Core.Expr) (offsetCount : Nat) :
    (expression.weakenAt 0).rename (globalShift offsetCount).lift =
      expression.rename (globalShift (offsetCount + 1)) := by
  rw [← Core.Expr.rename_insertion, Core.Expr.rename_comp,
    Core.Renaming.lift_comp_insertion_zero, globalShift_succ]

/-- Execute every store in the compiler's installation fold, then the real
continuation. The store and all captured environments are computed from the
actual global references supplied by allocation. -/
theorem globalInstallation_evaluates {codes : List GlobalCode} {start offsetCount : Nat}
    {locations : Nat → Nat} {environment : Core.Environment} {store final : Core.Store}
    (references : ∀ index code, codes[index]? = some code →
      environment[start + index]? =
        some (.cellRef (Core.OptionalCell.cellType code.own.functionType) (locations (start + index))))
    (bounded : ∀ index, index < codes.length → locations (start + index) < store.length)
    {body : Core.Expr} {result : Core.Value}
    (evaluated : Core.Evaluates (installationEnvironment environment (offsetCount + codes.length))
      (installationStore locations environment codes start offsetCount store)
      (body.rename (globalShift (offsetCount + codes.length))) result final) :
    Core.Evaluates (installationEnvironment environment offsetCount) store
      ((globalInstallation codes start body).rename (globalShift offsetCount)) result final := by
  induction codes generalizing start offsetCount store with
  | nil => simpa [globalInstallation, installationStore] using evaluated
  | cons code rest ih =>
      have locationBound : locations start < store.length := by simpa using bounded 0 (by simp)
      have reference : environment[start]? =
          some (.cellRef (Core.OptionalCell.cellType code.own.functionType) (locations start)) := by
        simpa using references 0 code rfl
      have stored : Core.Evaluates (installationEnvironment environment offsetCount) store
          (.storeCell (.var (globalShift offsetCount start))
            (.inRight .unit (code.expression.rename (globalShift offsetCount)))) .unit
          (store.set (locations start) (code.installedValue environment offsetCount)) := by
        apply Core.Evaluates.storeCell
          (.var (installationEnvironment_lookup reference offsetCount))
          (show store.read? (locations start) = some store[locations start] from
            List.getElem?_eq_getElem locationBound)
          (.inRight .lambda)
        simp only [Core.Store.write?, locationBound, ↓reduceIte]
        rfl
      simp only [globalInstallation, List.zipIdx_cons, List.foldr_cons, Core.Expr.rename]
      apply Core.Evaluates.letE stored
      change Core.Evaluates (.unit :: installationEnvironment environment offsetCount)
        (store.set (locations start) (code.installedValue environment offsetCount))
        (((globalInstallation rest (start + 1) body).weakenAt 0).rename
          (globalShift offsetCount).lift) result final
      rw [weaken_globalShift, ← installationEnvironment_succ]
      apply ih
      · intro index tail found
        simpa only [Nat.add_assoc, Nat.add_comm 1 index] using references (index + 1) tail found
      · intro index bound
        simpa only [List.length_set, Nat.add_assoc, Nat.add_comm 1 index] using
          bounded (index + 1) (by simpa using bound)
      · simpa only [installationStore, List.length_cons, Nat.add_assoc,
          Nat.add_comm 1 rest.length] using evaluated

theorem globalInstallation_eq (codes : List GlobalCode) (start : Nat) (body : Core.Expr) :
    globalInstallation codes start body =
      ((codes.map GlobalCode.expression).zipIdx start).foldr (fun (closure, index) next =>
        .letE (.storeCell (.var index) (.inRight .unit closure)) (next.weakenAt 0)) body := by
  induction codes generalizing start with
  | nil => rfl
  | cons code rest ih =>
      simp only [globalInstallation, List.map_cons, List.zipIdx_cons, List.foldr_cons]
      rw [← ih]
      rfl

def CompiledGlobal (fuel : Nat) (signatures : List Signature) (scope : Scope)
    (item : Function × Signature) (code : GlobalCode) : Prop :=
  code.own = item.2 ∧ lowerFunction fuel signatures scope item.1 item.2 = .ok code.expression

inductive CompiledGlobals (fuel : Nat) (signatures : List Signature) (scope : Scope) :
    List (Function × Signature) → List GlobalCode → Prop where
  | nil : CompiledGlobals fuel signatures scope [] []
  | cons {item : Function × Signature} {code : GlobalCode}
      {items : List (Function × Signature)} {codes : List GlobalCode}
      (head : CompiledGlobal fuel signatures scope item code)
      (tail : CompiledGlobals fuel signatures scope items codes) :
      CompiledGlobals fuel signatures scope (item :: items) (code :: codes)

/-- Every accepted function lowerer produces a lambda, retaining its actual
parameter allocation and result wrapper inside the recorded body. -/
theorem lowerFunctions_codes {fuel : Nat} {signatures : List Signature} {scope : Scope}
    {items : List (Function × Signature)} {closures : List Core.Expr}
    (compiled : items.mapM (fun (function, own) =>
      lowerFunction fuel signatures scope function own) = .ok closures) :
    ∃ codes, closures = codes.map GlobalCode.expression ∧
      CompiledGlobals fuel signatures scope items codes := by
  induction items generalizing closures with
  | nil => cases compiled; exact ⟨[], rfl, .nil⟩
  | cons item rest ih =>
      simp only [List.mapM_cons] at compiled
      obtain ⟨closure, closureCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
      obtain ⟨tail, tailCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
      cases returned
      obtain ⟨codes, rfl, related⟩ := ih tailCompiled
      obtain ⟨statements, _, closureShape⟩ :=
        StatementCorrespondence.lowerFunction_components closureCompiled
      let code : GlobalCode := ⟨item.2,
        parameterCode item.2.parameters.length 0 item.2.parameters
          (StatementCorrespondence.finishedBody item.2.result statements)⟩
      have closureEqual : closure = code.expression := closureShape
      exact ⟨code :: codes, by simp only [List.map_cons, closureEqual],
        .cons ⟨rfl, closureEqual ▸ closureCompiled⟩ related⟩

def globalScope (signatures : List Signature) (runtime : Scope) : Scope :=
  (signatures.reverse.map fun signature =>
    ⟨some (Effects.slotName ("function$" ++ signature.name)), signature.functionType, true⟩) ++ runtime

def globalInvocation (own : Signature) (index globalCount runtimeCount : Nat) : Core.Expr :=
  Core.LanguageResult.bind own.result
    (Core.OptionalCell.read own.functionType (.var index) (Core.Word.ofNatModulo 1))
    (.apply (.var 0) (.var (globalCount + runtimeCount + 1)))

/-- Decompose the real assembler into the exact folds proved above. No
alternate allocation or installation path is substituted for its code. -/
theorem assemble_components {functions : List Function} {entry : String} {runtime : Scope}
    {fuel : Nat} {own : Signature} {allocated : Core.Expr}
    (compiled : assemble functions entry runtime fuel = .ok (own, allocated)) :
    ∃ signatures codes binding index,
      functions.mapM (signature fuel) = .ok signatures ∧
      signatures.find? (·.name == entry) = some own ∧
      CompiledGlobals fuel signatures (globalScope signatures runtime)
        (functions.zip signatures).reverse codes ∧
      (globalScope signatures runtime).lookup (Effects.slotName ("function$" ++ entry)) = .ok (binding, index) ∧
      allocated = globalAllocation signatures
        (globalInstallation codes 0 (globalInvocation own index signatures.length runtime.length)) := by
  by_cases unique : (functions.map (·.name)).eraseDups.length = functions.length
  · simp only [assemble, unique, ↓reduceIte] at compiled
    obtain ⟨signatures, signaturesCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
    cases selected : signatures.find? (·.name == entry) with
    | none => simp [selected, fail, Bind.bind, Except.bind] at compiled
    | some own' =>
        simp only [selected, Pure.pure, Except.pure, Bind.bind, Except.bind] at compiled
        obtain ⟨closures, closuresCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
        obtain ⟨⟨binding, index⟩, looked, returned⟩ := lower_bind_eq_ok.mp compiled
        cases returned
        obtain ⟨codes, rfl, codesCompiled⟩ := lowerFunctions_codes closuresCompiled
        refine ⟨signatures, codes, binding, index, signaturesCompiled, selected, codesCompiled, looked, ?_⟩
        simp only [globalAllocation, globalInstallation_eq, globalInvocation, List.length_reverse]
  · simp [assemble, unique, fail, Bind.bind, Except.bind] at compiled

/-- Exact installed-closure lookup invariant. The environment here is the
global reference environment before the store-result Unit binders are added. -/
def InstalledGlobals (codes : List GlobalCode) (locations : Nat → Nat)
    (environment : Core.Environment) (store : Core.Store) : Prop :=
  ∀ index code, codes[index]? = some code →
    store.read? (locations index) = some (code.installedValue environment index)

theorem InstalledGlobals.append {codes : List GlobalCode} {locations : Nat → Nat}
    {environment : Core.Environment} {store : Core.Store}
    (installed : InstalledGlobals codes locations environment store) (suffix : Core.Store) :
    InstalledGlobals codes locations environment (store ++ suffix) := by
  intro index code found
  have looked := installed index code found
  have bound := (List.getElem?_eq_some_iff.mp looked).1
  simpa only [Core.Store.read?, List.getElem?_append_left bound] using looked

/-- Source values have no function-closure constructor. Consequently a source
local cell cannot alias an installed global function cell. -/
theorem ValueRel.not_closure {type : Core.Ty} {source : Semantics.Value}
    {parameterType resultType : Core.Ty} {body : Core.Expr} {environment : Core.Environment} :
    ¬ ValueRel type source (.closure parameterType resultType body environment) := by
  intro related
  cases related

theorem InstalledGlobals.write {codes : List GlobalCode} {locations : Nat → Nat}
    {environment : Core.Environment} {store updated : Core.Store}
    (installed : InstalledGlobals codes locations environment store)
    {world : World} {source : Semantics.Heap} (heap : HeapRel world source store)
    {index : Nat} {type : Core.Ty} {location : Nat} {value : Core.Value}
    (entry : world[index]? = some (type, location))
    (written : store.write? location value = some updated) :
    InstalledGlobals codes locations environment updated := by
  intro globalIndex code found
  have looked := installed globalIndex code found
  have different : locations globalIndex ≠ location := by
    intro sameLocation
    obtain ⟨sourceValue, targetValue, _, sourceRead, related⟩ := heap.cell index type location entry
    rw [sameLocation] at looked
    have sameValue := Option.some.inj (sourceRead.symm.trans looked)
    change Core.Value.inRight .unit targetValue =
      .inRight .unit (.closure (bundleType code.own.parameters)
        (Core.LanguageResult.resultType code.own.result)
        (code.body.rename (globalShift globalIndex).lift)
        (installationEnvironment environment globalIndex)) at sameValue
    cases sameValue
    exact ValueRel.not_closure related
  rw [Core.Store.write?_preserves_other written different]
  exact looked

theorem InstalledGlobals.externalFrame {σ : Type} (codes : List GlobalCode)
    (locations : Nat → Nat) (environment : Core.Environment) :
    StatementCorrespondence.ExternalFrame
      (fun (_ : σ) store => InstalledGlobals codes locations environment store) where
  allocate := fun installed => installed.append _
  write := fun installed heap entry written => installed.write heap entry written

theorem InstalledGlobals.of_installation {codes : List GlobalCode} {locations : Nat → Nat}
    {environment : Core.Environment} {store : Core.Store}
    (bounded : ∀ index, index < codes.length → locations index < store.length)
    (distinct : ∀ left right, left < codes.length → right < codes.length →
      locations left = locations right → left = right) :
    InstalledGlobals codes locations environment
      (installationStore locations environment codes 0 0 store) := by
  intro index code found
  simpa only [Nat.zero_add] using installationStore_lookup found
    (start := 0) (offsetCount := 0) (store := store)
    (by simpa only [Nat.zero_add] using bounded)
    (by simpa only [Nat.zero_add] using distinct)

theorem CompiledGlobals.signatures {fuel : Nat} {signatures : List Signature} {scope : Scope}
    {items : List (Function × Signature)} {codes : List GlobalCode}
    (compiled : CompiledGlobals fuel signatures scope items codes) :
    codes.map GlobalCode.own = items.map Prod.snd := by
  induction compiled with
  | nil => rfl
  | cons head _ ih => simp only [List.map_cons, head.1, ih]

theorem signatures_length {fuel : Nat} {functions : List Function} {signatures : List Signature}
    (compiled : functions.mapM (signature fuel) = .ok signatures) :
    functions.length = signatures.length := by
  induction functions generalizing signatures with
  | nil => cases compiled; rfl
  | cons function rest ih =>
      simp only [List.mapM_cons] at compiled
      obtain ⟨_, _, compiled⟩ := lower_bind_eq_ok.mp compiled
      obtain ⟨tail, tailCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
      cases returned
      exact congrArg Nat.succ (ih tailCompiled)

/-- The signatures retained by accepted closures are exactly the reversed
declaration signatures used by global scope and allocation. -/
theorem CompiledGlobals.aligned {fuel : Nat} {functions : List Function}
    {signatures : List Signature} {scope : Scope} {codes : List GlobalCode}
    (signaturesCompiled : functions.mapM (signature fuel) = .ok signatures)
    (compiled : CompiledGlobals fuel signatures scope (functions.zip signatures).reverse codes) :
    codes.map GlobalCode.own = signatures.reverse := by
  rw [compiled.signatures, List.map_reverse,
    List.map_snd_zip (Nat.le_of_eq (signatures_length signaturesCompiled).symm)]

/-- Global lexical bindings retain their actual internal names and cell
locations while source locals and administrative binders are added. -/
def GlobalEnvironmentRel (codes : List GlobalCode) (locations : Nat → Nat)
    (scope : Scope) (mapping : Core.Renaming) (environment : Core.Environment) : Prop :=
  ∀ index code, codes[index]? = some code → ∃ slot,
    scope.lookup (Effects.slotName ("function$" ++ code.own.name)) =
      .ok (⟨some (Effects.slotName ("function$" ++ code.own.name)), code.own.functionType, true⟩, slot) ∧
    environment[mapping slot]? = some (.cellRef (Core.OptionalCell.cellType code.own.functionType) (locations index))

theorem GlobalEnvironmentRel.lookup {codes : List GlobalCode} {locations : Nat → Nat}
    {scope : Scope} {mapping : Core.Renaming} {environment : Core.Environment}
    (related : GlobalEnvironmentRel codes locations scope mapping environment)
    {index : Nat} {code : GlobalCode} (found : codes[index]? = some code)
    {binding : Binding} {slot : Nat}
    (looked : scope.lookup (Effects.slotName ("function$" ++ code.own.name)) = .ok (binding, slot)) :
    binding.type = code.own.functionType ∧ binding.reference = true ∧
    environment[mapping slot]? = some (.cellRef (Core.OptionalCell.cellType code.own.functionType) (locations index)) := by
  obtain ⟨actualSlot, actual, reference⟩ := related index code found
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj (looked.symm.trans actual))
  exact ⟨rfl, rfl, reference⟩

theorem GlobalEnvironmentRel.temporary {codes : List GlobalCode} {locations : Nat → Nat}
    {scope : Scope} {mapping : Core.Renaming} {environment : Core.Environment}
    (related : GlobalEnvironmentRel codes locations scope mapping environment)
    (type : Core.Ty) (value : Core.Value) :
    GlobalEnvironmentRel codes locations (scope.temporary type) mapping.lift (value :: environment) := by
  intro index code found
  obtain ⟨slot, looked, reference⟩ := related index code found
  refine ⟨slot + 1, ?_, reference⟩
  simp [Scope.temporary, scope_lookup_cons, looked]

theorem slotName_reserved (name : String) :
    (Effects.slotName name).startsWith Effects.reservedPrefix = true := by
  simp [Effects.slotName, String.startsWith_string_iff]

theorem GlobalEnvironmentRel.addLocal {codes : List GlobalCode} {locations : Nat → Nat}
    {scope : Scope} {mapping : Core.Renaming} {environment : Core.Environment}
    (related : GlobalEnvironmentRel codes locations scope mapping environment)
    (name : String) (type : Core.Ty) (value : Core.Value)
    (allowed : name.startsWith Effects.reservedPrefix = false) :
    GlobalEnvironmentRel codes locations (scope.addLocal name type) mapping.lift (value :: environment) := by
  intro index code found
  obtain ⟨slot, looked, reference⟩ := related index code found
  have different : name ≠ Effects.slotName ("function$" ++ code.own.name) := by
    intro same
    have reserved := slotName_reserved ("function$" ++ code.own.name)
    rw [← same, allowed] at reserved
    contradiction
  refine ⟨slot + 1, ?_, reference⟩
  simp [Scope.addLocal, scope_lookup_cons, different, looked]

theorem GlobalEnvironmentRel.prepend {codes : List GlobalCode} {locations : Nat → Nat}
    {scope : Scope} {mapping : Core.Renaming} {environment : Core.Environment}
    (related : GlobalEnvironmentRel codes locations scope mapping environment)
    (extra : Core.Environment) :
    GlobalEnvironmentRel codes locations scope (fun index => extra.length + mapping index) (extra ++ environment) := by
  intro index code found
  obtain ⟨slot, looked, reference⟩ := related index code found
  refine ⟨slot, looked, ?_⟩
  simpa only [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left] using reference

def globalLocations (signatures : List Signature) (base : Nat) : Nat → Nat :=
  fun index => base + (signatures.length - 1 - index)

theorem GlobalEnvironmentRel.of_lookup {signatures : List Signature} {codes : List GlobalCode}
    (aligned : codes.map GlobalCode.own = signatures.reverse) {scope : Scope}
    (looked : ∀ index code, codes[index]? = some code →
      scope.lookup (Effects.slotName ("function$" ++ code.own.name)) =
        .ok (⟨some (Effects.slotName ("function$" ++ code.own.name)), code.own.functionType, true⟩, index))
    (base : Nat) (environment : Core.Environment) :
    GlobalEnvironmentRel codes (globalLocations signatures base) scope Core.Renaming.id
      (globalEnvironment signatures base environment) := by
  intro index code found
  refine ⟨index, looked index code found, ?_⟩
  apply globalEnvironment_lookup
  simp only [Core.Renaming.id, ← aligned, List.getElem?_map, found, Option.map_some]

theorem ParameterCells.globalEnvironment {types : List Core.Ty} {values : List Core.Value}
    {environment finalEnvironment : Core.Environment} {store finalStore : Core.Store}
    (cells : ParameterCells types values environment store finalEnvironment finalStore)
    {arguments : List Arg} (arity : arguments.length = types.length)
    (allowed : ∀ argument ∈ arguments, argument.name.startsWith Effects.reservedPrefix = false)
    {codes : List GlobalCode} {locations : Nat → Nat} {scope : Scope} {mapping : Core.Renaming}
    (related : GlobalEnvironmentRel codes locations scope mapping environment) :
    GlobalEnvironmentRel codes locations (parameterScope arguments types scope)
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

theorem aligned_length {signatures : List Signature} {codes : List GlobalCode}
    (aligned : codes.map GlobalCode.own = signatures.reverse) : codes.length = signatures.length := by
  simpa only [List.length_map, List.length_reverse] using congrArg List.length aligned

theorem globalLocations_bounded {signatures : List Signature} {codes : List GlobalCode}
    (aligned : codes.map GlobalCode.own = signatures.reverse) (store : Core.Store)
    {index : Nat} (bound : index < codes.length) :
    globalLocations signatures store.length index < (globalStore signatures store).length := by
  have length := aligned_length aligned
  simp only [globalLocations, globalStore, List.length_append, List.length_map]
  omega

theorem globalLocations_distinct {signatures : List Signature} {codes : List GlobalCode}
    (aligned : codes.map GlobalCode.own = signatures.reverse) (base : Nat)
    {left right : Nat} (leftBound : left < codes.length) (rightBound : right < codes.length)
    (same : globalLocations signatures base left = globalLocations signatures base right) : left = right := by
  have length := aligned_length aligned
  simp only [globalLocations] at same
  omega

def initializedGlobals (signatures : List Signature) (codes : List GlobalCode)
    (environment : Core.Environment) (store : Core.Store) : Core.Store :=
  installationStore (globalLocations signatures store.length)
    (globalEnvironment signatures store.length environment) codes 0 0 (globalStore signatures store)

theorem InstalledGlobals.initialize {signatures : List Signature} {codes : List GlobalCode}
    (aligned : codes.map GlobalCode.own = signatures.reverse)
    (environment : Core.Environment) (store : Core.Store) :
    InstalledGlobals codes (globalLocations signatures store.length)
      (globalEnvironment signatures store.length environment)
      (initializedGlobals signatures codes environment store) := by
  apply InstalledGlobals.of_installation
  · intro index bound
    exact globalLocations_bounded aligned store bound
  · intro left right leftBound rightBound same
    exact globalLocations_distinct aligned store.length leftBound rightBound same

theorem HeapRel.initializeGlobals {world : World} {source : Semantics.Heap} {store : Core.Store}
    (related : HeapRel world source store) (signatures : List Signature) (codes : List GlobalCode)
    (environment : Core.Environment) :
    HeapRel world source (initializedGlobals signatures codes environment store) where
  length_eq := related.length_eq
  distinct := related.distinct
  cell := by
    intro index type location entry
    obtain ⟨sourceValue, targetValue, found, read, valueRelated⟩ := related.cell index type location entry
    refine ⟨sourceValue, targetValue, found, ?_, valueRelated⟩
    have bound := related.location_bound entry
    rw [initializedGlobals, installationStore_preserves]
    · simpa only [globalStore, Core.Store.read?, List.getElem?_append_left bound] using read
    · intro offset _
      simp only [globalLocations]
      omega

/-- Execute allocation and installation from an arbitrary real caller store.
The continuation receives exactly the registered closure invariant above. -/
theorem globalInitialization_evaluates {signatures : List Signature} {codes : List GlobalCode}
    (aligned : codes.map GlobalCode.own = signatures.reverse)
    {environment : Core.Environment} {initial final : Core.Store} {body : Core.Expr} {result : Core.Value}
    (evaluated : Core.Evaluates
      (installationEnvironment (globalEnvironment signatures initial.length environment) codes.length)
      (initializedGlobals signatures codes environment initial)
      (body.rename (globalShift codes.length)) result final) :
    Core.Evaluates environment initial
      (globalAllocation signatures (globalInstallation codes 0 body)) result final := by
  apply globalAllocation_evaluates
  have references : ∀ index code, codes[index]? = some code →
      (globalEnvironment signatures initial.length environment)[0 + index]? =
        some (.cellRef (Core.OptionalCell.cellType code.own.functionType)
          (globalLocations signatures initial.length (0 + index))) := by
    intro index code found
    apply globalEnvironment_lookup
    simp only [Nat.zero_add, ← aligned, List.getElem?_map, found, Option.map_some]
  have executed := globalInstallation_evaluates (start := 0) (offsetCount := 0)
    (store := globalStore signatures initial) (body := body) (result := result) (final := final) references
    (fun index bound => by simpa only [Nat.zero_add] using
      globalLocations_bounded aligned initial (index := index) bound)
    (by simpa only [Nat.zero_add, initializedGlobals] using evaluated)
  have zero : globalShift 0 = Core.Renaming.id := by funext index; simp [globalShift, Core.Renaming.id]
  simpa only [zero, Core.Expr.rename_id, installationEnvironment, List.replicate_zero,
    List.nil_append] using executed

end Solcore.Frontend.RustHull.Correspondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ClosureFrameCorrespondence
/-! Installed function and loop closures survive source computation. Source
locals cannot contain closures, so their writes cannot alias these cells. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.Correspondence

def ClosuresPreserved (initial final : Core.Store) : Prop :=
  ∀ {location parameter result body environment},
    initial.read? location = some (.inRight .unit (.closure parameter result body environment)) →
    final.read? location = some (.inRight .unit (.closure parameter result body environment))

theorem ClosuresPreserved.refl (store : Core.Store) : ClosuresPreserved store store :=
  fun found => found

theorem ClosuresPreserved.trans {first middle last : Core.Store}
    (firstStep : ClosuresPreserved first middle) (secondStep : ClosuresPreserved middle last) :
    ClosuresPreserved first last := fun found => secondStep (firstStep found)

theorem ClosuresPreserved.append (store suffix : Core.Store) :
    ClosuresPreserved store (store ++ suffix) := by
  intro location parameter result body environment found
  have bound := (List.getElem?_eq_some_iff.mp found).1
  simpa only [Core.Store.read?, List.getElem?_append_left bound] using found

theorem ClosuresPreserved.write {store updated : Core.Store}
    {world : World} {source : Semantics.Heap} (heap : HeapRel world source store)
    {index : Nat} {type : Core.Ty} {location : Nat} {value : Core.Value}
    (entry : world[index]? = some (type, location))
    (written : store.write? location value = some updated) :
    ClosuresPreserved store updated := by
  intro retainedLocation parameter result body environment found
  have different : retainedLocation ≠ location := by
    intro same
    obtain ⟨sourceValue, targetValue, _, read, related⟩ := heap.cell index type location entry
    rw [same] at found
    have equal := Option.some.inj (read.symm.trans found)
    cases equal
    exact ValueRel.not_closure related
  rw [Core.Store.write?_preserves_other written different]
  exact found

theorem InstalledGlobals.preserved {codes : List GlobalCode} {locations : Nat → Nat}
    {environment : Core.Environment} {initial final : Core.Store}
    (installed : InstalledGlobals codes locations environment initial)
    (preserved : ClosuresPreserved initial final) :
    InstalledGlobals codes locations environment final := by
  intro index code found
  exact preserved (installed index code found)

end Solcore.Frontend.RustHull.Correspondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ProgramSelectionCorrespondence
/-! Function names, signatures and installed-code indices are selected by the
actual assembler. These facts connect that selection to independent source
function lookup, including the compiler's reverse global-scope order. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.Correspondence

inductive CompiledSignatures (fuel : Nat) : List Function → List Signature → Prop where
  | nil : CompiledSignatures fuel [] []
  | cons {function : Function} {own : Signature} {functions : List Function} {signatures : List Signature}
      (head : signature fuel function = .ok own)
      (tail : CompiledSignatures fuel functions signatures) :
      CompiledSignatures fuel (function :: functions) (own :: signatures)

theorem compiledSignatures {fuel : Nat} {functions : List Function} {signatures : List Signature}
    (compiled : functions.mapM (signature fuel) = .ok signatures) :
    CompiledSignatures fuel functions signatures := by
  induction functions generalizing signatures with
  | nil => cases compiled; exact .nil
  | cons function functions ih =>
      simp only [List.mapM_cons] at compiled
      obtain ⟨own, head, compiled⟩ := lower_bind_eq_ok.mp compiled
      obtain ⟨rest, tail, returned⟩ := lower_bind_eq_ok.mp compiled
      cases returned
      exact .cons head (ih tail)

theorem CompiledSignatures.names {fuel : Nat} {functions : List Function} {signatures : List Signature}
    (compiled : CompiledSignatures fuel functions signatures) :
    signatures.map (·.name) = functions.map (·.name) := by
  induction compiled with
  | nil => rfl
  | cons head tail ih => simp only [List.map_cons, signature_name head, ih]

theorem CompiledSignatures.length {fuel : Nat} {functions : List Function} {signatures : List Signature}
    (compiled : CompiledSignatures fuel functions signatures) : signatures.length = functions.length := by
  simpa only [List.length_map] using congrArg List.length compiled.names

theorem CompiledSignatures.selected {fuel : Nat} {functions : List Function} {signatures : List Signature}
    (compiled : CompiledSignatures fuel functions signatures) {entry : String} {own : Signature}
    (selected : signatures.find? (·.name == entry) = some own) :
    ∃ function, functions.find? (·.name == entry) = some function ∧ signature fuel function = .ok own := by
  induction compiled with
  | nil => simp at selected
  | @cons function own' functions signatures head tail ih =>
      by_cases matched : own'.name == entry
      · simp only [List.find?_cons, matched, Option.some.injEq] at selected
        subst own
        exact ⟨function, by simp only [List.find?_cons, ← signature_name head, matched], head⟩
      · simp only [List.find?_cons, matched] at selected
        obtain ⟨selectedFunction, found, accepted⟩ := ih selected
        exact ⟨selectedFunction, by simpa only [List.find?_cons, ← signature_name head, matched] using found, accepted⟩

private theorem eraseDups_length_le (names : List String) : names.eraseDups.length ≤ names.length := by
  cases names with
  | nil => simp
  | cons name rest =>
      rw [List.eraseDups_cons]
      simp only [List.length_cons]
      exact Nat.succ_le_succ (Nat.le_trans (eraseDups_length_le (rest.filter fun other => !other == name))
        (List.length_filter_le _ _))
termination_by names.length
decreasing_by exact Nat.lt_succ_of_le (List.length_filter_le _ _)

theorem names_unique_of_checked {names : List String} (checked : names.eraseDups.length = names.length) :
    names.Nodup := by
  induction names with
  | nil => exact .nil
  | cons name rest ih =>
      rw [List.eraseDups_cons] at checked
      have deduplicated := eraseDups_length_le (rest.filter fun other => !other == name)
      have filtered := List.length_filter_le (fun other => !other == name) rest
      have sameLength : (rest.filter fun other => !other == name).length = rest.length := by
        simp only [List.length_cons] at checked
        omega
      have allDifferent := List.length_filter_eq_length_iff.mp sameLength
      have same : rest.filter (fun other => !other == name) = rest := List.filter_eq_self.mpr allDifferent
      rw [same] at checked
      apply List.nodup_cons.mpr
      constructor
      · intro member
        simpa using allDifferent name member
      · exact ih (Nat.succ.inj checked)

theorem assemble_names_unique {functions : List Function} {entry : String} {runtime : Scope}
    {fuel : Nat} {own : Signature} {allocated : Core.Expr}
    (compiled : assemble functions entry runtime fuel = .ok (own, allocated)) :
    (functions.map (·.name)).Nodup := by
  by_cases unique : (functions.map (·.name)).eraseDups.length = functions.length
  · exact names_unique_of_checked (by simpa only [List.length_map] using unique)
  · simp [assemble, unique, fail, Bind.bind, Except.bind] at compiled

def globalBinding (own : Signature) : Binding :=
  ⟨some (Effects.slotName ("function$" ++ own.name)), own.functionType, true⟩

theorem functionSlot_injective : Function.Injective (fun name => Effects.slotName ("function$" ++ name)) := by
  intro left right same
  simpa [Effects.slotName] using same

private theorem namedScope_lookup {signatures : List Signature} {own : Signature} {index : Nat}
    (unique : (signatures.map (·.name)).Nodup) (found : signatures[index]? = some own) (runtime : Scope) :
    Scope.lookup ((signatures.map globalBinding) ++ runtime) (Effects.slotName ("function$" ++ own.name)) =
      .ok (globalBinding own, index) := by
  induction signatures generalizing index with
  | nil => simp at found
  | cons head rest ih =>
      obtain ⟨absent, tailUnique⟩ := List.nodup_cons.mp unique
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at found
          subst head
          simp [globalBinding, scope_lookup_cons]
      | succ index =>
          simp only [List.getElem?_cons_succ] at found
          have different : head.name ≠ own.name := by
            intro same
            apply absent
            change head.name ∈ rest.map (·.name)
            rw [same]
            exact List.mem_map.mpr ⟨own, List.mem_of_getElem? found, rfl⟩
          have slotDifferent : Effects.slotName ("function$" ++ head.name) ≠
              Effects.slotName ("function$" ++ own.name) := fun same => different (functionSlot_injective same)
          simp only [List.map_cons, List.cons_append, scope_lookup_cons, globalBinding,
            Option.some_beq_some, beq_eq_false_iff_ne.mpr slotDifferent, Bool.false_eq_true, ↓reduceIte]
          rw [ih tailUnique found]
          rfl

/-- The actual reverse global scope finds every unique function at precisely
its installed-code index, even when a separate runtime scope follows it. -/
theorem globalScope_lookup {signatures : List Signature} {own : Signature} {index : Nat}
    (unique : (signatures.map (·.name)).Nodup)
    (found : signatures.reverse[index]? = some own) (runtime : Scope) :
    (globalScope signatures runtime).lookup (Effects.slotName ("function$" ++ own.name)) =
      .ok (globalBinding own, index) := by
  apply namedScope_lookup (runtime := runtime) _ found
  simpa only [List.map_reverse] using (List.reverse_perm (signatures.map (·.name))).nodup_iff.mpr unique

theorem CompiledSignatures.selected_pair {fuel : Nat} {functions : List Function} {signatures : List Signature}
    (compiled : CompiledSignatures fuel functions signatures) {entry : String} {own : Signature}
    (selected : signatures.find? (·.name == entry) = some own) :
    ∃ function, functions.find? (·.name == entry) = some function ∧
      signature fuel function = .ok own ∧ (function, own) ∈ functions.zip signatures := by
  induction compiled with
  | nil => simp at selected
  | @cons function own' functions signatures head tail ih =>
      by_cases matched : own'.name == entry
      · simp only [List.find?_cons, matched, Option.some.injEq] at selected
        subst own
        exact ⟨function, by simp only [List.find?_cons, ← signature_name head, matched],
          head, List.mem_cons_self ..⟩
      · simp only [List.find?_cons, matched] at selected
        obtain ⟨selectedFunction, found, accepted, member⟩ := ih selected
        exact ⟨selectedFunction, by simpa only [List.find?_cons, ← signature_name head, matched] using found,
          accepted, List.mem_cons_of_mem _ member⟩

theorem CompiledGlobals.get {fuel : Nat} {signatures : List Signature} {scope : Scope}
    {items : List (Function × Signature)} {codes : List GlobalCode}
    (compiled : CompiledGlobals fuel signatures scope items codes)
    {index : Nat} {item : Function × Signature} (found : items[index]? = some item) :
    ∃ code, codes[index]? = some code ∧ CompiledGlobal fuel signatures scope item code := by
  induction compiled generalizing index with
  | nil => simp at found
  | @cons headItem code items codes head tail ih =>
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at found
          subst item
          exact ⟨code, rfl, head⟩
      | succ index => exact ih found

/-- A source-level named call and signature lookup select the same actual
compiled closure. This applies to any function, not only the public entry. -/
theorem compiledFunction_selected {fuel : Nat} {functions : List Function}
    {signatures : List Signature} {scope : Scope} {codes : List GlobalCode}
    (signaturesCompiled : functions.mapM (signature fuel) = .ok signatures)
    (codesCompiled : CompiledGlobals fuel signatures scope (functions.zip signatures).reverse codes)
    {name : String} {function : Function} {own : Signature}
    (sourceSelected : functions.find? (·.name == name) = some function)
    (signatureSelected : signatures.find? (·.name == name) = some own) :
    signature fuel function = .ok own ∧ ∃ (index : Nat) (code : GlobalCode),
      codes[index]? = some code ∧ code.own = own ∧
      lowerFunction fuel signatures scope function own = .ok code.expression := by
  obtain ⟨selectedFunction, selected, signatureCompiled, member⟩ :=
    (compiledSignatures signaturesCompiled).selected_pair signatureSelected
  have same := Option.some.inj (sourceSelected.symm.trans selected)
  subst selectedFunction
  obtain ⟨index, itemFound⟩ := List.getElem?_of_mem (List.mem_reverse.mpr member)
  obtain ⟨code, found, ownEqual, functionCompiled⟩ := codesCompiled.get itemFound
  exact ⟨signatureCompiled, index, code, found, ownEqual, functionCompiled⟩

/-- The selected source function and installed closure are extracted from the
same accepted assembler run, with the real reverse installation index. -/
theorem assemble_selection {functions : List Function} {entry : String} {runtime : Scope}
    {fuel : Nat} {own : Signature} {allocated : Core.Expr}
    (accepted : assemble functions entry runtime fuel = .ok (own, allocated)) :
    ∃ signatures codes function code index,
      functions.mapM (signature fuel) = .ok signatures ∧
      functions.find? (·.name == entry) = some function ∧
      signature fuel function = .ok own ∧
      CompiledGlobals fuel signatures (globalScope signatures runtime)
        (functions.zip signatures).reverse codes ∧
      codes[index]? = some code ∧ code.own = own ∧
      lowerFunction fuel signatures (globalScope signatures runtime) function own = .ok code.expression ∧
      allocated = globalAllocation signatures
        (globalInstallation codes 0 (globalInvocation own index signatures.length runtime.length)) := by
  obtain ⟨signatures, codes, binding, selectedIndex, signaturesCompiled, selected,
    codesCompiled, looked, allocatedEqual⟩ := assemble_components accepted
  have signaturesRelated := compiledSignatures signaturesCompiled
  obtain ⟨function, functionSelected, signatureCompiled, member⟩ := signaturesRelated.selected_pair selected
  obtain ⟨index, itemFound⟩ := List.getElem?_of_mem (List.mem_reverse.mpr member)
  obtain ⟨code, codeFound, ownEqual, functionCompiled⟩ := codesCompiled.get itemFound
  have aligned := codesCompiled.aligned signaturesCompiled
  have signatureFound : signatures.reverse[index]? = some own := by
    rw [← aligned, List.getElem?_map, codeFound]
    exact congrArg some ownEqual
  have unique : (signatures.map (·.name)).Nodup := by
    rw [signaturesRelated.names]
    exact assemble_names_unique accepted
  have actualLookup := globalScope_lookup unique signatureFound runtime
  have ownName : own.name = entry := by simpa only [beq_iff_eq] using List.find?_some selected
  rw [ownName] at actualLookup
  obtain ⟨_, rfl⟩ := Prod.mk.inj (Except.ok.inj (looked.symm.trans actualLookup))
  exact ⟨signatures, codes, function, code, selectedIndex, signaturesCompiled, functionSelected,
    signatureCompiled, codesCompiled, codeFound, ownEqual, functionCompiled, allocatedEqual⟩

end Solcore.Frontend.RustHull.Correspondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.CompiledProgramLookup
/-! Name and code lookup for calls within one accepted compiled program.
Source selections determine actual signatures and installed closure indices;
the assembler's uniqueness check makes each such code choice unambiguous. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.Correspondence

theorem CompiledSignatures.source_selected {fuel : Nat} {functions : List Function}
    {signatures : List Signature} (compiled : CompiledSignatures fuel functions signatures)
    {name : String} {function : Function}
    (selected : functions.find? (·.name == name) = some function) :
    ∃ own, signatures.find? (·.name == name) = some own ∧ signature fuel function = .ok own := by
  induction compiled with
  | nil => simp at selected
  | @cons head own functions signatures headCompiled tail ih =>
      by_cases matched : head.name == name
      · simp only [List.find?_cons, matched, Option.some.injEq] at selected
        subst function
        exact ⟨own, by simp only [List.find?_cons, signature_name headCompiled, matched], headCompiled⟩
      · simp only [List.find?_cons, matched] at selected
        obtain ⟨result, found, accepted⟩ := ih selected
        exact ⟨result, by simpa only [List.find?_cons, signature_name headCompiled, matched] using found, accepted⟩

theorem compiledFunction_resolve {fuel : Nat} {functions : List Function} {signatures : List Signature}
    {scope : Scope} {codes : List GlobalCode}
    (signaturesCompiled : functions.mapM (signature fuel) = .ok signatures)
    (codesCompiled : CompiledGlobals fuel signatures scope (functions.zip signatures).reverse codes)
    {name : String} {function : Function}
    (selected : functions.find? (·.name == name) = some function) :
    ∃ (index : Nat) (code : GlobalCode), signatures.find? (·.name == name) = some code.own ∧
      codes[index]? = some code ∧ signature fuel function = .ok code.own ∧
      lowerFunction fuel signatures scope function code.own = .ok code.expression := by
  obtain ⟨own, signatureFound, _⟩ := (compiledSignatures signaturesCompiled).source_selected selected
  obtain ⟨signatureCompiled, index, code, codeFound, ownEqual, functionCompiled⟩ :=
    compiledFunction_selected signaturesCompiled codesCompiled selected signatureFound
  cases ownEqual
  exact ⟨index, code, signatureFound, codeFound, signatureCompiled, functionCompiled⟩

theorem GlobalCode.lookup_unique {signatures : List Signature} {codes : List GlobalCode}
    (aligned : codes.map GlobalCode.own = signatures.reverse)
    (unique : (signatures.map Signature.name).Nodup)
    {leftIndex rightIndex : Nat} {left right : GlobalCode}
    (leftFound : codes[leftIndex]? = some left) (rightFound : codes[rightIndex]? = some right)
    (sameName : left.own.name = right.own.name) : leftIndex = rightIndex ∧ left = right := by
  have names : codes.map (fun code => code.own.name) = (signatures.map Signature.name).reverse := by
    change codes.map (Signature.name ∘ GlobalCode.own) = _
    rw [← List.map_map, aligned, List.map_reverse]
  have codeNamesUnique : (codes.map (fun code => code.own.name)).Nodup := by
    rw [names]
    exact (List.reverse_perm _).nodup_iff.mpr unique
  have leftName : (codes.map (fun code => code.own.name))[leftIndex]? = some left.own.name := by
    simp only [List.getElem?_map, leftFound, Option.map_some]
  have rightName : (codes.map (fun code => code.own.name))[rightIndex]? = some left.own.name := by
    simp only [List.getElem?_map, rightFound, Option.map_some, sameName]
  have sameIndex : leftIndex = rightIndex := (List.getElem?_inj
    ((List.getElem?_eq_some_iff.mp leftName).1) codeNamesUnique).mp (leftName.trans rightName.symm)
  subst rightIndex
  exact ⟨rfl, Option.some.inj (leftFound.symm.trans rightFound)⟩

theorem compiledFunction_at {fuel : Nat} {functions : List Function} {signatures : List Signature}
    {scope : Scope} {codes : List GlobalCode}
    (signaturesCompiled : functions.mapM (signature fuel) = .ok signatures)
    (codesCompiled : CompiledGlobals fuel signatures scope (functions.zip signatures).reverse codes)
    (unique : (signatures.map Signature.name).Nodup)
    {name : String} {function : Function} {code : GlobalCode} {index : Nat}
    (selected : functions.find? (·.name == name) = some function)
    (signatureFound : signatures.find? (·.name == name) = some code.own)
    (codeFound : codes[index]? = some code) :
    signature fuel function = .ok code.own ∧
      lowerFunction fuel signatures scope function code.own = .ok code.expression := by
  obtain ⟨signatureCompiled, otherIndex, other, otherFound, ownEqual, functionCompiled⟩ :=
    compiledFunction_selected signaturesCompiled codesCompiled selected signatureFound
  have ⟨_, equal⟩ := GlobalCode.lookup_unique (codesCompiled.aligned signaturesCompiled)
    unique otherFound codeFound (congrArg Signature.name ownEqual)
  subst other
  exact ⟨signatureCompiled, functionCompiled⟩

end Solcore.Frontend.RustHull.Correspondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.PureCallCorrespondence
/-! Pure calls preserve the independent Hull meaning through the actual
expression-list compiler and argument pack. Every argument may allocate or
update source locals; the world and exact Core heap are threaded in order. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.PureCallCorrespondence

open Correspondence StatementCorrespondence ScalarExecution

inductive ArgumentsRel : List Lowered → List Semantics.Value → List Core.Value → Prop where
  | nil : ArgumentsRel [] [] []
  | cons {argument : Lowered} {arguments : List Lowered} {source : Semantics.Value}
      {sources : List Semantics.Value} {target : Core.Value} {targets : List Core.Value}
      (head : ValueRel argument.type source target) (tail : ArgumentsRel arguments sources targets) :
      ArgumentsRel (argument :: arguments) (source :: sources) (target :: targets)

private theorem pair_rename (leftType rightType : Core.Ty) (left right : Core.Expr)
    (mapping : Core.Renaming) :
    (Core.LocalSequence.pair leftType rightType left right).rename mapping =
      Core.LocalSequence.pair leftType rightType (left.rename mapping) (right.rename mapping) := by
  simp [Core.LocalSequence.pair, Core.LanguageResult.bind, Core.LanguageResult.success,
    Core.Expr.rename, Core.Renaming.lift]

private theorem exprs_cons {σ : Type} {functions : List Function}
    {effects : Semantics.ExternalSemantics σ} {sourceEnvironment : Semantics.Environment}
    {argument : Expr} {rest : List Expr} {initial final : Semantics.State σ}
    {sources : List Semantics.Value}
    (evaluated : Semantics.EvalExprs functions effects sourceEnvironment (argument :: rest)
      initial (.value sources) final) :
    ∃ source values middle, sources = source :: values ∧
      Semantics.EvalExpr functions effects sourceEnvironment argument initial (.value source) middle ∧
      Semantics.EvalExprs functions effects sourceEnvironment rest middle (.value values) final := by
  generalize resultEq : Semantics.Result.value sources = result at evaluated
  cases evaluated with
  | cons head tail =>
      rename_i middle source result
      cases result with
      | fault reason => simp [Semantics.Result.map] at resultEq
      | value values =>
          simp only [Semantics.Result.map, Semantics.Result.value.injEq] at resultEq
          exact ⟨source, values, middle, resultEq, head, tail⟩
  | fault => cases resultEq

theorem arguments_preserve {σ : Type} {functions : List Function}
    {effects : Semantics.ExternalSemantics σ} {signatures : List Signature}
    {external : σ → Core.Store → Prop} {arguments : List Expr}
    (preserves : ∀ argument ∈ arguments, NormalExprPreserves functions effects signatures external argument)
    {sourceEnvironment : Semantics.Environment} {initial final : Semantics.State σ}
    {sources : List Semantics.Value}
    (evaluated : Semantics.EvalExprs functions effects sourceEnvironment arguments initial (.value sources) final)
    {fuel : Nat} {scope : Scope} {lowered : List Lowered}
    (compiled : arguments.mapM (lowerExpression fuel signatures scope) = .ok lowered)
    {world : World} {mapping : Core.Renaming} {environment : Core.Environment} {store : Core.Store}
    (environmentRelated : EnvironmentRel world sourceEnvironment scope mapping environment)
    (heap : HeapRel world initial.heap store) (externalRelated : external initial.external store) :
    ∃ extension targets finalStore,
      ArgumentsRel lowered sources targets ∧
      Core.Evaluates environment store ((packArguments lowered).expression.rename mapping)
        (.inRight .word (bundleValues targets)) finalStore ∧
      HeapRel (world ++ extension) final.heap finalStore ∧ external final.external finalStore := by
  induction arguments generalizing initial final sources lowered world mapping environment store with
  | nil =>
      cases compiled
      cases evaluated
      exact ⟨[], [], store, .nil, .inRight .unit, by simpa using heap, externalRelated⟩
  | cons argument rest ih =>
      obtain ⟨source, sources, middle, rfl, head, tail⟩ := exprs_cons evaluated
      simp only [List.mapM_cons] at compiled
      obtain ⟨headCode, headCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
      obtain ⟨tailCode, tailCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
      cases returned
      obtain ⟨headExtension, target, middleStore, related, headEvaluation, middleHeap, middleExternal⟩ :=
        preserves argument (by simp) head headCompiled environmentRelated heap externalRelated
      cases rest with
      | nil =>
          cases tailCompiled
          cases tail
          exact ⟨headExtension, [target], middleStore, .cons related .nil,
            headEvaluation, middleHeap, middleExternal⟩
      | cons next rest =>
          have tailPreserves : ∀ value ∈ next :: rest,
              NormalExprPreserves functions effects signatures external value := by
            intro value member
            exact preserves value (by simp [member])
          have middleEnvironment := (environmentRelated.extendWorld headExtension).prepend [target]
          obtain ⟨tailExtension, targets, finalStore, tailRelated, tailEvaluation, finalHeap, finalExternal⟩ :=
            ih tailPreserves tail tailCompiled middleEnvironment middleHeap middleExternal
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
          refine ⟨headExtension ++ tailExtension, target :: targets, finalStore,
            .cons related tailRelated, ?_, ?_, finalExternal⟩
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
                rw [pair_rename]
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

open BuiltinCorrespondence

inductive PureBuiltin where
  | binary (operation : WordBinary)
  | unary (operation : WordUnary)
  | ternary (operation : WordTernary)
  | comparison (operation : WordComparison)
  | toInteger | fromInteger | iszero | pop
  deriving Repr, DecidableEq

def PureBuiltin.name : PureBuiltin → String
  | .binary operation => operation.name | .unary operation => operation.name
  | .ternary operation => operation.name | .comparison operation => operation.name
  | .toInteger => "wordToInteger" | .fromInteger => "wordFromInteger"
  | .iszero => "iszero" | .pop => "pop"

def pureBuiltin? (name : String) : Option PureBuiltin :=
  match primitiveName name with
  | "add" => some (.binary .add) | "sub" => some (.binary .sub) | "mul" => some (.binary .mul)
  | "div" => some (.binary .udiv) | "mod" => some (.binary .umod)
  | "sdiv" => some (.binary .sdiv) | "smod" => some (.binary .smod)
  | "exp" => some (.binary .pow) | "signextend" => some (.binary .signExtend)
  | "and" => some (.binary .bitAnd) | "or" => some (.binary .bitOr) | "xor" => some (.binary .bitXor)
  | "byte" => some (.binary .byteAt) | "shl" => some (.binary .shl) | "shr" => some (.binary .shr)
  | "sar" => some (.binary .sar)
  | "not" => some (.unary .bitNot) | "clz" => some (.unary .clz)
  | "addmod" => some (.ternary .addMod) | "mulmod" => some (.ternary .mulMod)
  | "eq" => some (.comparison .eq) | "lt" => some (.comparison .lt) | "gt" => some (.comparison .gt)
  | "slt" => some (.comparison .slt) | "sgt" => some (.comparison .sgt)
  | "wordToInteger" => some .toInteger | "wordFromInteger" => some .fromInteger
  | "iszero" => some .iszero | "pop" => some .pop
  | _ => none

theorem pureBuiltin_name {name : String} {operation : PureBuiltin}
    (classified : pureBuiltin? name = some operation) : primitiveName name = operation.name := by
  unfold pureBuiltin? at classified
  split at classified <;> cases classified <;> assumption

theorem pureBuiltin_known {name : String} {operation : PureBuiltin}
    (classified : pureBuiltin? name = some operation) (type : Ty) (values : List Semantics.Value) :
    (Semantics.primitive? name type values).isSome = true := by
  rw [primitiveName_meaning, pureBuiltin_name classified]
  cases operation with
  | binary op => cases op <;> rfl
  | unary op => cases op <;> rfl
  | ternary op => cases op <;> rfl
  | comparison op => cases op <;> rfl
  | toInteger => rfl
  | fromInteger => rfl
  | iszero => rfl
  | pop => rfl

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
      have same : lowered = result := Option.some.inj normalized
      exact congrArg Except.ok same.symm

private theorem ArgumentsRel.oneWord {arguments : List Lowered} {targets : List Core.Value}
    {value : Core.Word} (related : ArgumentsRel arguments [.word value] targets) :
    ∃ expression, arguments = [⟨.word, expression⟩] ∧ targets = [.word value] := by
  cases related with
  | cons head tail =>
      cases tail
      rename_i argument target
      cases argument with
      | mk type expression =>
          cases head
          exact ⟨expression, rfl, rfl⟩

private theorem ArgumentsRel.twoWords {arguments : List Lowered} {targets : List Core.Value}
    {left right : Core.Word} (related : ArgumentsRel arguments [.word left, .word right] targets) :
    ∃ leftCode rightCode, arguments = [⟨.word, leftCode⟩, ⟨.word, rightCode⟩] ∧
      targets = [.word left, .word right] := by
  cases related with
  | cons head tail =>
      obtain ⟨rightCode, rfl, rfl⟩ := tail.oneWord
      rename_i argument target
      cases argument with
      | mk type expression =>
          cases head
          exact ⟨expression, rightCode, rfl, rfl⟩

private theorem ArgumentsRel.threeWords {arguments : List Lowered} {targets : List Core.Value}
    {first second third : Core.Word}
    (related : ArgumentsRel arguments [.word first, .word second, .word third] targets) :
    ∃ firstCode secondCode thirdCode,
      arguments = [⟨.word, firstCode⟩, ⟨.word, secondCode⟩, ⟨.word, thirdCode⟩] ∧
      targets = [.word first, .word second, .word third] := by
  cases related with
  | cons head tail =>
      obtain ⟨secondCode, thirdCode, rfl, rfl⟩ := tail.twoWords
      rename_i argument target
      cases argument with
      | mk type expression =>
          cases head
          exact ⟨expression, secondCode, thirdCode, rfl, rfl⟩

private theorem binary_value (operation : Core.Word → Core.Word → Core.Word)
    {values : List Semantics.Value} {result : Semantics.Value}
    (computed : Semantics.binaryWords operation values = .value result) :
    ∃ left right, values = [.word left, .word right] ∧ result = .word (operation left right) := by
  unfold Semantics.binaryWords at computed
  split at computed
  next left right => cases computed; exact ⟨left, right, rfl, rfl⟩
  next => cases computed

private theorem unary_value (operation : Core.Word → Core.Word)
    {values : List Semantics.Value} {result : Semantics.Value}
    (computed : Semantics.unaryWord operation values = .value result) :
    ∃ value, values = [.word value] ∧ result = .word (operation value) := by
  unfold Semantics.unaryWord at computed
  split at computed
  next value => cases computed; exact ⟨value, rfl, rfl⟩
  next => cases computed

private theorem ternary_value (operation : Core.Word → Core.Word → Core.Word → Core.Word)
    {values : List Semantics.Value} {result : Semantics.Value}
    (computed : Semantics.ternaryWords operation values = .value result) :
    ∃ first second third, values = [.word first, .word second, .word third] ∧
      result = .word (operation first second third) := by
  unfold Semantics.ternaryWords at computed
  split at computed
  next first second third => cases computed; exact ⟨first, second, third, rfl, rfl⟩
  next => cases computed

private theorem comparison_value (type : Ty) (operation : Core.Word → Core.Word → Bool)
    {values : List Semantics.Value} {result : Semantics.Value}
    (computed : Semantics.compareWords type operation values = .value result) :
    ∃ left right, values = [.word left, .word right] ∧
      Semantics.booleanResult type (operation left right) = .value result := by
  unfold Semantics.compareWords at computed
  split at computed
  next left right => exact ⟨left, right, rfl, computed⟩
  next => cases computed

private theorem binary_expected (operation : WordBinary) (scope : Scope) (type : Core.Ty)
    (left right : Core.Expr) {lowered : Lowered}
    (compiled : lowerBuiltin scope operation.name type [⟨.word, left⟩, ⟨.word, right⟩] = .ok lowered) : type = .word := by
  have reduced : lowerBuiltin scope operation.name type [⟨.word, left⟩, ⟨.word, right⟩] = (do
      expectType type .word
      pure ⟨type, Core.LanguageResult.bind type (packArguments [⟨.word, left⟩, ⟨.word, right⟩]).expression
        (Core.LanguageResult.success operation.code)⟩) := by
    cases operation <;> rfl
  rw [reduced] at compiled
  obtain ⟨checked, checkedType, _⟩ := lower_bind_eq_ok.mp compiled
  cases checked
  exact expectType_eq_of_ok checkedType

private theorem unary_expected (operation : WordUnary) (scope : Scope) (type : Core.Ty)
    (argument : Core.Expr) {lowered : Lowered}
    (compiled : lowerBuiltin scope operation.name type [⟨.word, argument⟩] = .ok lowered) : type = .word := by
  have reduced : lowerBuiltin scope operation.name type [⟨.word, argument⟩] = (do
      expectType type .word
      pure ⟨type, Core.LanguageResult.bind type (packArguments [⟨.word, argument⟩]).expression
        (Core.LanguageResult.success operation.code)⟩) := by
    cases operation <;> rfl
  rw [reduced] at compiled
  obtain ⟨checked, checkedType, _⟩ := lower_bind_eq_ok.mp compiled
  cases checked
  exact expectType_eq_of_ok checkedType

private theorem ternary_expected (operation : WordTernary) (scope : Scope) (type : Core.Ty)
    (first second third : Core.Expr) {lowered : Lowered}
    (compiled : lowerBuiltin scope operation.name type [⟨.word, first⟩, ⟨.word, second⟩, ⟨.word, third⟩] = .ok lowered) : type = .word := by
  have reduced : lowerBuiltin scope operation.name type [⟨.word, first⟩, ⟨.word, second⟩, ⟨.word, third⟩] = (do
      expectType type .word
      pure ⟨type, Core.LanguageResult.bind type (packArguments [⟨.word, first⟩, ⟨.word, second⟩, ⟨.word, third⟩]).expression
        (Core.LanguageResult.success operation.code)⟩) := by
    cases operation <;> rfl
  rw [reduced] at compiled
  obtain ⟨checked, checkedType, _⟩ := lower_bind_eq_ok.mp compiled
  cases checked
  exact expectType_eq_of_ok checkedType

private theorem conversion_expected {name : String}
    (named : name = "wordToInteger" ∨ name = "wordFromInteger")
    (scope : Scope) (type : Core.Ty) (argument : Core.Expr) {lowered : Lowered}
    (compiled : lowerBuiltin scope name type [⟨.word, argument⟩] = .ok lowered) : type = .word := by
  have reduced : lowerBuiltin scope name type [⟨.word, argument⟩] = (do
      expectType .word type
      pure ⟨.word, argument⟩) := by
    rcases named with rfl | rfl <;> rfl
  rw [reduced] at compiled
  obtain ⟨checked, checkedType, _⟩ := lower_bind_eq_ok.mp compiled
  cases checked
  exact (expectType_eq_of_ok checkedType).symm

private theorem pop_expected (scope : Scope) (type : Core.Ty) (argument : Core.Expr) {lowered : Lowered}
    (compiled : lowerBuiltin scope "pop" type [⟨.word, argument⟩] = .ok lowered) : type = .unit := by
  have reduced : lowerBuiltin scope "pop" type [⟨.word, argument⟩] = (do
      expectType type .unit
      pure ⟨type, Core.LanguageResult.bind type argument
        (Core.LanguageResult.success (.apply (.lambda .word .unit .unit) (.var 0)))⟩) := by rfl
  rw [reduced] at compiled
  obtain ⟨checked, checkedType, _⟩ := lower_bind_eq_ok.mp compiled
  cases checked
  exact expectType_eq_of_ok checkedType

private theorem normal_result {name : String} {sourceType : Ty} {sources : List Semantics.Value}
    {source : Semantics.Value} {lowered : Lowered} {mapping : Core.Renaming}
    {environment : Core.Environment} {initial final : Core.Store}
    (computed : Semantics.primitive? name sourceType sources = some (.value source))
    (preserved : ∃ result target, Semantics.primitive? name sourceType sources = some result ∧
      ResultRel lowered.type result target ∧
      Core.Evaluates environment initial (lowered.expression.rename mapping) target final) :
    ∃ target, ValueRel lowered.type source target ∧
      Core.Evaluates environment initial (lowered.expression.rename mapping) (.inRight .word target) final := by
  obtain ⟨result, target, meaning, related, evaluated⟩ := preserved
  rw [computed] at meaning
  cases meaning
  cases related with
  | value related => exact ⟨_, related, evaluated⟩

theorem canonical_preserves (operation : PureBuiltin)
    {fuel : Nat} {sourceType : Ty} {type : Core.Ty}
    (typeCompiled : lowerType fuel sourceType = .ok type)
    {scope : Scope} {arguments : List Lowered} {lowered : Lowered}
    (compiled : lowerBuiltin scope operation.name type arguments = .ok lowered)
    {sources : List Semantics.Value} {targets : List Core.Value} {source : Semantics.Value}
    (computed : Semantics.primitive? operation.name sourceType sources = some (.value source))
    (related : ArgumentsRel arguments sources targets)
    {mapping : Core.Renaming} {environment : Core.Environment} {initial final : Core.Store}
    (evaluated : Core.Evaluates environment initial ((packArguments arguments).expression.rename mapping)
      (.inRight .word (bundleValues targets)) final) :
    ∃ target, ValueRel lowered.type source target ∧
      Core.Evaluates environment initial (lowered.expression.rename mapping) (.inRight .word target) final := by
  cases operation with
  | binary op =>
      dsimp only [PureBuiltin.name] at compiled computed
      have model : Semantics.primitive? op.name sourceType sources =
          some (Semantics.binaryWords op.eval sources) := by cases op <;> rfl
      have sourceComputed := computed
      rw [model] at sourceComputed
      obtain ⟨left, right, rfl, rfl⟩ := binary_value op.eval (Option.some.inj sourceComputed)
      obtain ⟨leftCode, rightCode, rfl, rfl⟩ := related.twoWords
      have expected := binary_expected op scope type leftCode rightCode compiled
      subst type
      exact normal_result computed (wordBinary op (by cases op <;> rfl) compiled evaluated sourceType)
  | unary op =>
      dsimp only [PureBuiltin.name] at compiled computed
      have model : Semantics.primitive? op.name sourceType sources =
          some (Semantics.unaryWord op.eval sources) := by cases op <;> rfl
      have sourceComputed := computed
      rw [model] at sourceComputed
      obtain ⟨value, rfl, rfl⟩ := unary_value op.eval (Option.some.inj sourceComputed)
      obtain ⟨code, rfl, rfl⟩ := related.oneWord
      have expected := unary_expected op scope type code compiled
      subst type
      exact normal_result computed (wordUnary op (by cases op <;> rfl) compiled evaluated sourceType)
  | ternary op =>
      dsimp only [PureBuiltin.name] at compiled computed
      have model : Semantics.primitive? op.name sourceType sources =
          some (Semantics.ternaryWords op.eval sources) := by cases op <;> rfl
      have sourceComputed := computed
      rw [model] at sourceComputed
      obtain ⟨first, second, third, rfl, rfl⟩ := ternary_value op.eval (Option.some.inj sourceComputed)
      obtain ⟨firstCode, secondCode, thirdCode, rfl, rfl⟩ := related.threeWords
      have expected := ternary_expected op scope type firstCode secondCode thirdCode compiled
      subst type
      exact normal_result computed (wordTernary op compiled evaluated sourceType)
  | comparison op =>
      dsimp only [PureBuiltin.name] at compiled computed
      have model : Semantics.primitive? op.name sourceType sources =
          some (Semantics.compareWords sourceType op.eval sources) := by cases op <;> rfl
      have sourceComputed := computed
      rw [model] at sourceComputed
      obtain ⟨left, right, rfl, _⟩ := comparison_value sourceType op.eval (Option.some.inj sourceComputed)
      obtain ⟨leftCode, rightCode, rfl, rfl⟩ := related.twoWords
      exact normal_result computed
        (wordComparison op (by cases op <;> rfl) typeCompiled compiled evaluated)
  | toInteger | fromInteger =>
      have sourceComputed : Semantics.unaryWord id sources = .value source := Option.some.inj computed
      obtain ⟨value, rfl, rfl⟩ := unary_value id sourceComputed
      obtain ⟨code, rfl, rfl⟩ := related.oneWord
      have expected := conversion_expected (by first | exact Or.inl rfl | exact Or.inr rfl)
        scope type code compiled
      subst type
      obtain ⟨_, resultRelated, resultEvaluation⟩ := conversion
        (by first | exact Or.inl rfl | exact Or.inr rfl) compiled evaluated sourceType
      cases resultRelated with
      | value related => exact ⟨_, related, resultEvaluation⟩
  | iszero =>
      have originalComputed := computed
      change (some (match sources with
        | [value] => match Semantics.condition? value with
          | some truth => Semantics.booleanResult sourceType (!truth)
          | none => .fault (.invalidValue "boolean argument")
        | _ => .fault .arityMismatch)) = some (.value source) at computed
      split at computed
      next value =>
        cases related with
        | cons head tail =>
            cases tail
            exact normal_result originalComputed (iszero typeCompiled compiled head evaluated)
      next => cases computed
  | pop =>
      change (some (match sources with
        | [.word _] => Semantics.Result.value Semantics.Value.unit
        | _ => .fault (.invalidValue "pop argument"))) = some (.value source) at computed
      split at computed
      next value =>
        have same : Semantics.Value.unit = source := Semantics.Result.value.inj (Option.some.inj computed)
        subst source
        obtain ⟨code, rfl, rfl⟩ := related.oneWord
        have expected := pop_expected scope type code compiled
        subst type
        obtain ⟨_, resultRelated, resultEvaluation⟩ := pop compiled evaluated sourceType
        cases resultRelated with
        | value related => exact ⟨_, related, resultEvaluation⟩
      next => cases computed

/-- Dispatch every supported pure source name, including compiler aliases,
through the checked builtin implementation and its actual packed inputs. -/
theorem builtin_preserves {name : String} {operation : PureBuiltin}
    (classified : pureBuiltin? name = some operation)
    {fuel : Nat} {sourceType : Ty} {type : Core.Ty}
    (typeCompiled : lowerType fuel sourceType = .ok type)
    {scope : Scope} {arguments : List Lowered} {lowered : Lowered}
    (compiled : lowerBuiltin scope name type arguments = .ok lowered)
    {sources : List Semantics.Value} {targets : List Core.Value} {source : Semantics.Value}
    (computed : Semantics.primitive? name sourceType sources = some (.value source))
    (related : ArgumentsRel arguments sources targets)
    {mapping : Core.Renaming} {environment : Core.Environment} {initial final : Core.Store}
    (evaluated : Core.Evaluates environment initial ((packArguments arguments).expression.rename mapping)
      (.inRight .word (bundleValues targets)) final) :
    ∃ target, ValueRel lowered.type source target ∧
      Core.Evaluates environment initial (lowered.expression.rename mapping) (.inRight .word target) final := by
  have accepted := normalized_compiled compiled
  rw [pureBuiltin_name classified] at accepted
  rw [primitiveName_meaning, pureBuiltin_name classified] at computed
  exact canonical_preserves operation typeCompiled accepted computed related evaluated

private theorem call_source {σ : Type} {functions : List Function}
    {effects : Semantics.ExternalSemantics σ} {sourceEnvironment : Semantics.Environment}
    {initial final : Semantics.State σ} {name : String} {type : Ty} {arguments : List Expr}
    {span : Option Span} {source : Semantics.Value} {operation : PureBuiltin}
    (classified : pureBuiltin? name = some operation)
    (notFunction : functions.find? (·.name == name) = none)
    (evaluated : Semantics.EvalExpr functions effects sourceEnvironment
      ⟨type, .call name arguments, span⟩ initial (.value source) final) :
    ∃ values, Semantics.EvalExprs functions effects sourceEnvironment arguments initial (.value values) final ∧
      Semantics.primitive? name type values = some (.value source) := by
  generalize resultEq : Semantics.Result.value source = result at evaluated
  cases evaluated <;> simp_all
  rename_i middle otherName otherArguments values kind argumentsEvaluated called
  cases called with
  | function selected _ =>
      exact (notFunction _ (List.mem_of_find?_eq_some selected)
        (by simpa only [beq_iff_eq] using List.find?_some selected)).elim
  | primitive _ computed => exact ⟨values, argumentsEvaluated, computed⟩
  | external _ notPrimitive _ =>
      have known := pureBuiltin_known classified type values
      rw [notPrimitive] at known
      cases known

private theorem call_components {fuel : Nat} {signatures : List Signature} {scope : Scope}
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

/-- A source call to a pure builtin is compositional through the public
expression lowerer. The only induction premises concern its source arguments;
function resolution and the complete builtin dispatch are proved here. -/
theorem call {σ : Type} {functions : List Function} {effects : Semantics.ExternalSemantics σ}
    {signatures : List Signature} {external : σ → Core.Store → Prop}
    {name : String} {arguments : List Expr} {operation : PureBuiltin}
    (classified : pureBuiltin? name = some operation)
    (notFunction : functions.find? (·.name == name) = none)
    (notSignature : signatures.find? (·.name == name) = none)
    (preserves : ∀ argument ∈ arguments, NormalExprPreserves functions effects signatures external argument)
    (type : Ty) (span : Option Span) :
    NormalExprPreserves functions effects signatures external ⟨type, .call name arguments, span⟩ := by
  intro sourceEnvironment initial final source evaluated
  obtain ⟨values, argumentsEvaluated, computed⟩ := call_source classified notFunction evaluated
  intro fuel scope lowered compiled world mapping environment store environmentRelated heap externalRelated
  cases fuel with
  | zero => simp [lowerExpression, fail] at compiled
  | succ fuel =>
      obtain ⟨expected, codes, typeCompiled, argumentsCompiled, builtinCompiled⟩ :=
        call_components notSignature compiled
      obtain ⟨extension, targets, finalStore, related, argumentsEvaluation, finalHeap, finalExternal⟩ :=
        arguments_preserve preserves argumentsEvaluated argumentsCompiled environmentRelated heap externalRelated
      obtain ⟨target, resultRelated, resultEvaluation⟩ :=
        builtin_preserves classified typeCompiled builtinCompiled computed related argumentsEvaluation
      exact ⟨extension, target, finalStore, resultRelated, resultEvaluation, finalHeap, finalExternal⟩

end Solcore.Frontend.RustHull.PureCallCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.NamedCallCorrespondence
/-! Named calls use the actual function-slot read and argument pack emitted by
the Hull compiler. The captured closure is read before argument evaluation;
its application retains the store produced by those arguments. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.NamedCallCorrespondence

open Correspondence ScalarExecution PureCallCorrespondence

def checkArgumentTypes (arguments : List Lowered) (parameters : List Core.Ty) : LowerM PUnit :=
  forIn (arguments.zip parameters) PUnit.unit fun (argument, parameter) _ => do
    expectType parameter argument.type
    pure (.yield PUnit.unit)

theorem checkedArgumentTypes {arguments : List Lowered} {parameters : List Core.Ty}
    (arity : arguments.length = parameters.length)
    (checked : checkArgumentTypes arguments parameters = .ok PUnit.unit) :
    arguments.map Lowered.type = parameters := by
  induction arguments generalizing parameters with
  | nil => exact (List.eq_nil_of_length_eq_zero arity.symm).symm
  | cons argument rest ih =>
      cases parameters with
      | nil => simp at arity
      | cons parameter parameters =>
          by_cases same : parameter = argument.type
          · have tailChecked : checkArgumentTypes rest parameters = .ok PUnit.unit := by
              simpa [checkArgumentTypes, List.forIn_cons, expectType, same] using checked
            have tail := ih (Nat.succ.inj arity) tailChecked
            simp only [List.map_cons, same, tail]
          · simp [checkArgumentTypes, expectType, same, fail, Bind.bind, Except.bind] at checked

theorem call_components {fuel : Nat} {signatures : List Signature} {scope : Scope}
    {name : String} {type : Ty} {arguments : List Expr} {span : Option Span} {lowered : Lowered}
    {own : Signature} (selected : signatures.find? (·.name == name) = some own)
    (compiled : lowerExpression (fuel + 1) signatures scope ⟨type, .call name arguments, span⟩ = .ok lowered) :
    ∃ codes functionCode,
      arguments.mapM (lowerExpression fuel signatures scope) = .ok codes ∧
      codes.map Lowered.type = own.parameters ∧
      scope.read (Effects.slotName ("function$" ++ name)) = .ok functionCode ∧
      functionCode.type = own.functionType ∧
      lowered = ⟨own.result, Core.LanguageResult.bind own.result functionCode.expression
        (Core.LanguageResult.bind own.result ((packArguments codes).expression.weakenAt 0)
          (.apply (.var 1) (.var 0)))⟩ := by
  simp only [lowerExpression] at compiled
  obtain ⟨_, _, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨codes, argumentsCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  simp only [selected] at compiled
  by_cases arity : codes.length = own.parameters.length
  · simp only [arity, ↓reduceIte, Pure.pure, Except.pure, Bind.bind, Except.bind] at compiled
    obtain ⟨checked, checkedArguments, compiled⟩ := lower_bind_eq_ok.mp compiled
    cases checked
    have argumentTypes := checkedArgumentTypes arity checkedArguments
    obtain ⟨functionCode, functionCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
    obtain ⟨checked, functionMatched, compiled⟩ := lower_bind_eq_ok.mp compiled
    cases checked
    obtain ⟨checked, _, returned⟩ := lower_bind_eq_ok.mp compiled
    cases checked
    cases returned
    exact ⟨codes, functionCode, argumentsCompiled, argumentTypes, functionCompiled,
      (expectType_eq_of_ok functionMatched).symm, rfl⟩
  · simp [arity, fail, Bind.bind, Except.bind] at compiled

theorem ArgumentsRel.values {codes : List Lowered} {sources : List Semantics.Value}
    {targets : List Core.Value} (related : ArgumentsRel codes sources targets) :
    ValuesRel (codes.map Lowered.type) sources targets := by
  induction related with
  | nil => exact .nil
  | cons head _ ih => exact .cons head ih

theorem call_source {σ : Type} {functions : List Function}
    {effects : Semantics.ExternalSemantics σ} {sourceEnvironment : Semantics.Environment}
    {initial final : Semantics.State σ} {type : Ty} {name : String} {arguments : List Expr}
    {span : Option Span} {source : Semantics.Value}
    (evaluated : Semantics.EvalExpr functions effects sourceEnvironment
      ⟨type, .call name arguments, span⟩ initial (.value source) final) :
    ∃ middle values,
      Semantics.EvalExprs functions effects sourceEnvironment arguments initial (.value values) middle ∧
      Semantics.EvalCall functions effects name type values middle (.value source) final := by
  generalize resultEq : Semantics.Result.value source = result at evaluated
  cases evaluated <;> simp_all
  exact ⟨_, _, by assumption, by assumption⟩

theorem call_function_source {σ : Type} {functions : List Function}
    {effects : Semantics.ExternalSemantics σ} {initial final : Semantics.State σ}
    {name : String} {type : Ty} {values : List Semantics.Value} {source : Semantics.Value}
    {function : Function} (found : functions.find? (·.name == name) = some function)
    (called : Semantics.EvalCall functions effects name type values initial (.value source) final) :
    Semantics.EvalFunction functions effects function values initial (.value source) final := by
  cases called with
  | function selected evaluated =>
      have same := Option.some.inj (found.symm.trans selected)
      cases same
      exact evaluated
  | primitive notFunction _ => rw [found] at notFunction; cases notFunction
  | external notFunction _ _ => rw [found] at notFunction; cases notFunction

/-- Reading the function slot, evaluating arguments, and entering the captured
body use the exact order and de Bruijn shifts generated by lowerExpression. -/
theorem call_evaluates {codes : List Lowered} {functionCode : Lowered} {resultType : Core.Ty}
    {inputType outputType : Core.Ty} {body : Core.Expr} {captured environment : Core.Environment}
    {mapping : Core.Renaming} {initial argumentStore final : Core.Store}
    {argumentValue result : Core.Value}
    (functionEvaluated : Core.Evaluates environment initial (functionCode.expression.rename mapping)
      (.inRight .word (.closure inputType outputType body captured)) initial)
    (argumentsEvaluated : Core.Evaluates (.closure inputType outputType body captured :: environment) initial
      ((packArguments codes).expression.rename (fun index => 1 + mapping index))
      (.inRight .word argumentValue) argumentStore)
    (bodyEvaluated : Core.Evaluates (argumentValue :: captured) argumentStore body result final) :
    Core.Evaluates environment initial
      ((Core.LanguageResult.bind resultType functionCode.expression
        (Core.LanguageResult.bind resultType ((packArguments codes).expression.weakenAt 0)
          (.apply (.var 1) (.var 0)))).rename mapping) result final := by
  have shifted : ((packArguments codes).expression.weakenAt 0).rename mapping.lift =
      (packArguments codes).expression.rename (fun index => 1 + mapping index) := by
    rw [← Core.Expr.rename_insertion, Core.Expr.rename_comp, Core.Renaming.lift_comp_insertion_zero]
    congr 1
    funext index
    simp [Core.Renaming.comp, Core.Renaming.insertion, Nat.add_comm]
  apply Core.LanguageResult.bind_success resultType functionEvaluated
  apply Core.LanguageResult.bind_success resultType
    (by simpa only [shifted] using argumentsEvaluated)
  exact Core.Evaluates.apply (.var rfl) (.var rfl) bodyEvaluated

theorem global_read_evaluates {codes : List GlobalCode} {locations : Nat → Nat}
    {scope : Scope} {mapping : Core.Renaming} {environment captured : Core.Environment}
    {store : Core.Store} {index : Nat} {code : GlobalCode} {lowered : Lowered}
    (found : codes[index]? = some code)
    (globals : GlobalEnvironmentRel codes locations scope mapping environment)
    (installed : InstalledGlobals codes locations captured store)
    (compiled : scope.read (Effects.slotName ("function$" ++ code.own.name)) = .ok lowered) :
    Core.Evaluates environment store (lowered.expression.rename mapping)
      (.inRight .word (.closure (bundleType code.own.parameters)
        (Core.LanguageResult.resultType code.own.result)
        (code.body.rename (globalShift index).lift)
        (installationEnvironment captured index))) store := by
  simp only [Scope.read] at compiled
  obtain ⟨⟨binding, slot⟩, looked, returned⟩ := lower_bind_eq_ok.mp compiled
  cases returned
  obtain ⟨sameType, reference, foundReference⟩ := globals.lookup found looked
  simp only [reference, ↓reduceIte]
  exact Core.OptionalCell.read_success (Core.Word.ofNatModulo 1)
    (.var (sameType ▸ foundReference)) (installed index code found)

/-- The function induction premise uses the closure installed by the real
assembler, including the binder shift from every earlier installation. -/
def FunctionExecutionPreserves {σ : Type} (functions : List Function)
    (effects : Semantics.ExternalSemantics σ) (codes : List GlobalCode) (locations : Nat → Nat)
    (captured : Core.Environment) (function : Function) (code : GlobalCode) (index : Nat)
    (sources : List Semantics.Value) (initial final : Semantics.State σ) (source : Semantics.Value) : Prop :=
  Semantics.EvalFunction functions effects function sources initial (.value source) final →
  ∀ {targets}, ValuesRel code.own.parameters sources targets →
    ∀ {world store}, HeapRel world initial.heap store → InstalledGlobals codes locations captured store →
      ∃ extension target finalStore,
        ValueRel code.own.result source target ∧
        Core.Evaluates (bundleValues targets :: installationEnvironment captured index) store
          (code.body.rename (globalShift index).lift) (.inRight .word target) finalStore ∧
        HeapRel (world ++ extension) final.heap finalStore ∧ InstalledGlobals codes locations captured finalStore

/-- Context for named-call expressions, in addition to the source-local heap
relation. Pure expression proofs can be lifted because they are uniform in
the external store invariant. -/
def ContextualExprPreserves {σ : Type} (functions : List Function)
    (effects : Semantics.ExternalSemantics σ) (signatures : List Signature)
    (codes : List GlobalCode) (locations : Nat → Nat) (captured : Core.Environment)
    (expression : Expr) : Prop :=
  ∀ {sourceEnvironment initial final sourceValue},
    Semantics.EvalExpr functions effects sourceEnvironment expression initial (.value sourceValue) final →
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

theorem contextual_of_normal {σ : Type} {functions : List Function}
    {effects : Semantics.ExternalSemantics σ} {signatures : List Signature}
    {codes : List GlobalCode} {locations : Nat → Nat} {captured : Core.Environment} {expression : Expr}
    (preserves : StatementCorrespondence.NormalExprPreserves functions effects signatures
      (fun _ store => InstalledGlobals codes locations captured store) expression) :
    ContextualExprPreserves functions effects signatures codes locations captured expression := by
  intro sourceEnvironment initial final sourceValue evaluated fuel scope lowered compiled
    world mapping environment store locals _ heap installed
  exact preserves evaluated compiled locals heap installed

/-- Named source calls reach the actual installed closure. The function
induction premise is applied after the ordered source arguments, with their
derived heap and the retained global cells. -/
theorem call {σ : Type} {functions : List Function} {effects : Semantics.ExternalSemantics σ}
    {signatures : List Signature} {codes : List GlobalCode} {locations : Nat → Nat}
    {captured : Core.Environment} {name : String} {function : Function} {code : GlobalCode} {index : Nat}
    (foundFunction : functions.find? (·.name == name) = some function)
    (foundSignature : signatures.find? (·.name == name) = some code.own)
    (foundCode : codes[index]? = some code)
    (preservesFunction : ∀ sources initial final source,
      FunctionExecutionPreserves functions effects codes locations captured function code index sources initial final source)
    {arguments : List Expr}
    (preservesArguments : ∀ argument ∈ arguments,
      StatementCorrespondence.NormalExprPreserves functions effects signatures
        (fun _ store => InstalledGlobals codes locations captured store) argument)
    (type : Ty) (span : Option Span) :
    ContextualExprPreserves functions effects signatures codes locations captured
      ⟨type, .call name arguments, span⟩ := by
  intro sourceEnvironment initial final sourceValue evaluated
  obtain ⟨middle, sources, argumentsSource, called⟩ := call_source evaluated
  have functionSource := call_function_source foundFunction called
  intro fuel scope lowered compiled world mapping environment store locals globals heap installed
  cases fuel with
  | zero => simp [lowerExpression, fail] at compiled
  | succ fuel =>
      obtain ⟨argumentCodes, functionCode, argumentsCompiled, argumentTypes, functionCompiled, _, rfl⟩ :=
        call_components foundSignature compiled
      have foundName : (code.own.name == name) = true :=
        List.find?_some (p := fun (own : Signature) => own.name == name) foundSignature
      have sameName : code.own.name = name := by simpa only [beq_iff_eq] using foundName
      rw [← sameName] at functionCompiled
      have functionEvaluation := global_read_evaluates foundCode globals installed functionCompiled
      let closure := Core.Value.closure (bundleType code.own.parameters)
        (Core.LanguageResult.resultType code.own.result) (code.body.rename (globalShift index).lift)
        (installationEnvironment captured index)
      have argumentLocals := locals.prepend [closure]
      obtain ⟨argumentExtension, targets, argumentStore, argumentsRelated,
        argumentsEvaluation, argumentHeap, argumentGlobals⟩ :=
        arguments_preserve preservesArguments argumentsSource argumentsCompiled argumentLocals heap installed
      have values : ValuesRel code.own.parameters sources targets :=
        argumentTypes ▸ ArgumentsRel.values argumentsRelated
      obtain ⟨callExtension, target, finalStore, related, bodyEvaluation, finalHeap, finalGlobals⟩ :=
        preservesFunction sources middle final sourceValue functionSource values argumentHeap argumentGlobals
      exact ⟨argumentExtension ++ callExtension, target, finalStore, related,
        call_evaluates functionEvaluation argumentsEvaluation bodyEvaluation,
        by simpa only [List.append_assoc] using finalHeap, finalGlobals⟩

end Solcore.Frontend.RustHull.NamedCallCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ContextualStatementCorrespondence
/-! Straight-line source execution with installed global functions. Lexical
function references and installed closures survive local allocation, writes
and administrative statement-sequencing binders. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ContextualStatementCorrespondence
open Correspondence StatementCorrespondence NamedCallCorrespondence

theorem declaration_allowed {fuel : Nat} {signatures : List Signature} {scope : Scope}
    {result : Core.Ty} {loops : Nat} {name : String} {type : Ty} {span : Option Span}
    {rest : List Stmt} {expression : Core.Expr}
    (compiled : lowerStatements (fuel + 1) signatures scope result loops
      (⟨.letDecl name type, span⟩ :: rest) = .ok expression) :
    name.startsWith Effects.reservedPrefix = false := by
  cases allowed : name.startsWith Effects.reservedPrefix with
  | false => rfl
  | true => simp [lowerStatements, allowed, fail, Bind.bind, Except.bind] at compiled

theorem assign_variable {σ : Type} {functions : List Function}
    {effects : Semantics.ExternalSemantics σ} {signatures : List Signature}
    {codes : List GlobalCode} {locations : Nat → Nat} {captured : Core.Environment}
    {rhs : Expr} (rightPreserves : ContextualExprPreserves functions effects signatures codes locations captured rhs)
    {sourceEnvironment : Semantics.Environment} {initial middle final : Semantics.State σ}
    {sourceValue : Semantics.Value} {sourceType : Ty} {name : String}
    {leftSpan statementSpan : Option Span}
    (sourceEvaluated : Semantics.EvalExpr functions effects sourceEnvironment rhs initial
      (.value sourceValue) middle)
    (assigned : Semantics.assignResult sourceEnvironment middle
      ⟨sourceType, .var name, leftSpan⟩ sourceValue = .value final)
    {fuel : Nat} {scope : Scope} {result : Core.Ty} {loops : Nat} {expression : Core.Expr}
    (compiled : lowerStatement (fuel + 1) signatures scope result loops
      ⟨.assign ⟨sourceType, .var name, leftSpan⟩ rhs, statementSpan⟩ = .ok expression)
    {world : World} {mapping : Core.Renaming} {environment : Core.Environment} {store : Core.Store}
    (environmentRelated : EnvironmentRel world sourceEnvironment scope mapping environment)
    (globalsRelated : GlobalEnvironmentRel codes locations scope mapping environment)
    (heapRelated : HeapRel world initial.heap store) (installed : InstalledGlobals codes locations captured store) :
    ∃ extension finalStore,
      Core.Evaluates environment store (expression.rename mapping)
        (Core.LocalLoop.fallthroughValue result) finalStore ∧
      HeapRel (world ++ extension) final.heap finalStore ∧ InstalledGlobals codes locations captured finalStore := by
  obtain ⟨right, binding, index, rightCompiled, looked, _, sameType, rfl⟩ :=
    assign_variable_components compiled
  obtain ⟨extension, value, middleStore, valueRelated, evaluated, middleHeap, middleInstalled⟩ :=
    rightPreserves sourceEvaluated rightCompiled environmentRelated globalsRelated heapRelated installed
  rw [sameType] at valueRelated
  obtain ⟨sourceLocation, old, found, read, rfl⟩ := assign_variable_source assigned
  have middleEnvironment := environmentRelated.extendWorld extension
  obtain ⟨location, entry, _, targetFound⟩ :=
    middleEnvironment name sourceLocation binding index found looked
  obtain ⟨oldValue, targetRead, _⟩ := middleHeap.read entry read
  have written : middleStore.write? location (.inRight .unit value) =
      some (middleStore.set location (.inRight .unit value)) :=
    Core.Store.write?_eq_some_iff.mpr ⟨middleHeap.location_bound entry, rfl⟩
  exact ⟨extension, _, assign_variable_core evaluated targetFound targetRead written,
    middleHeap.write entry valueRelated written,
    middleInstalled.write middleHeap entry written⟩

theorem returned {σ : Type} {functions : List Function}
    {effects : Semantics.ExternalSemantics σ} {signatures : List Signature}
    {codes : List GlobalCode} {locations : Nat → Nat} {captured : Core.Environment} {value : Expr}
    (preserves : ContextualExprPreserves functions effects signatures codes locations captured value)
    {sourceEnvironment : Semantics.Environment} {initial final : Semantics.State σ}
    {sourceValue : Semantics.Value}
    (sourceEvaluated : Semantics.EvalExpr functions effects sourceEnvironment value initial
      (.value sourceValue) final)
    {fuel : Nat} {scope : Scope} {type : Core.Ty} {loops : Nat} {span : Option Span}
    {expression : Core.Expr}
    (compiled : lowerStatement (fuel + 1) signatures scope type loops
      ⟨.returnStmt value, span⟩ = .ok expression)
    {world : World} {mapping : Core.Renaming} {environment : Core.Environment} {store : Core.Store}
    (environmentRelated : EnvironmentRel world sourceEnvironment scope mapping environment)
    (globalsRelated : GlobalEnvironmentRel codes locations scope mapping environment)
    (heapRelated : HeapRel world initial.heap store) (installed : InstalledGlobals codes locations captured store) :
    ∃ extension targetValue finalStore,
      ControlRel type (.returned sourceValue) targetValue ∧
      Core.Evaluates environment store (expression.rename mapping) targetValue finalStore ∧
      HeapRel (world ++ extension) final.heap finalStore ∧ InstalledGlobals codes locations captured finalStore := by
  have components := compiled
  simp only [lowerStatement] at components
  obtain ⟨lowered, valueCompiled, components⟩ := lower_bind_eq_ok.mp components
  obtain ⟨checked, matched, _⟩ := lower_bind_eq_ok.mp components
  cases checked
  have sameType := expectType_eq_of_ok matched
  obtain ⟨extension, targetValue, finalStore, valueRelated, evaluated, finalHeap, finalInstalled⟩ :=
    preserves sourceEvaluated valueCompiled environmentRelated globalsRelated heapRelated installed
  exact ⟨extension, Core.LocalLoop.returnedValue targetValue, finalStore,
    .returned (sameType ▸ valueRelated), return_success compiled valueCompiled evaluated,
    finalHeap, finalInstalled⟩

theorem expression_statement {σ : Type} {functions : List Function}
    {effects : Semantics.ExternalSemantics σ} {signatures : List Signature}
    {codes : List GlobalCode} {locations : Nat → Nat} {captured : Core.Environment} {value : Expr}
    (preserves : ContextualExprPreserves functions effects signatures codes locations captured value)
    {sourceEnvironment : Semantics.Environment} {initial final : Semantics.State σ}
    {sourceValue : Semantics.Value}
    (sourceEvaluated : Semantics.EvalExpr functions effects sourceEnvironment value initial
      (.value sourceValue) final)
    {fuel : Nat} {scope : Scope} {type : Core.Ty} {loops : Nat} {span : Option Span}
    {expression : Core.Expr}
    (compiled : lowerStatement (fuel + 1) signatures scope type loops
      ⟨.expression value, span⟩ = .ok expression)
    {world : World} {mapping : Core.Renaming} {environment : Core.Environment} {store : Core.Store}
    (environmentRelated : EnvironmentRel world sourceEnvironment scope mapping environment)
    (globalsRelated : GlobalEnvironmentRel codes locations scope mapping environment)
    (heapRelated : HeapRel world initial.heap store) (installed : InstalledGlobals codes locations captured store) :
    ∃ extension finalStore,
      Core.Evaluates environment store (expression.rename mapping)
        (Core.LocalLoop.fallthroughValue type) finalStore ∧
      HeapRel (world ++ extension) final.heap finalStore ∧ InstalledGlobals codes locations captured finalStore := by
  simp only [lowerStatement] at compiled
  obtain ⟨lowered, valueCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
  cases returned
  obtain ⟨extension, targetValue, finalStore, _, evaluated, finalHeap, finalInstalled⟩ :=
    preserves sourceEvaluated valueCompiled environmentRelated globalsRelated heapRelated installed
  refine ⟨extension, finalStore, ?_, finalHeap, finalInstalled⟩
  apply Core.LanguageResult.bind_success _ evaluated
  simpa only [← Core.Expr.rename_insertion, rename_fallthrough] using
    Core.LocalLoop.fallthrough_evaluates type (targetValue :: environment) finalStore

/-- This first statement fragment has no branch or loop construct. Its
expression premises are proved separately against the same source semantics. -/
def StraightLine {σ : Type} (functions : List Function)
    (effects : Semantics.ExternalSemantics σ) (signatures : List Signature)
    (codes : List GlobalCode) (locations : Nat → Nat) (captured : Core.Environment) (statement : Stmt) : Prop :=
  match statement.kind with
  | .letDecl _ _ | .comment _ => True
  | .assign ⟨_, .var _, _⟩ value | .expression value | .returnStmt value =>
      ContextualExprPreserves functions effects signatures codes locations captured value
  | _ => False

theorem straight_line_statement {σ : Type} {functions : List Function}
    {effects : Semantics.ExternalSemantics σ} {signatures : List Signature}
    {codes : List GlobalCode} {locations : Nat → Nat} {captured : Core.Environment}
    {statement : Stmt} (eligible : StraightLine functions effects signatures codes locations captured statement)
    (notDeclaration : ∀ name type, statement.kind ≠ .letDecl name type)
    {sourceEnvironment : Semantics.Environment} {initial final : Semantics.State σ}
    {control : Semantics.Control}
    (sourceEvaluated : Semantics.EvalStmt functions effects sourceEnvironment statement initial control final)
    (normal : NormalControl control)
    {fuel : Nat} {scope : Scope} {type : Core.Ty} {loops : Nat} {expression : Core.Expr}
    (compiled : lowerStatement fuel signatures scope type loops statement = .ok expression)
    {world : World} {mapping : Core.Renaming} {environment : Core.Environment} {store : Core.Store}
    (environmentRelated : EnvironmentRel world sourceEnvironment scope mapping environment)
    (globalsRelated : GlobalEnvironmentRel codes locations scope mapping environment)
    (heapRelated : HeapRel world initial.heap store) (installed : InstalledGlobals codes locations captured store) :
    ∃ extension targetValue finalStore,
      ControlRel type control targetValue ∧
      Core.Evaluates environment store (expression.rename mapping) targetValue finalStore ∧
      HeapRel (world ++ extension) final.heap finalStore ∧ InstalledGlobals codes locations captured finalStore := by
  cases fuel with
  | zero => simp [lowerStatement, fail] at compiled
  | succ fuel =>
      cases statement with | mk kind span =>
      cases sourceEvaluated <;> simp_all only [NormalControl]
      case assign lhs rhs middle value kind evaluated assigned =>
        cases kind
        cases lhs with | mk lhsType lhsKind lhsSpan =>
        cases lhsKind <;> simp only [StraightLine] at eligible
        all_goals try contradiction
        case var name =>
          obtain ⟨extension, finalStore, executed, finalHeap, finalInstalled⟩ :=
            assign_variable eligible evaluated assigned compiled environmentRelated globalsRelated heapRelated installed
          exact ⟨extension, _, finalStore, .fallthrough, executed, finalHeap, finalInstalled⟩
      case expression value sourceValue kind evaluated =>
        cases kind
        obtain ⟨extension, finalStore, executed, finalHeap, finalInstalled⟩ :=
          expression_statement eligible evaluated compiled environmentRelated globalsRelated heapRelated installed
        exact ⟨extension, _, finalStore, .fallthrough, executed, finalHeap, finalInstalled⟩
      case returned value sourceValue kind evaluated =>
        cases kind
        exact returned eligible evaluated compiled environmentRelated globalsRelated heapRelated installed
      case block => exact False.elim eligible
      case forInit => exact False.elim eligible
      case forLoop => exact False.elim eligible
      case matchStmt => exact False.elim eligible
      case assembly => exact False.elim eligible
      case revert => exact False.elim eligible
      case comment text kind =>
        cases kind
        simp only [lowerStatement] at compiled
        cases compiled
        exact ⟨[], _, store, .fallthrough, Core.LocalLoop.fallthrough_evaluates _ _ _,
          by simpa only [List.append_nil] using heapRelated, installed⟩

/-- Accepted straight-line statement lists preserve normal source execution,
including each allocation and write. The premise concerns actual independent
source derivations; fuel here bounds compilation, not source execution. -/
theorem straight_line_statements {σ : Type} {functions : List Function}
    {effects : Semantics.ExternalSemantics σ} {signatures : List Signature}
    {codes : List GlobalCode} {locations : Nat → Nat} {captured : Core.Environment}
    {fuel : Nat} {scope : Scope} {type : Core.Ty} {loops : Nat} {expression : Core.Expr}
    {statements : List Stmt}
    (compiled : lowerStatements fuel signatures scope type loops statements = .ok expression)
    (eligible : ∀ statement ∈ statements, StraightLine functions effects signatures codes locations captured statement)
    {sourceEnvironment : Semantics.Environment} {initial final : Semantics.State σ}
    {control : Semantics.Control}
    (sourceEvaluated : Semantics.EvalStatements functions effects sourceEnvironment statements initial control final)
    (normal : NormalControl control)
    {world : World} {mapping : Core.Renaming} {environment : Core.Environment} {store : Core.Store}
    (environmentRelated : EnvironmentRel world sourceEnvironment scope mapping environment)
    (globalsRelated : GlobalEnvironmentRel codes locations scope mapping environment)
    (heapRelated : HeapRel world initial.heap store) (installed : InstalledGlobals codes locations captured store) :
    ∃ extension targetValue finalStore,
      ControlRel type control targetValue ∧
      Core.Evaluates environment store (expression.rename mapping) targetValue finalStore ∧
      HeapRel (world ++ extension) final.heap finalStore ∧ InstalledGlobals codes locations captured finalStore := by
  induction fuel generalizing scope type loops expression statements sourceEnvironment initial final control
      world mapping environment store with
  | zero => simp [lowerStatements, fail] at compiled
  | succ fuel ih =>
      cases sourceEvaluated
      case nil =>
        exact ⟨[], _, store, .fallthrough, empty compiled mapping environment store,
          by simpa only [List.append_nil] using heapRelated, installed⟩
      case declare statement rest name sourceType sourceValue kind zero tail =>
        cases statement with | mk statementKind span =>
        cases kind
        have allowed := declaration_allowed compiled
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
        obtain ⟨extension, targetValue, finalStore, related, bodyEvaluated, finalHeap, finalInstalled⟩ :=
          ih bodyCompiled (fun statement member => eligible statement (List.mem_cons_of_mem _ member))
            tail normal environmentExtended globalsExtended allocated (installed.append _)
        refine ⟨[(coreType shape, store.length)] ++ extension, targetValue, finalStore,
          related, ?_, ?_, finalInstalled⟩
        · have initialized := Core.OptionalCell.allocateInitialized_evaluates
            (type := coreType shape) evaluated
          have same := zeroValue_rename shape zeroCompiled mapping
          simpa only [Core.Expr.rename, Core.OptionalCell.allocateInitialized, same] using
            Core.Evaluates.letE initialized bodyEvaluated
        · simpa only [List.append_assoc] using finalHeap
      case declareInvalid => contradiction
      case next statement rest middle notDeclaration head tail =>
        obtain ⟨first, next, firstCompiled, nextCompiled, rfl⟩ := sequence_components notDeclaration compiled
        obtain ⟨firstExtension, firstValue, middleStore, firstRelated, firstEvaluated, middleHeap, middleInstalled⟩ :=
          straight_line_statement (eligible statement (List.mem_cons_self ..)) notDeclaration
            head trivial firstCompiled environmentRelated globalsRelated heapRelated installed
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
        obtain ⟨extension, targetValue, finalStore, related, nextEvaluated, finalHeap, finalInstalled⟩ :=
          ih nextCompiled (fun statement member => eligible statement (List.mem_cons_of_mem _ member))
            tail normal nextEnvironment nextGlobals middleHeap middleInstalled
        exact ⟨firstExtension ++ extension, targetValue, finalStore, related,
          sequence_fallthrough firstEvaluated nextEvaluated,
          by simpa only [List.append_assoc] using finalHeap, finalInstalled⟩
      case stop statement rest notDeclaration stopped head =>
        obtain ⟨first, next, firstCompiled, _, rfl⟩ := sequence_components notDeclaration compiled
        obtain ⟨extension, targetValue, finalStore, related, evaluated, finalHeap, finalInstalled⟩ :=
          straight_line_statement (eligible statement (List.mem_cons_self ..)) notDeclaration
            head normal firstCompiled environmentRelated globalsRelated heapRelated installed
        refine ⟨extension, targetValue, finalStore, related, ?_, finalHeap, finalInstalled⟩
        rw [rename_sequence]
        cases related with
        | fallthrough => exact False.elim (stopped rfl)
        | returned valueRelated => exact Core.LocalLoop.sequence_returned type evaluated
        | breaking => contradiction
        | continuing => contradiction
        | language => contradiction

end Solcore.Frontend.RustHull.ContextualStatementCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ContextualFunctionBodyCorrespondence
/-! Function-body correspondence with real installed global functions. The
accepted parameter-name guard protects global bindings during initialization,
and the exact captured-environment renaming is retained through the body. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ContextualStatementCorrespondence
open Correspondence ScalarExecution StatementCorrespondence NamedCallCorrespondence

def checkParameterNames (arguments : List Arg) : LowerM PUnit :=
  forIn arguments PUnit.unit fun argument _ => do
    if argument.name.startsWith Effects.reservedPrefix then fail "reserved runtime parameter name"
    pure (.yield PUnit.unit)

theorem checkParameterNames_allowed {arguments : List Arg}
    (checked : checkParameterNames arguments = .ok PUnit.unit) :
    ∀ argument ∈ arguments, argument.name.startsWith Effects.reservedPrefix = false := by
  induction arguments with
  | nil => intros; contradiction
  | cons argument rest ih =>
      cases allowed : argument.name.startsWith Effects.reservedPrefix with
      | true =>
          simp only [checkParameterNames, List.forIn_cons, allowed, ↓reduceIte, fail, Bind.bind, Except.bind] at checked
          cases checked
      | false =>
          have tailChecked : checkParameterNames rest = .ok PUnit.unit := by
            simpa only [checkParameterNames, List.forIn_cons, allowed, Bool.false_eq_true, ↓reduceIte,
              Bind.bind, Except.bind, Pure.pure, Except.pure] using checked
          intro selected member
          cases member with
          | head => exact allowed
          | tail _ member => exact ih tailChecked selected member

theorem lowerFunction_parameters_allowed {fuel : Nat} {signatures : List Signature} {scope : Scope}
    {function : Function} {own : Signature} {expression : Core.Expr}
    (compiled : lowerFunction fuel signatures scope function own = .ok expression) :
    ∀ argument ∈ function.args, argument.name.startsWith Effects.reservedPrefix = false := by
  by_cases unique : (function.args.map (·.name)).eraseDups.length = function.args.length
  · simp only [lowerFunction, unique, ↓reduceIte] at compiled
    obtain ⟨checked, namesChecked, _⟩ := lower_bind_eq_ok.mp compiled
    cases checked
    exact checkParameterNames_allowed namesChecked
  · simp [lowerFunction, unique, fail, Bind.bind, Except.bind] at compiled

theorem straight_line_body {σ : Type} {functions : List Function}
    {effects : Semantics.ExternalSemantics σ} {signatures : List Signature}
    {codes : List GlobalCode} {locations : Nat → Nat} {captured : Core.Environment}
    {typeFuel fuel : Nat} {sourceType : Ty} {scope : Scope} {type : Core.Ty}
    {expression : Core.Expr} {statements : List Stmt}
    (typeCompiled : lowerType typeFuel sourceType = .ok type)
    (compiled : lowerStatements fuel signatures scope type 0 statements = .ok expression)
    (eligible : ∀ statement ∈ statements, StraightLine functions effects signatures codes locations captured statement)
    {sourceEnvironment : Semantics.Environment} {initial final : Semantics.State σ}
    {control : Semantics.Control}
    (sourceEvaluated : Semantics.EvalStatements functions effects sourceEnvironment statements initial control final)
    (normal : NormalControl control)
    {world : World} {mapping : Core.Renaming} {environment : Core.Environment} {store : Core.Store}
    (environmentRelated : EnvironmentRel world sourceEnvironment scope mapping environment)
    (globalsRelated : GlobalEnvironmentRel codes locations scope mapping environment)
    (heapRelated : HeapRel world initial.heap store) (installed : InstalledGlobals codes locations captured store) :
    ∃ extension targetValue finalStore,
      ResultRel type (Semantics.finishFunction sourceType control) targetValue ∧
      Core.Evaluates environment store ((finishedBody type expression).rename mapping) targetValue finalStore ∧
      HeapRel (world ++ extension) final.heap finalStore ∧ InstalledGlobals codes locations captured finalStore := by
  obtain ⟨extension, controlValue, finalStore, related, evaluated, finalHeap, finalInstalled⟩ :=
    straight_line_statements compiled eligible sourceEvaluated normal
      environmentRelated globalsRelated heapRelated installed
  obtain ⟨value, resultRelated, finished⟩ := finish_preserves typeCompiled related evaluated
  exact ⟨extension, value, finalStore, resultRelated, finished, finalHeap, finalInstalled⟩

/-- The source function derivation reaches the actual lowered, renamed body.
Both its local cells and its global function references are derived from the
actual argument initializer; no parameter-heap correspondence is assumed. -/
theorem lowerFunction_body_contextual {σ : Type} {functions : List Function}
    {effects : Semantics.ExternalSemantics σ} {signatures : List Signature}
    {codes : List GlobalCode} {locations : Nat → Nat} {captured : Core.Environment}
    {typeFuel fuel : Nat} {scope : Scope} {function : Function} {own : Signature}
    {body : Core.Expr}
    (signatureCompiled : signature typeFuel function = .ok own)
    (compiled : lowerFunction fuel signatures scope function own =
      .ok (.lambda (bundleType own.parameters) (Core.LanguageResult.resultType own.result) body))
    (eligible : ∀ statement ∈ function.body, StraightLine functions effects signatures codes locations captured statement)
    {sources : List Semantics.Value} {targets : List Core.Value}
    (values : ValuesRel own.parameters sources targets)
    {initial final : Semantics.State σ} {sourceResult : Semantics.Result Semantics.Value}
    (sourceEvaluated : Semantics.EvalFunction functions effects function sources initial sourceResult final)
    (normal : ∃ value, sourceResult = .value value)
    {world : World} {mapping : Core.Renaming} {environment : Core.Environment} {store : Core.Store}
    (globalsRelated : GlobalEnvironmentRel codes locations scope mapping environment)
    (heapRelated : HeapRel world initial.heap store)
    (installed : InstalledGlobals codes locations captured store) :
    ∃ extension targetValue finalStore,
      ResultRel own.result sourceResult targetValue ∧
      Core.Evaluates (bundleValues targets :: environment) store (body.rename mapping.lift)
        targetValue finalStore ∧
      HeapRel (world ++ extension) final.heap finalStore ∧ InstalledGlobals codes locations captured finalStore := by
  have allowed := lowerFunction_parameters_allowed compiled
  cases sourceEvaluated with
  | arity mismatch => obtain ⟨value, same⟩ := normal; contradiction
  | body bound sourceExecuted =>
      rename_i allocated sourceEnvironment control
      have controlNormal : NormalControl control := by
        obtain ⟨value, same⟩ := normal
        cases control <;> first | trivial | simp [Semantics.finishFunction] at same
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
        initialize_parameters_renamed
          (external := fun (_ : σ) targetStore => InstalledGlobals codes locations captured targetStore)
          values arity emptyEnvironment heapRelated installed
          (fun _ _ _ _ hypothesis => hypothesis.append _)
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (bound.symm.trans sourceBound))
      have parameterGlobals := cells.globalEnvironment arity allowed
        (globalsRelated.temporary (bundleType own.parameters) (bundleValues targets))
      obtain ⟨extension, targetValue, finalStore, related, executed, finalHeap, finalInstalled⟩ :=
        straight_line_body resultCompiled statementsCompiled eligible sourceExecuted controlNormal
          parametersRelated parameterGlobals allocatedHeap allocatedGlobals
      have initialized := cells.evaluates_renamed (allValues := targets) (start := 0)
        (mapping := mapping.lift) rfl
        (fun index value found => by simpa only [Nat.zero_add] using found) executed
      refine ⟨parameterExtension ++ extension, targetValue, finalStore, related, ?_, ?_, finalInstalled⟩
      · simpa only [parameterCode, values.length.2] using initialized
      · simpa only [List.append_assoc] using finalHeap

end Solcore.Frontend.RustHull.ContextualStatementCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.GlobalInvocationCorrespondence
/-! The real entry invocation after global installation: lookup reads the
registered closure and passes the original bundle past global and runtime
bindings, including the Unit binders introduced during installation. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.Correspondence

theorem globalEnvironment_argument (signatures : List Signature) (base : Nat)
    (runtimeValues : Core.Environment) (input : Core.Value) (caller : Core.Environment) :
    (globalEnvironment signatures base (runtimeValues ++ input :: caller))[signatures.length + runtimeValues.length]? = some input := by
  rw [globalEnvironment_eq, List.getElem?_append_right (by simp)]
  simp only [List.length_reverse, List.length_map, List.length_zipIdx, Nat.add_sub_cancel_left]
  simp

theorem globalInvocation_rename (own : Signature) (index globals runtime offsetCount : Nat) :
    (globalInvocation own index globals runtime).rename (globalShift offsetCount) =
      Core.LanguageResult.bind own.result
        (Core.OptionalCell.read own.functionType (.var (offsetCount + index)) (Core.Word.ofNatModulo 1))
        (.apply (.var 0) (.var (offsetCount + (globals + runtime) + 1))) := by
  simp [globalInvocation, Core.LanguageResult.bind, Core.OptionalCell.read,
    Core.LanguageResult.failure, Core.LanguageResult.success, Core.Expr.rename,
    Core.Renaming.lift, globalShift]

/-- The selected installed closure is called in its exact capture environment.
The argument is the original public input bundle, with no host reconstruction. -/
theorem globalInvocation_evaluates {signatures : List Signature} {codes : List GlobalCode}
    (aligned : codes.map GlobalCode.own = signatures.reverse)
    {index : Nat} {code : GlobalCode} (selected : codes[index]? = some code)
    {base : Nat} {runtimeValues caller : Core.Environment} {input result : Core.Value}
    {store final : Core.Store}
    (installed : InstalledGlobals codes (globalLocations signatures base)
      (globalEnvironment signatures base (runtimeValues ++ input :: caller)) store)
    (evaluated : Core.Evaluates
      (input :: installationEnvironment
        (globalEnvironment signatures base (runtimeValues ++ input :: caller)) index)
      store (code.body.rename (globalShift index).lift) result final) :
    Core.Evaluates
      (installationEnvironment
        (globalEnvironment signatures base (runtimeValues ++ input :: caller)) codes.length)
      store ((globalInvocation code.own index signatures.length runtimeValues.length).rename
        (globalShift codes.length)) result final := by
  rw [globalInvocation_rename]
  have reference : (globalEnvironment signatures base (runtimeValues ++ input :: caller))[index]? =
      some (.cellRef (Core.OptionalCell.cellType code.own.functionType)
        (globalLocations signatures base index)) := by
    apply globalEnvironment_lookup
    simp only [← aligned, List.getElem?_map, selected, Option.map_some]
  have read := Core.OptionalCell.read_success (Core.Word.ofNatModulo 1)
    (Core.Evaluates.var (installationEnvironment_lookup reference codes.length))
    (installed index code selected)
  apply Core.LanguageResult.bind_success code.own.result read
  apply Core.Evaluates.apply (.var rfl) (Core.Evaluates.var ?_) evaluated
  exact installationEnvironment_lookup
    (globalEnvironment_argument signatures base runtimeValues input caller) codes.length

end Solcore.Frontend.RustHull.Correspondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.InitializationCoverage
/-! The actual source argument binder establishes coverage of the compiler's
parameter scope. Equal arities also exclude the malformed argument outcome. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.Correspondence

theorem bindArguments_exists {σ : Type} {arguments : List Arg} {sources : List Semantics.Value}
    (arity : arguments.length = sources.length) (environment : Semantics.Environment)
    (state : Semantics.State σ) :
    ∃ finalEnvironment finalState,
      Semantics.bindArguments arguments sources environment state = some (finalEnvironment, finalState) := by
  induction arguments generalizing sources environment state with
  | nil =>
      cases sources with
      | nil => exact ⟨environment, state, rfl⟩
      | cons => simp at arity
  | cons argument arguments ih =>
      cases sources with
      | nil => simp at arity
      | cons source sources =>
          exact ih (Nat.succ.inj arity) ((argument.name, state.heap.length) :: environment)
            (Semantics.allocate state source).2

/-- Follow the same allocations and name insertions returned by bindArguments;
no second initializer is used to establish body coverage. -/
theorem ScopeCoverage.bindArguments {σ : Type} {arguments : List Arg} {types : List Core.Ty}
    {sources : List Semantics.Value} {environment finalEnvironment : Semantics.Environment}
    {state finalState : Semantics.State σ} {scope : Scope}
    (covered : ScopeCoverage environment scope) (arity : arguments.length = types.length)
    (bound : Semantics.bindArguments arguments sources environment state = some (finalEnvironment, finalState)) :
    ScopeCoverage finalEnvironment (parameterScope arguments types scope) := by
  induction arguments generalizing types sources environment state scope with
  | nil =>
      cases types with
      | cons => simp at arity
      | nil =>
          cases sources with
          | cons => cases bound
          | nil =>
              cases bound
              exact covered
  | cons argument arguments ih =>
      cases types with
      | nil => simp at arity
      | cons type types =>
          cases sources with
          | nil => cases bound
          | cons source sources =>
              have tail := ih (covered.addLocal argument.name type state.heap.length)
                (Nat.succ.inj arity) bound
              simpa only [parameterScope, List.zip_cons_cons, List.foldl_cons] using tail

end Solcore.Frontend.RustHull.Correspondence
end
