import Solcore.Frontend.RustHull.SemanticsCorrespondenceSupport
import Solcore.Frontend.RustHull.ExecutionCorrespondence

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
