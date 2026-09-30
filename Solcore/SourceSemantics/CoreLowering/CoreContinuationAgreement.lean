import Solcore.SourceSemantics.CoreLowering.CoreHelperInversion

/-! A finite prefix with a known value can be composed around, or removed
from, any finite continuation evaluation. This is an agreement between the
existing mathematical evaluations, with no executable evaluator added. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.CoreProof

open Core

structure ContinuationAgreement (environment : Environment) (store : Store) (whole : Expr)
    (nextEnvironment : Environment) (nextStore : Store) (next : Expr) : Prop where
  wrap : ∀ {result finalStore}, Evaluates nextEnvironment nextStore next result finalStore →
    Evaluates environment store whole result finalStore
  unwrap : ∀ {result finalStore}, Evaluates environment store whole result finalStore →
    Evaluates nextEnvironment nextStore next result finalStore

namespace ContinuationAgreement

theorem refl (environment : Environment) (store : Store) (code : Expr) :
    ContinuationAgreement environment store code environment store code := ⟨id, id⟩

theorem trans {environment middleEnvironment nextEnvironment : Environment}
    {store middleStore nextStore : Store} {whole middle next : Expr}
    (first : ContinuationAgreement environment store whole middleEnvironment middleStore middle)
    (second : ContinuationAgreement middleEnvironment middleStore middle nextEnvironment nextStore next) :
    ContinuationAgreement environment store whole nextEnvironment nextStore next :=
  ⟨fun evaluation => first.wrap (second.wrap evaluation), fun evaluation => second.unwrap (first.unwrap evaluation)⟩

theorem letE {environment : Environment} {before middle : Store} {initializer body : Expr} {value : Value}
    (evaluated : Evaluates environment before initializer value middle) :
    ContinuationAgreement environment before (.letE initializer body) (value :: environment) middle body := by
  constructor
  · exact fun body => .letE evaluated body
  · intro result finalStore evaluation
    obtain ⟨_, sized⟩ := evaluation_has_size evaluation
    obtain ⟨_, _, body⟩ := sized.let_body evaluated
    exact body.sound

theorem bind {environment : Environment} {before middle : Store} {computation body : Expr} {type : Ty} {value : Value}
    (evaluated : Evaluates environment before computation (.inRight .word value) middle) :
    ContinuationAgreement environment before (LanguageResult.bind type computation body) (value :: environment) middle body := by
  constructor
  · exact fun body => LanguageResult.bind_success type evaluated body
  · intro result finalStore evaluation
    obtain ⟨_, sized⟩ := evaluation_has_size evaluation
    obtain ⟨_, _, body⟩ := sized.bind_success evaluated
    exact body.sound

end ContinuationAgreement

end Solcore.SourceSemantics.CoreLowering.CoreProof
