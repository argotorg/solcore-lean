import Solcore.Resolved.Identity

/-!
Collision-free identities for compiler functions, traits, and implementations
in the whole-program frontend.

Source declarations and compiler-provided builtins inhabit disjoint variants.
The one-way declaration coercions keep source catalog construction concise,
while consumers that require source declarations must use `declaration?`
explicitly.
-/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Compiler-provided functions that do not have source declaration identities. -/
inductive BuiltinFunctionId where
  | integerSub
  | wordFromInteger
  | integerAdd
  | integerEq
  | integerLt
  | integerMul
  deriving Repr, BEq, DecidableEq

namespace BuiltinFunctionId

/-- Compiler functions implemented by the current frontend, in stable
append-only introduction order.  Name lookup derives from this list so
extending the identity type cannot silently leave a separate hand-written
lookup chain stale. -/
def all : List BuiltinFunctionId :=
  [.integerSub, .wordFromInteger, .integerAdd, .integerEq, .integerLt,
    .integerMul]

/-- Every compiler-function identity occurs in the lookup catalog. -/
theorem all_complete (function : BuiltinFunctionId) : function ∈ all := by
  cases function <;> simp [all]

/-- The append-only compiler-function catalog contains no repeated identity. -/
theorem all_nodup : all.Nodup := by
  simp [all]

end BuiltinFunctionId

/-- Compiler-provided traits that do not have source declaration identities. -/
inductive BuiltinTraitId where
  | int
  deriving Repr, BEq, DecidableEq

/-- A trait identity from either the compiler or a resolved source declaration. -/
inductive ProgramTraitId where
  | builtin (id : BuiltinTraitId)
  | declaration (id : Resolved.DeclarationId)
  deriving Repr, BEq, DecidableEq

instance : Coe Resolved.DeclarationId ProgramTraitId where
  coe := .declaration

namespace ProgramTraitId

/-- Recover the source declaration identity when this is a source trait. -/
def declaration? : ProgramTraitId → Option Resolved.DeclarationId
  | .builtin _ => none
  | .declaration id => some id

end ProgramTraitId

/-- Compiler-provided implementations that do not have source declarations. -/
inductive BuiltinImplId where
  | intInteger
  | intWord
  deriving Repr, BEq, DecidableEq

/-- An implementation identity from either the compiler or source catalog. -/
inductive ProgramImplId where
  | builtin (id : BuiltinImplId)
  | declaration (id : Resolved.DeclarationId)
  deriving Repr, BEq, DecidableEq

instance : Coe Resolved.DeclarationId ProgramImplId where
  coe := .declaration

namespace ProgramImplId

/-- Recover the source declaration identity when this is a source impl. -/
def declaration? : ProgramImplId → Option Resolved.DeclarationId
  | .builtin _ => none
  | .declaration id => some id

end ProgramImplId

end Solcore.Frontend
