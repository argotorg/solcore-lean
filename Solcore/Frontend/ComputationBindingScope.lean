import Solcore.Syntax.Term

/-! Source-only let-name exposure for the supported computation-body profile.
Explicit blocks and match arms are scope barriers; bare if branches are not. -/

set_option autoImplicit false

namespace Solcore.Frontend

inductive ExposesComputationLetName (name : String) : Syntax.Block → Prop where
  | binding {blockSpan letSpan : Syntax.SourceSpan} {identifier : Syntax.Identifier}
      {annotation : Option Syntax.TypeExpr} {initializer : Option Syntax.Expr}
      {rest : List Syntax.Statement} (spelling : identifier.value = name) :
      ExposesComputationLetName name
        ⟨blockSpan, ⟨letSpan, .letDecl identifier annotation initializer⟩ :: rest⟩
  | tail {blockSpan : Syntax.SourceSpan} {statement : Syntax.Statement}
      {rest : List Syntax.Statement}
      (exposed : ExposesComputationLetName name ⟨blockSpan, rest⟩) :
      ExposesComputationLetName name ⟨blockSpan, statement :: rest⟩
  | thenBranch {blockSpan ifSpan : Syntax.SourceSpan} {condition : Syntax.Expr}
      {thenBody : Syntax.Block} {elseBody : Option Syntax.Block} {rest : List Syntax.Statement}
      (exposed : ExposesComputationLetName name thenBody) :
      ExposesComputationLetName name
        ⟨blockSpan, ⟨ifSpan, .ifThen condition thenBody elseBody⟩ :: rest⟩
  | elseBranch {blockSpan ifSpan : Syntax.SourceSpan} {condition : Syntax.Expr}
      {thenBody elseBody : Syntax.Block} {rest : List Syntax.Statement}
      (exposed : ExposesComputationLetName name elseBody) :
      ExposesComputationLetName name
        ⟨blockSpan, ⟨ifSpan, .ifThen condition thenBody (some elseBody)⟩ :: rest⟩

def ComputationNamesProtected (names : List String) (body : Syntax.Block) : Prop :=
  ∀ name, ExposesComputationLetName name body → name ∉ names

def computationBlockPreservesNames (names : List String) (body : Syntax.Block) : Bool :=
  match body with
  | ⟨_, []⟩ => true
  | ⟨span, ⟨_, .letDecl identifier _ _⟩ :: rest⟩ =>
      decide (identifier.value ∉ names) && computationBlockPreservesNames names ⟨span, rest⟩
  | ⟨span, ⟨_, .ifThen _ thenBody none⟩ :: rest⟩ =>
      computationBlockPreservesNames names thenBody &&
        computationBlockPreservesNames names ⟨span, rest⟩
  | ⟨span, ⟨_, .ifThen _ thenBody (some elseBody)⟩ :: rest⟩ =>
      computationBlockPreservesNames names thenBody &&
        computationBlockPreservesNames names elseBody &&
        computationBlockPreservesNames names ⟨span, rest⟩
  | ⟨span, _ :: rest⟩ => computationBlockPreservesNames names ⟨span, rest⟩
termination_by sizeOf body
decreasing_by all_goals simp_wf; all_goals omega

end Solcore.Frontend
