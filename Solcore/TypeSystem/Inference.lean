import Solcore.TypeSystem.Scheme
import Solcore.TypeSystem.Unification

set_option autoImplicit false

namespace Solcore.TypeSystem

/-- Reusable inference state for later source-expression consumers. -/
structure InferState where
  next : Nat
  substitution : Substitution := []
  deriving Repr, DecidableEq

namespace InferState

def initial (next : Nat := 0) : InferState :=
  { next }

def resolve (state : InferState) (type : Ty) : Ty :=
  state.substitution.apply type

def fresh (state : InferState) : Ty × InferState :=
  (.variable ⟨state.next⟩, { state with next := state.next + 1 })

def instantiate (state : InferState) (scheme : Scheme) : Ty × InferState :=
  let (type, next) := scheme.instantiate state.next
  (state.resolve type, { state with next })

def instantiateDeclaration (state : InferState) (scheme : DeclarationScheme) :
    Ty × InferState :=
  let (type, next) := scheme.instantiate state.next
  (state.resolve type, { state with next })

/-- Unify under the current substitution and compose the new solution into it. -/
def unify (state : InferState) (left right : Ty) : Except Unification.Error InferState := do
  let update ← Unification.unifyTypes (state.resolve left) (state.resolve right)
  pure { state with substitution := update.compose state.substitution }

def solve (state : InferState) (constraints : List Constraint) :
    Except Unification.Error InferState := do
  let normalized := constraints.map (·.apply state.substitution)
  let update ← Unification.unify normalized
  pure { state with substitution := update.compose state.substitution }

end InferState

/-- A deliberately small expression language used to exercise the kernel end to end. -/
inductive Expr where
  | unit
  | bool (value : Bool)
  | word (value : Nat)
  | variable (name : String)
  | pair (left right : Expr)
  | lambda (parameter : String) (body : Expr)
  | application (function argument : Expr)
  | letE (name : String) (value body : Expr)
  | annotation (expression : Expr) (type : Ty)
  deriving Repr, DecidableEq

namespace Expr

/-- Every flexible variable written explicitly in an annotation lies below a
shared allocator bound. -/
def AnnotationsBelow (next : Nat) : Expr → Prop
  | .unit
  | .bool _
  | .word _
  | .variable _ => True
  | .pair left right
  | .application left right =>
      left.AnnotationsBelow next ∧ right.AnnotationsBelow next
  | .lambda _ body => body.AnnotationsBelow next
  | .letE _ value body =>
      value.AnnotationsBelow next ∧ body.AnnotationsBelow next
  | .annotation expression type =>
      expression.AnnotationsBelow next ∧ type.VariablesBelow next

/-- Annotation bounds are monotone in the allocator limit. -/
theorem AnnotationsBelow.weaken
    {expression : Expr} {lower upper : Nat}
    (below : expression.AnnotationsBelow lower) (bound : lower ≤ upper) :
    expression.AnnotationsBelow upper := by
  induction expression with
  | unit | bool | word | «variable» => trivial
  | pair left right leftInduction rightInduction
  | application left right leftInduction rightInduction =>
      exact ⟨leftInduction below.1, rightInduction below.2⟩
  | lambda parameter body induction =>
      exact induction below
  | letE name value body valueInduction bodyInduction =>
      exact ⟨valueInduction below.1, bodyInduction below.2⟩
  | annotation expression type induction =>
      exact ⟨induction below.1, below.2.weaken bound⟩

end Expr

namespace Inference

inductive Error where
  | unknownVariable (name : String)
  | unification (error : Unification.Error)
  deriving Repr, DecidableEq

structure Result where
  type : Ty
  state : InferState
  deriving Repr, DecidableEq

@[simp] private def liftUnification {α : Type} :
    Except Unification.Error α → Except Error α
  | .ok value => .ok value
  | .error error => .error (.unification error)

namespace Detail

/-- Internal recursive inference worker exposed only so the adjacent
properties module can establish structural invariants.  Ordinary callers use
`infer`. -/
def inferFrom (environment : Environment) :
    Expr → InferState → Except Error Result
  | .unit, state => .ok { type := .unit, state }
  | .bool _, state => .ok { type := .bool, state }
  | .word _, state => .ok { type := .word, state }
  | .variable name, state =>
      match environment.lookup? name with
      | none => .error (.unknownVariable name)
      | some scheme =>
          let (type, state) := state.instantiate scheme
          .ok { type, state }
  | .pair left right, state => do
      let leftResult ← inferFrom environment left state
      let rightEnvironment := environment.apply leftResult.state.substitution
      let rightResult ← inferFrom rightEnvironment right leftResult.state
      pure
        { type := .product
            (rightResult.state.resolve leftResult.type) rightResult.type
          state := rightResult.state }
  | .lambda parameter body, state => do
      let (parameterType, state) := state.fresh
      let bodyResult ← inferFrom ((parameter, .mono parameterType) :: environment) body state
      pure
        { type := .function
            (bodyResult.state.resolve parameterType) bodyResult.type
          state := bodyResult.state }
  | .application function argument, state => do
      let functionResult ← inferFrom environment function state
      let argumentEnvironment := environment.apply functionResult.state.substitution
      let argumentResult ← inferFrom argumentEnvironment argument functionResult.state
      let (resultType, state) := argumentResult.state.fresh
      let state ← liftUnification <| state.unify functionResult.type
        (.function argumentResult.type resultType)
      pure { type := state.resolve resultType, state }
  | .letE name value body, state => do
      let valueResult ← inferFrom environment value state
      let environment := environment.apply valueResult.state.substitution
      let valueType := valueResult.state.resolve valueResult.type
      let scheme := environment.generalize valueType
      inferFrom ((name, scheme) :: environment) body valueResult.state
  | .annotation expression expected, state => do
      let result ← inferFrom environment expression state
      let state ← liftUnification <| result.state.unify result.type expected
      pure { type := state.resolve expected, state }

end Detail

/-- Infer a type and retain the final state for incremental consumers. -/
def infer (environment : Environment) (expression : Expr) : Except Error Result := do
  let result ← Detail.inferFrom environment expression
    (.initial environment.nextVariable)
  pure { result with type := result.state.resolve result.type }

/-- The compact API used by callers which need only the inferred type. -/
def inferType (environment : Environment) (expression : Expr) : Except Error Ty := do
  pure (← infer environment expression).type

def inferClosed (expression : Expr) : Except Error Ty :=
  inferType [] expression

end Inference

end Solcore.TypeSystem
