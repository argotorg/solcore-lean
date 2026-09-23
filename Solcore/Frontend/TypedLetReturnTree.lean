import Solcore.Frontend.ReturnBody
import Solcore.Frontend.StructuralType
import Solcore.Frontend.LocalTypeInputs
import Solcore.Resolved.FreshIdentity
import Solcore.Frontend.TypedLetReturnBody
import Solcore.Frontend.LocalExpressionEvaluator
import Solcore.Frontend.LocalExpressionLookupProperties
import Solcore.Frontend.LocalReference
import Solcore.Frontend.LocalFunctionApplication
import Solcore.Frontend.LocalOwnerRenaming
import Solcore.Core.Machine
import Solcore.Resolved.LocalFragmentProperties
import Solcore.Frontend.TerminalReturnTree
import Solcore.Core.LocalFragment
import Solcore.Core.FuelResumptionProperties

/-! A separate value-free adapter for recursive typed prefixes and terminal
if/else branches. Siblings start in the same original scope; their local fresh
IDs need not be globally distinct. Structural annotations or independently inferred
initializer types reuse existing Core and entry records. Strict expression
prefixes discard their values without extending the original source scope.
Terminal lexical blocks retain their original child scope and exact Core. -/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Every written child is checked in its original scope. Named lets extend
that scope; discarded expressions instead weaken the unchanged tail Core under
a hidden Core binder, without introducing a source name or identity. -/
def elaborateTypedLetReturnTree? (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (inputs : LocalTypeInputs) (body : Syntax.Block) : Option (Core.Expr × Core.Ty) :=
  match body with
  | ⟨_, [⟨_, .returnStmt _⟩]⟩ => elaborateReturnBody? inputs.names inputs.context body
  | ⟨_, [⟨innerSpan, .block statements⟩]⟩ =>
      elaborateTypedLetReturnTree? types owner inputs ⟨innerSpan, statements⟩
  | ⟨blockSpan, ⟨_, .letDecl name (some annotation) (some initializer)⟩ :: rest⟩ =>
      if name.value ∉ inputs.names.map Prod.fst then do
        let declaredType ← interpretStructuralType? types annotation
        let (initializerCore, initializerType) ← elaborateLocalExpression? inputs.names inputs.context initializer
        if initializerType = declaredType then do
          let (tailCore, returnType) ← elaborateTypedLetReturnTree? types owner
            (inputs.bindFresh owner name.value declaredType) ⟨blockSpan, rest⟩
          return (.letE initializerCore tailCore, returnType)
        else none
      else none
  | ⟨blockSpan, ⟨_, .letDecl name none (some initializer)⟩ :: rest⟩ =>
      if name.value ∉ inputs.names.map Prod.fst then do
        let (initializerCore, initializerType) ← elaborateLocalExpression? inputs.names inputs.context initializer
        let (tailCore, returnType) ← elaborateTypedLetReturnTree? types owner
          (inputs.bindFresh owner name.value initializerType) ⟨blockSpan, rest⟩
        return (.letE initializerCore tailCore, returnType)
      else none
  | ⟨blockSpan, ⟨_, .expression expression true⟩ :: rest⟩ => do
      let (expressionCore, _) ← elaborateLocalExpression? inputs.names inputs.context expression
      let (tailCore, returnType) ← elaborateTypedLetReturnTree? types owner inputs ⟨blockSpan, rest⟩
      return (.letE expressionCore (tailCore.weakenAt 0), returnType)
  | ⟨_, [⟨_, .ifThen condition thenBody (some elseBody)⟩]⟩ => do
      let (conditionCore, conditionType) ← elaborateLocalExpression? inputs.names inputs.context condition
      if conditionType = .bool then do
        let (thenCore, thenType) ← elaborateTypedLetReturnTree? types owner inputs thenBody
        let (elseCore, elseType) ← elaborateTypedLetReturnTree? types owner inputs elseBody
        if thenType = elseType then return (.ifE conditionCore thenCore elseCore, thenType)
        else none
      else none
  | _ => none
termination_by sizeOf body

inductive TypedLetReturnTreeHasType (types : TypeNameTable) (owner : Resolved.DeclarationId) :
    LocalTypeInputs → Syntax.Block → Core.Ty → Prop where
  | single {inputs : LocalTypeInputs} {body : Syntax.Block} {type : Core.Ty}
      (child : ReturnBodyHasType inputs.names inputs.context body type) :
      TypedLetReturnTreeHasType types owner inputs body type
  | block {inputs : LocalTypeInputs} {outerSpan innerSpan : Syntax.SourceSpan}
      {statements : List Syntax.Statement} {type : Core.Ty}
      (child : TypedLetReturnTreeHasType types owner inputs ⟨innerSpan, statements⟩ type) :
      TypedLetReturnTreeHasType types owner inputs
        ⟨outerSpan, [⟨innerSpan, .block statements⟩]⟩ type
  | binding {inputs : LocalTypeInputs} {blockSpan letSpan : Syntax.SourceSpan}
      {name : Syntax.Identifier} {annotation : Syntax.TypeExpr} {initializer : Syntax.Expr}
      {rest : List Syntax.Statement} {declaredType returnType : Core.Ty}
      (meaning : StructuralTypeDenotes types annotation declaredType)
      (unused : name.value ∉ inputs.names.map Prod.fst)
      (initializerTyping : LocalExpressionHasType inputs.names inputs.context initializer declaredType)
      (tailTyping : TypedLetReturnTreeHasType types owner
        (inputs.bindFresh owner name.value declaredType) ⟨blockSpan, rest⟩ returnType) :
      TypedLetReturnTreeHasType types owner inputs
        ⟨blockSpan, ⟨letSpan, .letDecl name (some annotation) (some initializer)⟩ :: rest⟩ returnType
  | inferred {inputs : LocalTypeInputs} {blockSpan letSpan : Syntax.SourceSpan}
      {name : Syntax.Identifier} {initializer : Syntax.Expr} {rest : List Syntax.Statement}
      {inferredType returnType : Core.Ty}
      (unused : name.value ∉ inputs.names.map Prod.fst)
      (initializerTyping : LocalExpressionHasType inputs.names inputs.context initializer inferredType)
      (tailTyping : TypedLetReturnTreeHasType types owner
        (inputs.bindFresh owner name.value inferredType) ⟨blockSpan, rest⟩ returnType) :
      TypedLetReturnTreeHasType types owner inputs
        ⟨blockSpan, ⟨letSpan, .letDecl name none (some initializer)⟩ :: rest⟩ returnType
  | discard {inputs : LocalTypeInputs} {blockSpan statementSpan : Syntax.SourceSpan}
      {expression : Syntax.Expr} {rest : List Syntax.Statement} {discardedType returnType : Core.Ty}
      (expressionTyping : LocalExpressionHasType inputs.names inputs.context expression discardedType)
      (tailTyping : TypedLetReturnTreeHasType types owner inputs ⟨blockSpan, rest⟩ returnType) :
      TypedLetReturnTreeHasType types owner inputs
        ⟨blockSpan, ⟨statementSpan, .expression expression true⟩ :: rest⟩ returnType
  | conditional {inputs : LocalTypeInputs} {blockSpan ifSpan : Syntax.SourceSpan}
      {condition : Syntax.Expr} {thenBody elseBody : Syntax.Block} {type : Core.Ty}
      (conditionTyping : LocalExpressionHasType inputs.names inputs.context condition .bool)
      (thenTyping : TypedLetReturnTreeHasType types owner inputs thenBody type)
      (elseTyping : TypedLetReturnTreeHasType types owner inputs elseBody type) :
      TypedLetReturnTreeHasType types owner inputs
        ⟨blockSpan, [⟨ifSpan, .ifThen condition thenBody (some elseBody)⟩]⟩ type

/-- Original syntax and independently resolved, lowered and typed children
determine exact nested lets and both ordered branches, not merely the result type. -/
inductive TypedLetReturnTreeElaborates (types : TypeNameTable) (owner : Resolved.DeclarationId) :
    LocalTypeInputs → Syntax.Block → Core.Expr → Core.Ty → Prop where
  | single {inputs : LocalTypeInputs} {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
      (child : ReturnBodyElaborates inputs.names inputs.context body core type) :
      TypedLetReturnTreeElaborates types owner inputs body core type
  | block {inputs : LocalTypeInputs} {outerSpan innerSpan : Syntax.SourceSpan}
      {statements : List Syntax.Statement} {core : Core.Expr} {type : Core.Ty}
      (child : TypedLetReturnTreeElaborates types owner inputs ⟨innerSpan, statements⟩ core type) :
      TypedLetReturnTreeElaborates types owner inputs
        ⟨outerSpan, [⟨innerSpan, .block statements⟩]⟩ core type
  | binding {inputs : LocalTypeInputs} {blockSpan letSpan : Syntax.SourceSpan}
      {name : Syntax.Identifier} {annotation : Syntax.TypeExpr} {initializer : Syntax.Expr}
      {rest : List Syntax.Statement} {declaredType returnType : Core.Ty}
      {initializerResolved : Resolved.Expr} {initializerCore tailCore : Core.Expr}
      (meaning : StructuralTypeDenotes types annotation declaredType)
      (unused : name.value ∉ inputs.names.map Prod.fst)
      (resolution : ResolvesLocalExpression inputs.names initializer initializerResolved)
      (lowered : Resolved.Lowers inputs.ids initializerResolved initializerCore)
      (typing : Resolved.HasType inputs.context initializerResolved declaredType)
      (tailElaboration : TypedLetReturnTreeElaborates types owner
        (inputs.bindFresh owner name.value declaredType) ⟨blockSpan, rest⟩ tailCore returnType) :
      TypedLetReturnTreeElaborates types owner inputs
        ⟨blockSpan, ⟨letSpan, .letDecl name (some annotation) (some initializer)⟩ :: rest⟩
        (.letE initializerCore tailCore) returnType
  | inferred {inputs : LocalTypeInputs} {blockSpan letSpan : Syntax.SourceSpan}
      {name : Syntax.Identifier} {initializer : Syntax.Expr} {rest : List Syntax.Statement}
      {inferredType returnType : Core.Ty} {initializerResolved : Resolved.Expr}
      {initializerCore tailCore : Core.Expr}
      (unused : name.value ∉ inputs.names.map Prod.fst)
      (resolution : ResolvesLocalExpression inputs.names initializer initializerResolved)
      (lowered : Resolved.Lowers inputs.ids initializerResolved initializerCore)
      (typing : Resolved.HasType inputs.context initializerResolved inferredType)
      (tailElaboration : TypedLetReturnTreeElaborates types owner
        (inputs.bindFresh owner name.value inferredType) ⟨blockSpan, rest⟩ tailCore returnType) :
      TypedLetReturnTreeElaborates types owner inputs
        ⟨blockSpan, ⟨letSpan, .letDecl name none (some initializer)⟩ :: rest⟩
        (.letE initializerCore tailCore) returnType
  | discard {inputs : LocalTypeInputs} {blockSpan statementSpan : Syntax.SourceSpan}
      {expression : Syntax.Expr} {rest : List Syntax.Statement} {discardedType returnType : Core.Ty}
      {resolved : Resolved.Expr} {expressionCore tailCore : Core.Expr}
      (resolution : ResolvesLocalExpression inputs.names expression resolved)
      (lowered : Resolved.Lowers inputs.ids resolved expressionCore)
      (typing : Resolved.HasType inputs.context resolved discardedType)
      (tailElaboration : TypedLetReturnTreeElaborates types owner inputs ⟨blockSpan, rest⟩ tailCore returnType) :
      TypedLetReturnTreeElaborates types owner inputs
        ⟨blockSpan, ⟨statementSpan, .expression expression true⟩ :: rest⟩
        (.letE expressionCore (tailCore.weakenAt 0)) returnType
  | conditional {inputs : LocalTypeInputs} {blockSpan ifSpan : Syntax.SourceSpan}
      {condition : Syntax.Expr} {thenBody elseBody : Syntax.Block} {conditionResolved : Resolved.Expr}
      {conditionCore thenCore elseCore : Core.Expr} {type : Core.Ty}
      (resolution : ResolvesLocalExpression inputs.names condition conditionResolved)
      (lowered : Resolved.Lowers inputs.ids conditionResolved conditionCore)
      (typing : Resolved.HasType inputs.context conditionResolved .bool)
      (thenElaboration : TypedLetReturnTreeElaborates types owner inputs thenBody thenCore type)
      (elseElaboration : TypedLetReturnTreeElaborates types owner inputs elseBody elseCore type) :
      TypedLetReturnTreeElaborates types owner inputs
        ⟨blockSpan, [⟨ifSpan, .ifThen condition thenBody (some elseBody)⟩]⟩
        (.ifE conditionCore thenCore elseCore) type

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.TypedLetReturnTreeElaboration`
-/

/-! Exact independent provenance characterizes recursive typed let/return trees.
Child decomposition retains both source arms and each old-scope initializer. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem elaborateTypedLetReturnTree?_single (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (inputs : LocalTypeInputs) (returned : Option Syntax.Expr) (blockSpan returnSpan : Syntax.SourceSpan) :
    elaborateTypedLetReturnTree? types owner inputs ⟨blockSpan, [⟨returnSpan, .returnStmt returned⟩]⟩ =
      elaborateReturnBody? inputs.names inputs.context ⟨blockSpan, [⟨returnSpan, .returnStmt returned⟩]⟩ := by
  rw [elaborateTypedLetReturnTree?]

theorem elaborateTypedLetReturnTree?_block (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (inputs : LocalTypeInputs) (outerSpan innerSpan : Syntax.SourceSpan) (statements : List Syntax.Statement) :
    elaborateTypedLetReturnTree? types owner inputs ⟨outerSpan, [⟨innerSpan, .block statements⟩]⟩ =
      elaborateTypedLetReturnTree? types owner inputs ⟨innerSpan, statements⟩ := by
  rw [elaborateTypedLetReturnTree?]

theorem elaborateTypedLetReturnTree?_binding_children
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {blockSpan letSpan : Syntax.SourceSpan} {name : Syntax.Identifier}
    {annotation : Syntax.TypeExpr} {initializer : Syntax.Expr} {rest : List Syntax.Statement}
    {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTypedLetReturnTree? types owner inputs
      ⟨blockSpan, ⟨letSpan, .letDecl name (some annotation) (some initializer)⟩ :: rest⟩ = some (core, type)) :
    ∃ declaredType initializerCore tailCore,
      name.value ∉ inputs.names.map Prod.fst ∧ interpretStructuralType? types annotation = some declaredType ∧
      elaborateLocalExpression? inputs.names inputs.context initializer = some (initializerCore, declaredType) ∧
      elaborateTypedLetReturnTree? types owner (inputs.bindFresh owner name.value declaredType)
        ⟨blockSpan, rest⟩ = some (tailCore, type) ∧ core = .letE initializerCore tailCore := by
  rw [elaborateTypedLetReturnTree?] at accepted
  split at accepted
  next unused =>
    simp only [bind, Option.bind_eq_some_iff] at accepted
    obtain ⟨declaredType, meaning, ⟨initializerCore, initializerType⟩, initializerAccepted, remaining⟩ := accepted
    split at remaining
    next sameType =>
      change initializerType = declaredType at sameType
      subst initializerType
      simp only [Option.bind_eq_some_iff] at remaining
      obtain ⟨⟨tailCore, returnType⟩, tailAccepted, result⟩ := remaining
      change some (.letE initializerCore tailCore, returnType) = some (core, type) at result
      simp only [Option.some.injEq, Prod.mk.injEq] at result
      rcases result with ⟨rfl, rfl⟩
      exact ⟨declaredType, initializerCore, tailCore, unused, meaning, initializerAccepted, tailAccepted, rfl⟩
    next different => cases remaining
  next used => cases accepted

theorem elaborateTypedLetReturnTree?_inferred_children
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {blockSpan letSpan : Syntax.SourceSpan} {name : Syntax.Identifier}
    {initializer : Syntax.Expr} {rest : List Syntax.Statement} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTypedLetReturnTree? types owner inputs
      ⟨blockSpan, ⟨letSpan, .letDecl name none (some initializer)⟩ :: rest⟩ = some (core, type)) :
    ∃ initializerType initializerCore tailCore,
      name.value ∉ inputs.names.map Prod.fst ∧
      elaborateLocalExpression? inputs.names inputs.context initializer = some (initializerCore, initializerType) ∧
      elaborateTypedLetReturnTree? types owner (inputs.bindFresh owner name.value initializerType)
        ⟨blockSpan, rest⟩ = some (tailCore, type) ∧ core = .letE initializerCore tailCore := by
  rw [elaborateTypedLetReturnTree?] at accepted
  split at accepted
  next unused =>
    simp only [bind, Option.bind_eq_some_iff] at accepted
    obtain ⟨⟨initializerCore, initializerType⟩, initializerAccepted,
      ⟨tailCore, returnType⟩, tailAccepted, result⟩ := accepted
    change some (.letE initializerCore tailCore, returnType) = some (core, type) at result
    simp only [Option.some.injEq, Prod.mk.injEq] at result
    rcases result with ⟨rfl, rfl⟩
    exact ⟨initializerType, initializerCore, tailCore, unused, initializerAccepted, tailAccepted, rfl⟩
  next used => cases accepted

theorem elaborateTypedLetReturnTree?_conditional_children
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {blockSpan ifSpan : Syntax.SourceSpan} {condition : Syntax.Expr}
    {thenBody elseBody : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTypedLetReturnTree? types owner inputs
      ⟨blockSpan, [⟨ifSpan, .ifThen condition thenBody (some elseBody)⟩]⟩ = some (core, type)) :
    ∃ conditionCore thenCore elseCore,
      elaborateLocalExpression? inputs.names inputs.context condition = some (conditionCore, .bool) ∧
      elaborateTypedLetReturnTree? types owner inputs thenBody = some (thenCore, type) ∧
      elaborateTypedLetReturnTree? types owner inputs elseBody = some (elseCore, type) ∧
      core = .ifE conditionCore thenCore elseCore := by
  rw [elaborateTypedLetReturnTree?] at accepted
  simp only [bind, Option.bind_eq_some_iff] at accepted
  obtain ⟨⟨conditionCore, conditionType⟩, conditionAccepted, remaining⟩ := accepted
  split at remaining
  next conditionBool =>
    change conditionType = .bool at conditionBool
    subst conditionType
    simp only [Option.bind_eq_some_iff] at remaining
    obtain ⟨⟨thenCore, thenType⟩, thenAccepted, ⟨elseCore, elseType⟩, elseAccepted, result⟩ := remaining
    split at result
    next sameType =>
      change thenType = elseType at sameType
      subst elseType
      change some (.ifE conditionCore thenCore elseCore, thenType) = some (core, type) at result
      simp only [Option.some.injEq, Prod.mk.injEq] at result
      rcases result with ⟨rfl, rfl⟩
      exact ⟨conditionCore, thenCore, elseCore, conditionAccepted, thenAccepted, elseAccepted, rfl⟩
    next different => cases result
  next notBool => cases remaining

theorem elaborateTypedLetReturnTree?_discard_children
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {blockSpan statementSpan : Syntax.SourceSpan} {source : Syntax.Expr}
    {rest : List Syntax.Statement} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTypedLetReturnTree? types owner inputs
      ⟨blockSpan, ⟨statementSpan, .expression source true⟩ :: rest⟩ = some (core, type)) :
    ∃ expressionType expressionCore tailCore,
      elaborateLocalExpression? inputs.names inputs.context source = some (expressionCore, expressionType) ∧
      elaborateTypedLetReturnTree? types owner inputs ⟨blockSpan, rest⟩ = some (tailCore, type) ∧
      core = .letE expressionCore (tailCore.weakenAt 0) := by
  rw [elaborateTypedLetReturnTree?] at accepted
  simp only [bind, Option.bind_eq_some_iff] at accepted
  obtain ⟨⟨expressionCore, expressionType⟩, expressionAccepted,
    ⟨tailCore, returnType⟩, tailAccepted, result⟩ := accepted
  change some (.letE expressionCore (tailCore.weakenAt 0), returnType) = some (core, type) at result
  simp only [Option.some.injEq, Prod.mk.injEq] at result
  rcases result with ⟨rfl, rfl⟩
  exact ⟨expressionType, expressionCore, tailCore, expressionAccepted, tailAccepted, rfl⟩

theorem TypedLetReturnTreeElaborates.complete
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : TypedLetReturnTreeElaborates types owner inputs body core type) :
    elaborateTypedLetReturnTree? types owner inputs body = some (core, type) := by
  induction elaboration with
  | single child =>
      have accepted := child.complete
      cases child <;> simpa only [elaborateTypedLetReturnTree?] using accepted
  | block _ ih => simpa only [elaborateTypedLetReturnTree?_block] using ih
  | binding meaning unused resolution lowered typing _ ih =>
      have initializerAccepted := elaborateLocalExpression?_complete resolution
        (by simpa only [LocalTypeInputs.context_ids] using lowered) typing
      rw [elaborateTypedLetReturnTree?]
      simp only [if_pos unused, meaning.complete, initializerAccepted, ih, bind,
        Option.bind_some, ite_true, pure, Pure.pure]
  | inferred unused resolution lowered typing _ ih =>
      have initializerAccepted := elaborateLocalExpression?_complete resolution
        (by simpa only [LocalTypeInputs.context_ids] using lowered) typing
      rw [elaborateTypedLetReturnTree?]
      simp only [if_pos unused, initializerAccepted, ih, bind, Option.bind_some, pure, Pure.pure]
  | discard resolution lowered typing _ ih =>
      have expressionAccepted := elaborateLocalExpression?_complete resolution
        (by simpa only [LocalTypeInputs.context_ids] using lowered) typing
      rw [elaborateTypedLetReturnTree?]
      simp only [expressionAccepted, ih, bind, Option.bind_some, pure, Pure.pure]
  | conditional resolution lowered typing _ _ thenIH elseIH =>
      have conditionAccepted := elaborateLocalExpression?_complete resolution
        (by simpa only [LocalTypeInputs.context_ids] using lowered) typing
      rw [elaborateTypedLetReturnTree?]
      simp [conditionAccepted, thenIH, elseIH]

theorem elaborateTypedLetReturnTree?_elaborates
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTypedLetReturnTree? types owner inputs body = some (core, type)) :
    TypedLetReturnTreeElaborates types owner inputs body core type := by
  cases body with
  | mk blockSpan statements =>
      cases statements with
      | nil => simp only [elaborateTypedLetReturnTree?, reduceCtorEq] at accepted
      | cons statement rest =>
          cases statement with
          | mk statementSpan payload =>
              cases payload <;> try simp only [elaborateTypedLetReturnTree?, reduceCtorEq] at accepted
              case returnStmt returned =>
                cases rest with
                | nil => exact .single (elaborateReturnBody?_elaborates
                    (by simpa only [elaborateTypedLetReturnTree?_single] using accepted))
                | cons _ _ => simp only [elaborateTypedLetReturnTree?, reduceCtorEq] at accepted
              case block statements =>
                cases rest with
                | nil => exact .block (elaborateTypedLetReturnTree?_elaborates
                    (by simpa only [elaborateTypedLetReturnTree?_block] using accepted))
                | cons _ _ => simp only [elaborateTypedLetReturnTree?, reduceCtorEq] at accepted
              case letDecl name optionalType optionalInitializer =>
                cases optionalType with
                | none =>
                    cases optionalInitializer with
                    | none => simp only [elaborateTypedLetReturnTree?, reduceCtorEq] at accepted
                    | some initializer =>
                        obtain ⟨initializerType, initializerCore, tailCore, unused,
                          initializerAccepted, tailAccepted, rfl⟩ :=
                          elaborateTypedLetReturnTree?_inferred_children accepted
                        obtain ⟨resolved, resolution, lowered, typing⟩ := elaborateLocalExpression?_sound initializerAccepted
                        exact .inferred unused resolution
                          (by simpa only [LocalTypeInputs.context_ids] using lowered) typing
                          (elaborateTypedLetReturnTree?_elaborates tailAccepted)
                | some annotation =>
                    cases optionalInitializer with
                    | none => simp only [elaborateTypedLetReturnTree?, reduceCtorEq] at accepted
                    | some initializer =>
                        obtain ⟨declaredType, initializerCore, tailCore, unused, meaning,
                          initializerAccepted, tailAccepted, rfl⟩ :=
                          elaborateTypedLetReturnTree?_binding_children accepted
                        obtain ⟨resolved, resolution, lowered, typing⟩ := elaborateLocalExpression?_sound initializerAccepted
                        exact .binding (interpretStructuralType?_sound meaning) unused resolution
                          (by simpa only [LocalTypeInputs.context_ids] using lowered) typing
                          (elaborateTypedLetReturnTree?_elaborates tailAccepted)
              case ifThen condition thenBody optionalElse =>
                cases rest with
                | cons _ _ => simp only [elaborateTypedLetReturnTree?, reduceCtorEq] at accepted
                | nil =>
                    cases optionalElse with
                    | none => simp only [elaborateTypedLetReturnTree?, reduceCtorEq] at accepted
                    | some elseBody =>
                        obtain ⟨conditionCore, thenCore, elseCore, conditionAccepted,
                          thenAccepted, elseAccepted, rfl⟩ := elaborateTypedLetReturnTree?_conditional_children accepted
                        obtain ⟨resolved, resolution, lowered, typing⟩ := elaborateLocalExpression?_sound conditionAccepted
                        exact .conditional resolution
                          (by simpa only [LocalTypeInputs.context_ids] using lowered) typing
                          (elaborateTypedLetReturnTree?_elaborates thenAccepted)
                          (elaborateTypedLetReturnTree?_elaborates elseAccepted)
              case expression source trailingSemicolon =>
                cases trailingSemicolon with
                | false => simp only [elaborateTypedLetReturnTree?, reduceCtorEq] at accepted
                | true =>
                    obtain ⟨expressionType, expressionCore, tailCore,
                      expressionAccepted, tailAccepted, rfl⟩ := elaborateTypedLetReturnTree?_discard_children accepted
                    obtain ⟨resolved, resolution, lowered, typing⟩ := elaborateLocalExpression?_sound expressionAccepted
                    exact .discard resolution (by simpa only [LocalTypeInputs.context_ids] using lowered) typing
                      (elaborateTypedLetReturnTree?_elaborates tailAccepted)
termination_by sizeOf body

theorem elaborateTypedLetReturnTree?_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty} :
    elaborateTypedLetReturnTree? types owner inputs body = some (core, type) ↔
      TypedLetReturnTreeElaborates types owner inputs body core type :=
  ⟨elaborateTypedLetReturnTree?_elaborates, TypedLetReturnTreeElaborates.complete⟩

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.TypedLetReturnTreeEvaluation`
-/

/-! Independent recursive paths evaluate strict initializers in the old scope
and only the selected conditional arm. Raw paths do not imply whole acceptance
or a source shadowing policy. Fresh IDs are relative to the current name table;
discard prefixes evaluate their tails without allocating any source identity.
Terminal blocks retain the original inner scope, stores and computation. -/

set_option autoImplicit false

namespace Solcore.Frontend

inductive TypedLetReturnTreeEvaluates (owner : Resolved.DeclarationId) :
    LocalNameTable → Resolved.Environment → Core.Store → Syntax.Block → Core.Value → Core.Store → Prop where
  | single {table : LocalNameTable} {environment : Resolved.Environment}
      {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value}
      (child : ReturnBodyEvaluates table environment initialStore body value finalStore) :
      TypedLetReturnTreeEvaluates owner table environment initialStore body value finalStore
  | block {table : LocalNameTable} {environment : Resolved.Environment}
      {outerSpan innerSpan : Syntax.SourceSpan} {statements : List Syntax.Statement}
      {initialStore finalStore : Core.Store} {value : Core.Value}
      (child : TypedLetReturnTreeEvaluates owner table environment initialStore
        ⟨innerSpan, statements⟩ value finalStore) :
      TypedLetReturnTreeEvaluates owner table environment initialStore
        ⟨outerSpan, [⟨innerSpan, .block statements⟩]⟩ value finalStore
  | binding {table : LocalNameTable} {environment : Resolved.Environment}
      {blockSpan letSpan : Syntax.SourceSpan} {name : Syntax.Identifier}
      {annotation : Syntax.TypeExpr} {initializer : Syntax.Expr} {rest : List Syntax.Statement}
      {initialStore middleStore finalStore : Core.Store} {boundValue value : Core.Value}
      (initializerEvaluation : LocalExpressionEvaluates table environment initialStore initializer boundValue middleStore)
      (tailEvaluation : TypedLetReturnTreeEvaluates owner
        ((name.value, Resolved.freshLocalId owner (table.map Prod.snd)) :: table)
        ((Resolved.freshLocalId owner (table.map Prod.snd), boundValue) :: environment)
        middleStore ⟨blockSpan, rest⟩ value finalStore) :
      TypedLetReturnTreeEvaluates owner table environment initialStore
        ⟨blockSpan, ⟨letSpan, .letDecl name (some annotation) (some initializer)⟩ :: rest⟩ value finalStore
  | inferred {table : LocalNameTable} {environment : Resolved.Environment}
      {blockSpan letSpan : Syntax.SourceSpan} {name : Syntax.Identifier}
      {initializer : Syntax.Expr} {rest : List Syntax.Statement}
      {initialStore middleStore finalStore : Core.Store} {boundValue value : Core.Value}
      (initializerEvaluation : LocalExpressionEvaluates table environment initialStore initializer boundValue middleStore)
      (tailEvaluation : TypedLetReturnTreeEvaluates owner
        ((name.value, Resolved.freshLocalId owner (table.map Prod.snd)) :: table)
        ((Resolved.freshLocalId owner (table.map Prod.snd), boundValue) :: environment)
        middleStore ⟨blockSpan, rest⟩ value finalStore) :
      TypedLetReturnTreeEvaluates owner table environment initialStore
        ⟨blockSpan, ⟨letSpan, .letDecl name none (some initializer)⟩ :: rest⟩ value finalStore
  | discard {table : LocalNameTable} {environment : Resolved.Environment}
      {blockSpan statementSpan : Syntax.SourceSpan} {expression : Syntax.Expr} {rest : List Syntax.Statement}
      {initialStore middleStore finalStore : Core.Store} {discardedValue value : Core.Value}
      (expressionEvaluation : LocalExpressionEvaluates table environment initialStore expression discardedValue middleStore)
      (tailEvaluation : TypedLetReturnTreeEvaluates owner table environment middleStore
        ⟨blockSpan, rest⟩ value finalStore) :
      TypedLetReturnTreeEvaluates owner table environment initialStore
        ⟨blockSpan, ⟨statementSpan, .expression expression true⟩ :: rest⟩ value finalStore
  | ifTrue {table : LocalNameTable} {environment : Resolved.Environment}
      {blockSpan statementSpan : Syntax.SourceSpan} {condition : Syntax.Expr}
      {thenBody elseBody : Syntax.Block} {initialStore middleStore finalStore : Core.Store} {value : Core.Value}
      (conditionEvaluation : LocalExpressionEvaluates table environment initialStore condition (.bool true) middleStore)
      (branchEvaluation : TypedLetReturnTreeEvaluates owner table environment middleStore thenBody value finalStore) :
      TypedLetReturnTreeEvaluates owner table environment initialStore
        ⟨blockSpan, [⟨statementSpan, .ifThen condition thenBody (some elseBody)⟩]⟩ value finalStore
  | ifFalse {table : LocalNameTable} {environment : Resolved.Environment}
      {blockSpan statementSpan : Syntax.SourceSpan} {condition : Syntax.Expr}
      {thenBody elseBody : Syntax.Block} {initialStore middleStore finalStore : Core.Store} {value : Core.Value}
      (conditionEvaluation : LocalExpressionEvaluates table environment initialStore condition (.bool false) middleStore)
      (branchEvaluation : TypedLetReturnTreeEvaluates owner table environment middleStore elseBody value finalStore) :
      TypedLetReturnTreeEvaluates owner table environment initialStore
        ⟨blockSpan, [⟨statementSpan, .ifThen condition thenBody (some elseBody)⟩]⟩ value finalStore

/-- Selected lets, discards and conditionals each add two existing Core transitions.
An unused initializer or discarded expression still contributes its complete cost.
A terminal block has the exact cost of its child, with no added transition. -/
inductive TypedLetReturnTreeEvaluatesWithCost (owner : Resolved.DeclarationId) :
    LocalNameTable → Resolved.Environment → Core.Store → Syntax.Block → Core.Value → Core.Store → Nat → Prop where
  | single {table : LocalNameTable} {environment : Resolved.Environment}
      {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
      (child : ReturnBodyEvaluatesWithCost table environment initialStore body value finalStore cost) :
      TypedLetReturnTreeEvaluatesWithCost owner table environment initialStore body value finalStore cost
  | block {table : LocalNameTable} {environment : Resolved.Environment}
      {outerSpan innerSpan : Syntax.SourceSpan} {statements : List Syntax.Statement}
      {initialStore finalStore : Core.Store} {value : Core.Value} {cost : Nat}
      (child : TypedLetReturnTreeEvaluatesWithCost owner table environment initialStore
        ⟨innerSpan, statements⟩ value finalStore cost) :
      TypedLetReturnTreeEvaluatesWithCost owner table environment initialStore
        ⟨outerSpan, [⟨innerSpan, .block statements⟩]⟩ value finalStore cost
  | binding {table : LocalNameTable} {environment : Resolved.Environment}
      {blockSpan letSpan : Syntax.SourceSpan} {name : Syntax.Identifier}
      {annotation : Syntax.TypeExpr} {initializer : Syntax.Expr} {rest : List Syntax.Statement}
      {initialStore middleStore finalStore : Core.Store} {boundValue value : Core.Value}
      {initializerCost tailCost : Nat}
      (initializerEvaluation : LocalExpressionEvaluatesWithCost table environment
        initialStore initializer boundValue middleStore initializerCost)
      (tailEvaluation : TypedLetReturnTreeEvaluatesWithCost owner
        ((name.value, Resolved.freshLocalId owner (table.map Prod.snd)) :: table)
        ((Resolved.freshLocalId owner (table.map Prod.snd), boundValue) :: environment)
        middleStore ⟨blockSpan, rest⟩ value finalStore tailCost) :
      TypedLetReturnTreeEvaluatesWithCost owner table environment initialStore
        ⟨blockSpan, ⟨letSpan, .letDecl name (some annotation) (some initializer)⟩ :: rest⟩
        value finalStore (initializerCost + tailCost + 2)
  | inferred {table : LocalNameTable} {environment : Resolved.Environment}
      {blockSpan letSpan : Syntax.SourceSpan} {name : Syntax.Identifier}
      {initializer : Syntax.Expr} {rest : List Syntax.Statement}
      {initialStore middleStore finalStore : Core.Store} {boundValue value : Core.Value}
      {initializerCost tailCost : Nat}
      (initializerEvaluation : LocalExpressionEvaluatesWithCost table environment
        initialStore initializer boundValue middleStore initializerCost)
      (tailEvaluation : TypedLetReturnTreeEvaluatesWithCost owner
        ((name.value, Resolved.freshLocalId owner (table.map Prod.snd)) :: table)
        ((Resolved.freshLocalId owner (table.map Prod.snd), boundValue) :: environment)
        middleStore ⟨blockSpan, rest⟩ value finalStore tailCost) :
      TypedLetReturnTreeEvaluatesWithCost owner table environment initialStore
        ⟨blockSpan, ⟨letSpan, .letDecl name none (some initializer)⟩ :: rest⟩
        value finalStore (initializerCost + tailCost + 2)
  | discard {table : LocalNameTable} {environment : Resolved.Environment}
      {blockSpan statementSpan : Syntax.SourceSpan} {expression : Syntax.Expr} {rest : List Syntax.Statement}
      {initialStore middleStore finalStore : Core.Store} {discardedValue value : Core.Value}
      {expressionCost tailCost : Nat}
      (expressionEvaluation : LocalExpressionEvaluatesWithCost table environment
        initialStore expression discardedValue middleStore expressionCost)
      (tailEvaluation : TypedLetReturnTreeEvaluatesWithCost owner table environment
        middleStore ⟨blockSpan, rest⟩ value finalStore tailCost) :
      TypedLetReturnTreeEvaluatesWithCost owner table environment initialStore
        ⟨blockSpan, ⟨statementSpan, .expression expression true⟩ :: rest⟩
        value finalStore (expressionCost + tailCost + 2)
  | ifTrue {table : LocalNameTable} {environment : Resolved.Environment}
      {blockSpan statementSpan : Syntax.SourceSpan} {condition : Syntax.Expr}
      {thenBody elseBody : Syntax.Block} {initialStore middleStore finalStore : Core.Store}
      {value : Core.Value} {conditionCost branchCost : Nat}
      (conditionEvaluation : LocalExpressionEvaluatesWithCost table environment
        initialStore condition (.bool true) middleStore conditionCost)
      (branchEvaluation : TypedLetReturnTreeEvaluatesWithCost owner table environment
        middleStore thenBody value finalStore branchCost) :
      TypedLetReturnTreeEvaluatesWithCost owner table environment initialStore
        ⟨blockSpan, [⟨statementSpan, .ifThen condition thenBody (some elseBody)⟩]⟩
        value finalStore (conditionCost + branchCost + 2)
  | ifFalse {table : LocalNameTable} {environment : Resolved.Environment}
      {blockSpan statementSpan : Syntax.SourceSpan} {condition : Syntax.Expr}
      {thenBody elseBody : Syntax.Block} {initialStore middleStore finalStore : Core.Store}
      {value : Core.Value} {conditionCost branchCost : Nat}
      (conditionEvaluation : LocalExpressionEvaluatesWithCost table environment
        initialStore condition (.bool false) middleStore conditionCost)
      (branchEvaluation : TypedLetReturnTreeEvaluatesWithCost owner table environment
        middleStore elseBody value finalStore branchCost) :
      TypedLetReturnTreeEvaluatesWithCost owner table environment initialStore
        ⟨blockSpan, [⟨statementSpan, .ifThen condition thenBody (some elseBody)⟩]⟩
        value finalStore (conditionCost + branchCost + 2)

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.TypedLetReturnTreeEvaluationEmbeddingProperties`
-/

/-! Old selected paths embed with their exact value, stores and cost.
No annotation meaning, runtime typing or whole-source acceptance is added. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem TerminalReturnTreeEvaluates.typedLetReturnTree
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value}
    (evaluation : TerminalReturnTreeEvaluates table environment initialStore body value finalStore)
    (owner : Resolved.DeclarationId) :
    TypedLetReturnTreeEvaluates owner table environment initialStore body value finalStore := by
  induction evaluation with
  | single child => exact .single child
  | ifTrue condition _ ih => exact .ifTrue condition ih
  | ifFalse condition _ ih => exact .ifFalse condition ih

theorem TerminalReturnTreeEvaluatesWithCost.typedLetReturnTree
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : TerminalReturnTreeEvaluatesWithCost table environment initialStore body value finalStore cost)
    (owner : Resolved.DeclarationId) :
    TypedLetReturnTreeEvaluatesWithCost owner table environment initialStore body value finalStore cost := by
  induction evaluation with
  | single child => exact .single child
  | ifTrue condition _ ih => exact .ifTrue condition ih
  | ifFalse condition _ ih => exact .ifFalse condition ih

theorem TypedLetReturnBodyEvaluates.returnTree
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value}
    (evaluation : TypedLetReturnBodyEvaluates owner table environment initialStore body value finalStore) :
    TypedLetReturnTreeEvaluates owner table environment initialStore body value finalStore := by
  induction evaluation with
  | terminal child => exact child.typedLetReturnTree owner
  | binding initializer _ ih => exact .binding initializer ih

theorem TypedLetReturnBodyEvaluatesWithCost.returnTree
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : TypedLetReturnBodyEvaluatesWithCost owner table environment initialStore body value finalStore cost) :
    TypedLetReturnTreeEvaluatesWithCost owner table environment initialStore body value finalStore cost := by
  induction evaluation with
  | terminal child => exact child.typedLetReturnTree owner
  | binding initializer _ ih => exact .binding initializer ih

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.TypedLetReturnTreeEvaluationProperties`
-/

/-! Raw store/value/cost laws require no checking or runtime type assumptions.
Whole typing gives existence only with an actual aligned, typed environment;
each strict initializer supplies the real value used in its extended tail. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem TypedLetReturnTreeEvaluates.store_eq
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value}
    (evaluation : TypedLetReturnTreeEvaluates owner table environment initialStore body value finalStore) :
    finalStore = initialStore := by
  induction evaluation with
  | single child => exact child.store_eq
  | block _ ih => exact ih
  | binding child _ ih | inferred child _ ih | discard child _ ih | ifTrue child _ ih | ifFalse child _ ih =>
      exact ih.trans child.store_eq

theorem TypedLetReturnTreeEvaluates.deterministic
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore : Core.Store} {body : Syntax.Block}
    {left right : Core.Value} {leftStore rightStore : Core.Store}
    (first : TypedLetReturnTreeEvaluates owner table environment initialStore body left leftStore)
    (second : TypedLetReturnTreeEvaluates owner table environment initialStore body right rightStore) :
    left = right ∧ leftStore = rightStore := by
  induction first generalizing right rightStore with
  | single child =>
      cases second with
      | single other => exact child.deterministic other
      | block _ | binding _ _ | inferred _ _ | discard _ _ | ifTrue _ _ | ifFalse _ _ => cases child
  | block _ ih =>
      cases second with
      | single other => cases other
      | block other => exact ih other
  | binding initializer _ ih =>
      cases second with
      | single other => cases other
      | binding otherInitializer otherTail =>
          obtain ⟨rfl, rfl⟩ := initializer.deterministic otherInitializer
          exact ih otherTail
  | inferred initializer _ ih =>
      cases second with
      | single other => cases other
      | inferred otherInitializer otherTail =>
          obtain ⟨rfl, rfl⟩ := initializer.deterministic otherInitializer
          exact ih otherTail
  | discard expression _ ih =>
      cases second with
      | single other => cases other
      | discard otherExpression otherTail =>
          obtain ⟨_, rfl⟩ := expression.deterministic otherExpression
          exact ih otherTail
  | ifTrue condition _ ih =>
      cases second with
      | single other => cases other
      | ifTrue otherCondition otherBranch =>
          obtain ⟨_, rfl⟩ := condition.deterministic otherCondition
          exact ih otherBranch
      | ifFalse otherCondition _ => cases (condition.deterministic otherCondition).1
  | ifFalse condition _ ih =>
      cases second with
      | single other => cases other
      | ifTrue otherCondition _ => cases (condition.deterministic otherCondition).1
      | ifFalse otherCondition otherBranch =>
          obtain ⟨_, rfl⟩ := condition.deterministic otherCondition
          exact ih otherBranch

theorem TypedLetReturnTreeHasType.evaluates
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {environment : Resolved.Environment} {body : Syntax.Block} {type : Core.Ty}
    (typing : TypedLetReturnTreeHasType types owner inputs body type)
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids inputs.context)
    (environmentTyped : Core.EnvironmentHasTypes
      (Resolved.LocalScope.values environment) (Resolved.LocalScope.values inputs.context)) (store : Core.Store) :
    ∃ value, TypedLetReturnTreeEvaluates owner inputs.names environment store body value store ∧
      Core.ValueHasType value type := by
  induction typing generalizing environment with
  | single child =>
      obtain ⟨value, evaluation, typed⟩ := child.evaluates sameIds environmentTyped store
      exact ⟨value, .single evaluation, typed⟩
  | block _ ih =>
      obtain ⟨value, evaluation, typed⟩ := ih sameIds environmentTyped
      exact ⟨value, .block evaluation, typed⟩
  | @binding inputs blockSpan letSpan name annotation initializer rest declaredType returnType
      _ _ initializerTyping _ ih =>
      obtain ⟨boundValue, initializerEvaluation, boundTyped⟩ :=
        initializerTyping.evaluates sameIds environmentTyped store
      have tailIds : Resolved.LocalScope.ids
          ((Resolved.freshLocalId owner inputs.ids, boundValue) :: environment) =
          Resolved.LocalScope.ids (inputs.bindFresh owner name.value declaredType).context := by
        simpa only [LocalTypeInputs.bindFresh_context, Resolved.LocalScope.ids, List.map_cons, Prod.fst]
          using congrArg (Resolved.freshLocalId owner inputs.ids :: ·) sameIds
      have tailTyped : Core.EnvironmentHasTypes
          (Resolved.LocalScope.values ((Resolved.freshLocalId owner inputs.ids, boundValue) :: environment))
          (Resolved.LocalScope.values (inputs.bindFresh owner name.value declaredType).context) :=
        .cons boundTyped environmentTyped
      obtain ⟨value, tailEvaluation, valueTyped⟩ := ih tailIds tailTyped
      refine ⟨value, .binding initializerEvaluation ?_, valueTyped⟩
      simpa only [LocalTypeInputs.bindFresh_names, LocalTypeInputs.names_ids] using tailEvaluation
  | @inferred inputs blockSpan letSpan name initializer rest inferredType returnType
      _ initializerTyping _ ih =>
      obtain ⟨boundValue, initializerEvaluation, boundTyped⟩ :=
        initializerTyping.evaluates sameIds environmentTyped store
      have tailIds : Resolved.LocalScope.ids
          ((Resolved.freshLocalId owner inputs.ids, boundValue) :: environment) =
          Resolved.LocalScope.ids (inputs.bindFresh owner name.value inferredType).context := by
        simpa only [LocalTypeInputs.bindFresh_context, Resolved.LocalScope.ids, List.map_cons, Prod.fst]
          using congrArg (Resolved.freshLocalId owner inputs.ids :: ·) sameIds
      have tailTyped : Core.EnvironmentHasTypes
          (Resolved.LocalScope.values ((Resolved.freshLocalId owner inputs.ids, boundValue) :: environment))
          (Resolved.LocalScope.values (inputs.bindFresh owner name.value inferredType).context) :=
        .cons boundTyped environmentTyped
      obtain ⟨value, tailEvaluation, valueTyped⟩ := ih tailIds tailTyped
      refine ⟨value, .inferred initializerEvaluation ?_, valueTyped⟩
      simpa only [LocalTypeInputs.bindFresh_names, LocalTypeInputs.names_ids] using tailEvaluation
  | discard expressionTyping _ ih =>
      obtain ⟨_, expressionEvaluation, _⟩ := expressionTyping.evaluates sameIds environmentTyped store
      obtain ⟨value, tailEvaluation, valueTyped⟩ := ih sameIds environmentTyped
      exact ⟨value, .discard expressionEvaluation tailEvaluation, valueTyped⟩
  | conditional conditionTyping _ _ thenIH elseIH =>
      obtain ⟨conditionValue, conditionEvaluation, conditionTyped⟩ :=
        conditionTyping.evaluates sameIds environmentTyped store
      obtain ⟨choice, rfl⟩ := conditionTyped.bool_shape
      cases choice with
      | false =>
          obtain ⟨value, evaluation, typed⟩ := elseIH sameIds environmentTyped
          exact ⟨value, .ifFalse conditionEvaluation evaluation, typed⟩
      | true =>
          obtain ⟨value, evaluation, typed⟩ := thenIH sameIds environmentTyped
          exact ⟨value, .ifTrue conditionEvaluation evaluation, typed⟩

theorem TypedLetReturnTreeEvaluates.preserves_type
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {environment : Resolved.Environment} {body : Syntax.Block} {type : Core.Ty}
    {value : Core.Value} {initialStore finalStore : Core.Store}
    (evaluation : TypedLetReturnTreeEvaluates owner inputs.names environment initialStore body value finalStore)
    (typing : TypedLetReturnTreeHasType types owner inputs body type)
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids inputs.context)
    (environmentTyped : Core.EnvironmentHasTypes
      (Resolved.LocalScope.values environment) (Resolved.LocalScope.values inputs.context)) :
    Core.ValueHasType value type ∧ finalStore = initialStore := by
  obtain ⟨other, evaluated, typed⟩ := typing.evaluates sameIds environmentTyped initialStore
  obtain ⟨rfl, sameStore⟩ := evaluation.deterministic evaluated
  exact ⟨typed, sameStore⟩

theorem TypedLetReturnTreeEvaluatesWithCost.erase
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : TypedLetReturnTreeEvaluatesWithCost owner table environment initialStore body value finalStore cost) :
    TypedLetReturnTreeEvaluates owner table environment initialStore body value finalStore := by
  induction evaluation with
  | single child => exact .single child.erase
  | block _ ih => exact .block ih
  | binding initializer _ ih => exact .binding initializer.erase ih
  | inferred initializer _ ih => exact .inferred initializer.erase ih
  | discard expression _ ih => exact .discard expression.erase ih
  | ifTrue condition _ ih => exact .ifTrue condition.erase ih
  | ifFalse condition _ ih => exact .ifFalse condition.erase ih

theorem TypedLetReturnTreeEvaluates.exists_cost
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value}
    (evaluation : TypedLetReturnTreeEvaluates owner table environment initialStore body value finalStore) :
    ∃ cost, TypedLetReturnTreeEvaluatesWithCost owner table environment initialStore body value finalStore cost := by
  induction evaluation with
  | single child =>
      obtain ⟨cost, costed⟩ := child.exists_cost
      exact ⟨cost, .single costed⟩
  | block _ ih =>
      obtain ⟨cost, costed⟩ := ih
      exact ⟨cost, .block costed⟩
  | binding initializer _ ih =>
      obtain ⟨_, initializerCost⟩ := initializer.exists_cost
      obtain ⟨_, tailCost⟩ := ih
      exact ⟨_, .binding initializerCost tailCost⟩
  | inferred initializer _ ih =>
      obtain ⟨_, initializerCost⟩ := initializer.exists_cost
      obtain ⟨_, tailCost⟩ := ih
      exact ⟨_, .inferred initializerCost tailCost⟩
  | discard expression _ ih =>
      obtain ⟨_, expressionCost⟩ := expression.exists_cost
      obtain ⟨_, tailCost⟩ := ih
      exact ⟨_, .discard expressionCost tailCost⟩
  | ifTrue condition _ ih =>
      obtain ⟨_, conditionCost⟩ := condition.exists_cost
      obtain ⟨_, branchCost⟩ := ih
      exact ⟨_, .ifTrue conditionCost branchCost⟩
  | ifFalse condition _ ih =>
      obtain ⟨_, conditionCost⟩ := condition.exists_cost
      obtain ⟨_, branchCost⟩ := ih
      exact ⟨_, .ifFalse conditionCost branchCost⟩

theorem typedLetReturnTreeEvaluates_iff_exists_cost
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} :
    TypedLetReturnTreeEvaluates owner table environment initialStore body value finalStore ↔
      ∃ cost, TypedLetReturnTreeEvaluatesWithCost owner table environment initialStore body value finalStore cost :=
  ⟨TypedLetReturnTreeEvaluates.exists_cost, fun ⟨_, evaluation⟩ => evaluation.erase⟩

theorem TypedLetReturnTreeEvaluatesWithCost.store_eq
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : TypedLetReturnTreeEvaluatesWithCost owner table environment initialStore body value finalStore cost) :
    finalStore = initialStore := evaluation.erase.store_eq

theorem TypedLetReturnTreeEvaluatesWithCost.cost_pos
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : TypedLetReturnTreeEvaluatesWithCost owner table environment initialStore body value finalStore cost) :
    0 < cost := by
  induction evaluation with
  | single child => exact child.cost_pos
  | block _ ih => exact ih
  | binding _ _ _ | inferred _ _ _ | discard _ _ _ | ifTrue _ _ _ | ifFalse _ _ _ => omega

theorem TypedLetReturnTreeEvaluatesWithCost.deterministic
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore : Core.Store} {body : Syntax.Block} {left right : Core.Value}
    {leftStore rightStore : Core.Store} {leftCost rightCost : Nat}
    (first : TypedLetReturnTreeEvaluatesWithCost owner table environment initialStore body left leftStore leftCost)
    (second : TypedLetReturnTreeEvaluatesWithCost owner table environment initialStore body right rightStore rightCost) :
    left = right ∧ leftStore = rightStore ∧ leftCost = rightCost := by
  induction first generalizing right rightStore rightCost with
  | single child =>
      cases second with
      | single other => exact child.deterministic other
      | block _ | binding _ _ | inferred _ _ | discard _ _ | ifTrue _ _ | ifFalse _ _ => cases child
  | block _ ih =>
      cases second with
      | single other => cases other
      | block other => exact ih other
  | binding initializer _ ih =>
      cases second with
      | single other => cases other
      | binding otherInitializer otherTail =>
          obtain ⟨rfl, rfl, rfl⟩ := initializer.deterministic otherInitializer
          obtain ⟨rfl, rfl, rfl⟩ := ih otherTail
          exact ⟨rfl, rfl, rfl⟩
  | inferred initializer _ ih =>
      cases second with
      | single other => cases other
      | inferred otherInitializer otherTail =>
          obtain ⟨rfl, rfl, rfl⟩ := initializer.deterministic otherInitializer
          obtain ⟨rfl, rfl, rfl⟩ := ih otherTail
          exact ⟨rfl, rfl, rfl⟩
  | discard expression _ ih =>
      cases second with
      | single other => cases other
      | discard otherExpression otherTail =>
          obtain ⟨_, rfl, rfl⟩ := expression.deterministic otherExpression
          obtain ⟨rfl, rfl, rfl⟩ := ih otherTail
          exact ⟨rfl, rfl, rfl⟩
  | ifTrue condition _ ih =>
      cases second with
      | single other => cases other
      | ifTrue otherCondition otherBranch =>
          obtain ⟨_, rfl, rfl⟩ := condition.deterministic otherCondition
          obtain ⟨rfl, rfl, rfl⟩ := ih otherBranch
          exact ⟨rfl, rfl, rfl⟩
      | ifFalse otherCondition _ => cases (condition.deterministic otherCondition).1
  | ifFalse condition _ ih =>
      cases second with
      | single other => cases other
      | ifTrue otherCondition _ => cases (condition.deterministic otherCondition).1
      | ifFalse otherCondition otherBranch =>
          obtain ⟨_, rfl, rfl⟩ := condition.deterministic otherCondition
          obtain ⟨rfl, rfl, rfl⟩ := ih otherBranch
          exact ⟨rfl, rfl, rfl⟩

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.TypedLetReturnTreeEvaluator`
-/

/-! Direct raw recursive-body evaluation. Optional annotations do not affect
type-free execution. Fresh IDs use the name table alone, and strict
initializers supply the actual values placed in the extended tail scope.
Discarded expressions execute strictly without extending source scopes.
Terminal lexical wrappers preserve the original child's result and cost. -/
set_option autoImplicit false
namespace Solcore.Frontend

/-- Exact existing Core-transition cost, without checking or executing Core.
Raw selected success does not imply whole-source acceptance. -/
def evaluateTypedLetReturnTreeWithCost? (owner : Resolved.DeclarationId)
    (table : LocalNameTable) (environment : Resolved.Environment)
    (body : Syntax.Block) : Option (Core.Value × Nat) :=
  match body with
  | ⟨_, [⟨_, .returnStmt none⟩]⟩ => some (.unit, 1)
  | ⟨_, [⟨_, .returnStmt (some source)⟩]⟩ =>
      evaluateLocalExpressionWithCost? table environment source
  | ⟨_, [⟨innerSpan, .block statements⟩]⟩ =>
      evaluateTypedLetReturnTreeWithCost? owner table environment ⟨innerSpan, statements⟩
  | ⟨blockSpan, ⟨_, .letDecl name _ (some initializer)⟩ :: rest⟩ => do
      let (boundValue, initializerCost) ← evaluateLocalExpressionWithCost? table environment initializer
      let id := Resolved.freshLocalId owner (table.map Prod.snd)
      let (value, tailCost) ← evaluateTypedLetReturnTreeWithCost? owner
        ((name.value, id) :: table) ((id, boundValue) :: environment) ⟨blockSpan, rest⟩
      return (value, initializerCost + tailCost + 2)
  | ⟨blockSpan, ⟨_, .expression expression true⟩ :: rest⟩ => do
      let (_, expressionCost) ← evaluateLocalExpressionWithCost? table environment expression
      let (value, tailCost) ← evaluateTypedLetReturnTreeWithCost? owner table environment ⟨blockSpan, rest⟩
      return (value, expressionCost + tailCost + 2)
  | ⟨_, [⟨_, .ifThen condition thenBody (some elseBody)⟩]⟩ => do
      let (.bool choice, conditionCost) ← evaluateLocalExpressionWithCost? table environment condition
        | none
      let (value, branchCost) ← if choice then
        evaluateTypedLetReturnTreeWithCost? owner table environment thenBody
      else evaluateTypedLetReturnTreeWithCost? owner table environment elseBody
      return (value, conditionCost + branchCost + 2)
  | _ => none
termination_by sizeOf body

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.TypedLetReturnTreeEvaluatorCorrespondence`
-/

/-! Direct body results and independent raw cost evidence agree on the original
syntax and actual caller rows. No annotation meaning or name-freshness premise
is inserted; strict initializers extend the tail with their actual value. -/
set_option autoImplicit false
namespace Solcore.Frontend

theorem evaluateTypedLetReturnTreeWithCost?_sound
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (accepted : evaluateTypedLetReturnTreeWithCost? owner table environment body = some (value, cost))
    (store : Core.Store) :
    TypedLetReturnTreeEvaluatesWithCost owner table environment store body value store cost := by
  cases body with
  | mk blockSpan statements =>
      cases statements with
      | nil => simp only [evaluateTypedLetReturnTreeWithCost?, reduceCtorEq] at accepted
      | cons statement rest =>
          cases statement with
          | mk statementSpan payload =>
              cases payload <;> try simp only [evaluateTypedLetReturnTreeWithCost?, reduceCtorEq] at accepted
              case returnStmt returned =>
                cases rest with
                | cons _ _ => simp only [evaluateTypedLetReturnTreeWithCost?, reduceCtorEq] at accepted
                | nil =>
                    cases returned with
                    | none =>
                        simp only [evaluateTypedLetReturnTreeWithCost?, Option.some.injEq, Prod.mk.injEq] at accepted
                        obtain ⟨rfl, rfl⟩ := accepted
                        exact .single .bare
                    | some source =>
                        rw [evaluateTypedLetReturnTreeWithCost?] at accepted
                        exact .single (.expression (evaluateLocalExpressionWithCost?_sound accepted store))
              case block inner =>
                cases rest with
                | cons _ _ => simp only [evaluateTypedLetReturnTreeWithCost?, reduceCtorEq] at accepted
                | nil =>
                    rw [evaluateTypedLetReturnTreeWithCost?] at accepted
                    exact .block (evaluateTypedLetReturnTreeWithCost?_sound accepted store)
              case letDecl name optionalType optionalInitializer =>
                cases optionalInitializer with
                | none => simp only [evaluateTypedLetReturnTreeWithCost?, reduceCtorEq] at accepted
                | some initializer =>
                    simp only [evaluateTypedLetReturnTreeWithCost?, bind, Option.bind_eq_some_iff] at accepted
                    obtain ⟨⟨boundValue, initializerCost⟩, initializerAccepted,
                      ⟨actual, tailCost⟩, tailAccepted, result⟩ := accepted
                    simp only [pure, Option.some.injEq, Prod.mk.injEq] at result
                    obtain ⟨rfl, rfl⟩ := result
                    cases optionalType with
                    | none =>
                        exact .inferred (evaluateLocalExpressionWithCost?_sound initializerAccepted store)
                          (evaluateTypedLetReturnTreeWithCost?_sound tailAccepted store)
                    | some annotation =>
                        exact .binding (evaluateLocalExpressionWithCost?_sound initializerAccepted store)
                          (evaluateTypedLetReturnTreeWithCost?_sound tailAccepted store)
              case expression source terminated =>
                cases terminated with
                | false => simp only [evaluateTypedLetReturnTreeWithCost?, reduceCtorEq] at accepted
                | true =>
                    simp only [evaluateTypedLetReturnTreeWithCost?, bind, Option.bind_eq_some_iff] at accepted
                    obtain ⟨⟨discarded, headCost⟩, headAccepted,
                      ⟨actual, tailCost⟩, tailAccepted, result⟩ := accepted
                    simp only [pure, Option.some.injEq, Prod.mk.injEq] at result
                    obtain ⟨rfl, rfl⟩ := result
                    exact .discard (evaluateLocalExpressionWithCost?_sound headAccepted store)
                      (evaluateTypedLetReturnTreeWithCost?_sound tailAccepted store)
              case ifThen condition thenBody optionalElse =>
                cases rest with
                | cons _ _ => simp only [evaluateTypedLetReturnTreeWithCost?, reduceCtorEq] at accepted
                | nil =>
                    cases optionalElse with
                    | none => simp only [evaluateTypedLetReturnTreeWithCost?, reduceCtorEq] at accepted
                    | some elseBody =>
                        simp only [evaluateTypedLetReturnTreeWithCost?, bind, Option.bind_eq_some_iff] at accepted
                        obtain ⟨⟨actual, conditionCost⟩, conditionAccepted, result⟩ := accepted
                        cases actual <;> simp only [reduceCtorEq] at result
                        rename_i choice
                        cases choice <;> simp only [Bool.false_eq_true, ↓reduceIte, Option.bind_eq_some_iff] at result
                        all_goals
                          obtain ⟨⟨actual, branchCost⟩, branchAccepted, result⟩ := result
                          simp only [pure, Option.some.injEq, Prod.mk.injEq] at result
                          obtain ⟨rfl, rfl⟩ := result
                          first
                          | exact .ifTrue (evaluateLocalExpressionWithCost?_sound conditionAccepted store)
                              (evaluateTypedLetReturnTreeWithCost?_sound branchAccepted store)
                          | exact .ifFalse (evaluateLocalExpressionWithCost?_sound conditionAccepted store)
                              (evaluateTypedLetReturnTreeWithCost?_sound branchAccepted store)
termination_by sizeOf body

theorem evaluateTypedLetReturnTreeWithCost?_complete
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : TypedLetReturnTreeEvaluatesWithCost owner table environment
      initialStore body value finalStore cost) :
    evaluateTypedLetReturnTreeWithCost? owner table environment body = some (value, cost) := by
  induction evaluation with
  | single child =>
      cases child with
      | bare => simp only [evaluateTypedLetReturnTreeWithCost?]
      | expression evaluated =>
          simpa only [evaluateTypedLetReturnTreeWithCost?] using evaluateLocalExpressionWithCost?_complete evaluated
  | block _ ih => simpa only [evaluateTypedLetReturnTreeWithCost?] using ih
  | binding initializer _ ih | inferred initializer _ ih | discard initializer _ ih
  | ifTrue initializer _ ih | ifFalse initializer _ ih =>
      simp [evaluateTypedLetReturnTreeWithCost?, evaluateLocalExpressionWithCost?_complete initializer, ih]

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.TypedLetReturnTreeEvaluatorProperties`
-/

/-! Exact store-free outputs characterize raw recursive paths, not whole-body
acceptance. General store correspondence explicitly retains the final store. -/
set_option autoImplicit false
namespace Solcore.Frontend

theorem evaluateTypedLetReturnTreeWithCost?_iff
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {body : Syntax.Block} {value : Core.Value} {cost : Nat} (store : Core.Store) :
    evaluateTypedLetReturnTreeWithCost? owner table environment body = some (value, cost) ↔
      TypedLetReturnTreeEvaluatesWithCost owner table environment store body value store cost :=
  ⟨fun accepted => evaluateTypedLetReturnTreeWithCost?_sound accepted store,
    evaluateTypedLetReturnTreeWithCost?_complete⟩

theorem typedLetReturnTreeEvaluatesWithCost_iff_evaluate
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat} :
    TypedLetReturnTreeEvaluatesWithCost owner table environment initialStore body value finalStore cost ↔
      finalStore = initialStore ∧
        evaluateTypedLetReturnTreeWithCost? owner table environment body = some (value, cost) := by
  constructor
  · intro evaluation
    exact ⟨evaluation.store_eq, evaluateTypedLetReturnTreeWithCost?_complete evaluation⟩
  · rintro ⟨rfl, accepted⟩
    exact evaluateTypedLetReturnTreeWithCost?_sound accepted _

theorem evaluateTypedLetReturnTreeWithCost?_eq_none_iff
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {body : Syntax.Block} (store : Core.Store) :
    evaluateTypedLetReturnTreeWithCost? owner table environment body = none ↔
      ¬ ∃ value cost, TypedLetReturnTreeEvaluatesWithCost owner table environment store body value store cost := by
  constructor
  · intro absent ⟨value, cost, evaluation⟩
    have accepted := evaluateTypedLetReturnTreeWithCost?_complete evaluation
    rw [absent] at accepted
    cases accepted
  · intro absent
    cases result : evaluateTypedLetReturnTreeWithCost? owner table environment body with
    | none => rfl
    | some pair =>
        exact False.elim (absent ⟨pair.1, pair.2, evaluateTypedLetReturnTreeWithCost?_sound result store⟩)

theorem evaluateTypedLetReturnTreeWithCost?_exists_cost_iff
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {body : Syntax.Block} {value : Core.Value} (store : Core.Store) :
    (∃ cost, evaluateTypedLetReturnTreeWithCost? owner table environment body = some (value, cost)) ↔
      TypedLetReturnTreeEvaluates owner table environment store body value store := by
  constructor
  · rintro ⟨cost, accepted⟩
    exact (evaluateTypedLetReturnTreeWithCost?_sound accepted store).erase
  · intro evaluation
    obtain ⟨cost, costed⟩ := evaluation.exists_cost
    exact ⟨cost, evaluateTypedLetReturnTreeWithCost?_complete costed⟩

theorem evaluateTypedLetReturnTreeWithCost?_value_iff
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {body : Syntax.Block} {value : Core.Value} (store : Core.Store) :
    (evaluateTypedLetReturnTreeWithCost? owner table environment body).map Prod.fst = some value ↔
      TypedLetReturnTreeEvaluates owner table environment store body value store := by
  constructor
  · intro projected
    obtain ⟨⟨actual, cost⟩, accepted, same⟩ := Option.map_eq_some_iff.mp projected
    cases same
    exact (evaluateTypedLetReturnTreeWithCost?_sound accepted store).erase
  · intro evaluation
    obtain ⟨cost, accepted⟩ := (evaluateTypedLetReturnTreeWithCost?_exists_cost_iff store).mpr evaluation
    simp only [accepted, Option.map_some]

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.TypedLetReturnTreeLookupProperties`
-/

/-! Raw recursive results depend on composed first-match values, not the
identity or layout of the intermediate keys. Owners and fresh IDs may differ.
These laws do not establish whole checking or equality of Core checkpoints. -/
set_option autoImplicit false
namespace Solcore.Frontend

private theorem lookup_bind_fresh (owner : Resolved.DeclarationId)
    (table : LocalNameTable) (environment : Resolved.Environment)
    (binder spelling : String) (value : Core.Value) :
    (LocalNameTable.lookup? ((binder, Resolved.freshLocalId owner (table.map Prod.snd)) :: table) spelling).bind
        (Resolved.LocalScope.lookup? ((Resolved.freshLocalId owner (table.map Prod.snd), value) :: environment)) =
      if binder = spelling then some value else (table.lookup? spelling).bind environment.lookup? := by
  by_cases same : binder = spelling
  · simp only [LocalNameTable.lookup?, if_pos same, Option.bind_some, Resolved.LocalScope.lookup?, ↓reduceIte]
  · simp only [LocalNameTable.lookup?, if_neg same]
    cases found : table.lookup? spelling with
    | none => rfl
    | some id =>
        have different : Resolved.freshLocalId owner (table.map Prod.snd) ≠ id := by
          intro equal
          apply Resolved.freshLocalId_not_mem owner (table.map Prod.snd)
          rw [equal]
          exact List.mem_map_of_mem (f := Prod.snd) (LocalNameTable.lookup?_iff.mp found).mem
        simp only [Option.bind_some, Resolved.LocalScope.lookup?, if_neg different]

private theorem lookup_fresh_congr
    (leftOwner rightOwner : Resolved.DeclarationId) (leftTable rightTable : LocalNameTable)
    (leftEnvironment rightEnvironment : Resolved.Environment)
    (sameLookup : ∀ name, (leftTable.lookup? name).bind leftEnvironment.lookup? =
      (rightTable.lookup? name).bind rightEnvironment.lookup?) (binder : String) (value : Core.Value) :
    ∀ name,
      (LocalNameTable.lookup? ((binder, Resolved.freshLocalId leftOwner (leftTable.map Prod.snd)) :: leftTable) name).bind
          (Resolved.LocalScope.lookup? ((Resolved.freshLocalId leftOwner (leftTable.map Prod.snd), value) :: leftEnvironment)) =
        (LocalNameTable.lookup? ((binder, Resolved.freshLocalId rightOwner (rightTable.map Prod.snd)) :: rightTable) name).bind
          (Resolved.LocalScope.lookup? ((Resolved.freshLocalId rightOwner (rightTable.map Prod.snd), value) :: rightEnvironment)) := by
  intro name
  rw [lookup_bind_fresh, lookup_bind_fresh, sameLookup name]

/-- Equal composed actual-value lookups preserve full raw results even when
owners, scope lengths and independently allocated fresh identities differ. -/
theorem evaluateTypedLetReturnTreeWithCost?_congr_lookup
    (leftOwner rightOwner : Resolved.DeclarationId) (leftTable rightTable : LocalNameTable)
    (leftEnvironment rightEnvironment : Resolved.Environment)
    (sameLookup : ∀ name, (leftTable.lookup? name).bind leftEnvironment.lookup? =
      (rightTable.lookup? name).bind rightEnvironment.lookup?) (body : Syntax.Block) :
    evaluateTypedLetReturnTreeWithCost? leftOwner leftTable leftEnvironment body =
      evaluateTypedLetReturnTreeWithCost? rightOwner rightTable rightEnvironment body := by
  cases body with
  | mk blockSpan statements =>
      cases statements with
      | nil => simp only [evaluateTypedLetReturnTreeWithCost?]
      | cons statement rest =>
          cases statement with
          | mk statementSpan payload =>
              cases payload <;> try simp only [evaluateTypedLetReturnTreeWithCost?]
              case returnStmt returned =>
                cases rest with
                | cons _ _ => simp only [evaluateTypedLetReturnTreeWithCost?]
                | nil =>
                    cases returned with
                    | none => simp only [evaluateTypedLetReturnTreeWithCost?]
                    | some source =>
                        simpa only [evaluateTypedLetReturnTreeWithCost?] using
                          evaluateLocalExpressionWithCost?_congr_lookup leftTable rightTable
                            leftEnvironment rightEnvironment sameLookup source
              case block inner =>
                cases rest with
                | cons _ _ => simp only [evaluateTypedLetReturnTreeWithCost?]
                | nil =>
                    simpa only [evaluateTypedLetReturnTreeWithCost?] using
                      evaluateTypedLetReturnTreeWithCost?_congr_lookup leftOwner rightOwner leftTable rightTable
                        leftEnvironment rightEnvironment sameLookup ⟨statementSpan, inner⟩
              case letDecl name optionalType optionalInitializer =>
                cases optionalInitializer with
                | none => simp only [evaluateTypedLetReturnTreeWithCost?]
                | some initializer =>
                    have tailSame (boundValue : Core.Value) :
                        evaluateTypedLetReturnTreeWithCost? leftOwner
                          ((name.value, Resolved.freshLocalId leftOwner (leftTable.map Prod.snd)) :: leftTable)
                          ((Resolved.freshLocalId leftOwner (leftTable.map Prod.snd), boundValue) :: leftEnvironment) ⟨blockSpan, rest⟩ =
                        evaluateTypedLetReturnTreeWithCost? rightOwner
                          ((name.value, Resolved.freshLocalId rightOwner (rightTable.map Prod.snd)) :: rightTable)
                          ((Resolved.freshLocalId rightOwner (rightTable.map Prod.snd), boundValue) :: rightEnvironment) ⟨blockSpan, rest⟩ :=
                      evaluateTypedLetReturnTreeWithCost?_congr_lookup leftOwner rightOwner _ _ _ _
                        (lookup_fresh_congr leftOwner rightOwner leftTable rightTable leftEnvironment rightEnvironment
                          sameLookup name.value boundValue) ⟨blockSpan, rest⟩
                    rw [evaluateTypedLetReturnTreeWithCost?, evaluateTypedLetReturnTreeWithCost?,
                      evaluateLocalExpressionWithCost?_congr_lookup leftTable rightTable leftEnvironment rightEnvironment sameLookup]
                    simp only [tailSame]
              case expression source terminated =>
                cases terminated with
                | false => simp only [evaluateTypedLetReturnTreeWithCost?]
                | true =>
                    rw [evaluateTypedLetReturnTreeWithCost?, evaluateTypedLetReturnTreeWithCost?,
                      evaluateLocalExpressionWithCost?_congr_lookup leftTable rightTable leftEnvironment rightEnvironment sameLookup,
                      evaluateTypedLetReturnTreeWithCost?_congr_lookup leftOwner rightOwner leftTable rightTable
                        leftEnvironment rightEnvironment sameLookup ⟨blockSpan, rest⟩]
              case ifThen condition thenBody optionalElse =>
                cases rest with
                | cons _ _ => simp only [evaluateTypedLetReturnTreeWithCost?]
                | nil =>
                    cases optionalElse with
                    | none => simp only [evaluateTypedLetReturnTreeWithCost?]
                    | some elseBody =>
                        rw [evaluateTypedLetReturnTreeWithCost?, evaluateTypedLetReturnTreeWithCost?,
                          evaluateLocalExpressionWithCost?_congr_lookup leftTable rightTable leftEnvironment rightEnvironment sameLookup,
                          evaluateTypedLetReturnTreeWithCost?_congr_lookup leftOwner rightOwner leftTable rightTable
                            leftEnvironment rightEnvironment sameLookup thenBody,
                          evaluateTypedLetReturnTreeWithCost?_congr_lookup leftOwner rightOwner leftTable rightTable
                            leftEnvironment rightEnvironment sameLookup elseBody]
termination_by sizeOf body

/-- The relation still records both stores: observational equality cannot
replace a successful path's final store by an unrelated store. -/
theorem typedLetReturnTreeEvaluatesWithCost_congr_lookup_iff
    {leftOwner rightOwner : Resolved.DeclarationId} {leftTable rightTable : LocalNameTable}
    {leftEnvironment rightEnvironment : Resolved.Environment}
    (sameLookup : ∀ name, (leftTable.lookup? name).bind leftEnvironment.lookup? =
      (rightTable.lookup? name).bind rightEnvironment.lookup?)
    {body : Syntax.Block} {initialStore finalStore : Core.Store} {value : Core.Value} {cost : Nat} :
    TypedLetReturnTreeEvaluatesWithCost leftOwner leftTable leftEnvironment initialStore body value finalStore cost ↔
      TypedLetReturnTreeEvaluatesWithCost rightOwner rightTable rightEnvironment initialStore body value finalStore cost := by
  rw [typedLetReturnTreeEvaluatesWithCost_iff_evaluate, typedLetReturnTreeEvaluatesWithCost_iff_evaluate,
    evaluateTypedLetReturnTreeWithCost?_congr_lookup leftOwner rightOwner leftTable rightTable
      leftEnvironment rightEnvironment sameLookup]

theorem typedLetReturnTreeEvaluates_congr_lookup_iff
    {leftOwner rightOwner : Resolved.DeclarationId} {leftTable rightTable : LocalNameTable}
    {leftEnvironment rightEnvironment : Resolved.Environment}
    (sameLookup : ∀ name, (leftTable.lookup? name).bind leftEnvironment.lookup? =
      (rightTable.lookup? name).bind rightEnvironment.lookup?)
    {body : Syntax.Block} {initialStore finalStore : Core.Store} {value : Core.Value} :
    TypedLetReturnTreeEvaluates leftOwner leftTable leftEnvironment initialStore body value finalStore ↔
      TypedLetReturnTreeEvaluates rightOwner rightTable rightEnvironment initialStore body value finalStore := by
  rw [typedLetReturnTreeEvaluates_iff_exists_cost, typedLetReturnTreeEvaluates_iff_exists_cost]
  exact exists_congr fun _ => typedLetReturnTreeEvaluatesWithCost_congr_lookup_iff sameLookup

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.TypedLetReturnTreeRawOwnerProperties`
-/

/-! Raw owner covariance preserves complete direct results and independent
paths on arbitrary caller rows. No checking, typing, uniqueness or alignment
premise is introduced, and owner maps need not be surjective. -/

set_option autoImplicit false

namespace Solcore.Frontend

private theorem expression_mapIds
    (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping)
    (table : LocalNameTable) (environment : Resolved.Environment) (source : Syntax.Expr) :
    evaluateLocalExpressionWithCost? (LocalNameTable.mapIds mapping table)
        (Resolved.LocalScope.mapIds mapping environment) source =
      evaluateLocalExpressionWithCost? table environment source := by
  cases original : evaluateLocalExpressionWithCost? table environment source with
  | none =>
      cases mapped : evaluateLocalExpressionWithCost? (LocalNameTable.mapIds mapping table)
          (Resolved.LocalScope.mapIds mapping environment) source with
      | none => rfl
      | some pair =>
          have impossible := evaluateLocalExpressionWithCost?_complete
            ((localExpressionEvaluatesWithCost_mapIds_iff mapping injective).mp
              (evaluateLocalExpressionWithCost?_sound mapped []))
          rw [original] at impossible
          cases impossible
  | some pair =>
      exact evaluateLocalExpressionWithCost?_complete
        ((localExpressionEvaluatesWithCost_mapIds_iff mapping injective).mpr
          (evaluateLocalExpressionWithCost?_sound original []))

private theorem fresh_mapOwner
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (injective : Function.Injective mapping) (owner : Resolved.DeclarationId) (table : LocalNameTable) :
    Resolved.freshLocalId (mapping owner)
        ((LocalNameTable.mapIds (ownerLocalIdMap mapping) table).map Prod.snd) =
      ownerLocalIdMap mapping (Resolved.freshLocalId owner (table.map Prod.snd)) := by
  simpa only [LocalNameTable.mapIds, List.map_map, Function.comp_def, ownerLocalIdMap,
    Resolved.freshLocalId_owner] using
    Resolved.freshLocalId_map_owner mapping injective owner (table.map Prod.snd)

/-- Relabeling both raw tables preserves success and absence, including strict
initializers and only the actual selected arm. Source and values are unchanged. -/
theorem evaluateTypedLetReturnTreeWithCost?_mapOwner
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (injective : Function.Injective mapping) (owner : Resolved.DeclarationId)
    (table : LocalNameTable) (environment : Resolved.Environment) (body : Syntax.Block) :
    evaluateTypedLetReturnTreeWithCost? (mapping owner)
        (LocalNameTable.mapIds (ownerLocalIdMap mapping) table)
        (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) environment) body =
      evaluateTypedLetReturnTreeWithCost? owner table environment body := by
  cases body with
  | mk blockSpan statements =>
      cases statements with
      | nil => simp only [evaluateTypedLetReturnTreeWithCost?]
      | cons statement rest =>
          cases statement with
          | mk statementSpan payload =>
              cases payload <;> try simp only [evaluateTypedLetReturnTreeWithCost?]
              case returnStmt returned =>
                cases rest with
                | cons _ _ => simp only [evaluateTypedLetReturnTreeWithCost?]
                | nil =>
                    cases returned with
                    | none => simp only [evaluateTypedLetReturnTreeWithCost?]
                    | some source =>
                        simpa only [evaluateTypedLetReturnTreeWithCost?] using
                          expression_mapIds (ownerLocalIdMap mapping)
                            (ownerLocalIdMap_injective mapping injective) table environment source
              case block inner =>
                cases rest with
                | cons _ _ => simp only [evaluateTypedLetReturnTreeWithCost?]
                | nil =>
                    simpa only [evaluateTypedLetReturnTreeWithCost?] using
                      evaluateTypedLetReturnTreeWithCost?_mapOwner mapping injective owner table environment ⟨statementSpan, inner⟩
              case letDecl name optionalType optionalInitializer =>
                cases optionalInitializer with
                | none => simp only [evaluateTypedLetReturnTreeWithCost?]
                | some initializer =>
                    have tailSame (boundValue : Core.Value) :
                        evaluateTypedLetReturnTreeWithCost? (mapping owner)
                          ((name.value, Resolved.freshLocalId (mapping owner)
                            ((LocalNameTable.mapIds (ownerLocalIdMap mapping) table).map Prod.snd)) ::
                              LocalNameTable.mapIds (ownerLocalIdMap mapping) table)
                          ((Resolved.freshLocalId (mapping owner)
                            ((LocalNameTable.mapIds (ownerLocalIdMap mapping) table).map Prod.snd), boundValue) ::
                              Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) environment) ⟨blockSpan, rest⟩ =
                        evaluateTypedLetReturnTreeWithCost? owner
                          ((name.value, Resolved.freshLocalId owner (table.map Prod.snd)) :: table)
                          ((Resolved.freshLocalId owner (table.map Prod.snd), boundValue) :: environment) ⟨blockSpan, rest⟩ := by
                      rw [fresh_mapOwner mapping injective owner table]
                      simpa only [LocalNameTable.mapIds, Resolved.LocalScope.mapIds, List.map_cons] using
                        evaluateTypedLetReturnTreeWithCost?_mapOwner mapping injective owner
                          ((name.value, Resolved.freshLocalId owner (table.map Prod.snd)) :: table)
                          ((Resolved.freshLocalId owner (table.map Prod.snd), boundValue) :: environment) ⟨blockSpan, rest⟩
                    rw [evaluateTypedLetReturnTreeWithCost?, evaluateTypedLetReturnTreeWithCost?,
                      expression_mapIds (ownerLocalIdMap mapping)
                        (ownerLocalIdMap_injective mapping injective)]
                    simp only [tailSame]
              case expression source terminated =>
                cases terminated with
                | false => simp only [evaluateTypedLetReturnTreeWithCost?]
                | true =>
                    rw [evaluateTypedLetReturnTreeWithCost?, evaluateTypedLetReturnTreeWithCost?,
                      expression_mapIds (ownerLocalIdMap mapping)
                        (ownerLocalIdMap_injective mapping injective),
                      evaluateTypedLetReturnTreeWithCost?_mapOwner mapping injective owner table environment ⟨blockSpan, rest⟩]
              case ifThen condition thenBody optionalElse =>
                cases rest with
                | cons _ _ => simp only [evaluateTypedLetReturnTreeWithCost?]
                | nil =>
                    cases optionalElse with
                    | none => simp only [evaluateTypedLetReturnTreeWithCost?]
                    | some elseBody =>
                        rw [evaluateTypedLetReturnTreeWithCost?, evaluateTypedLetReturnTreeWithCost?,
                          expression_mapIds (ownerLocalIdMap mapping)
                            (ownerLocalIdMap_injective mapping injective),
                          evaluateTypedLetReturnTreeWithCost?_mapOwner mapping injective owner table environment thenBody,
                          evaluateTypedLetReturnTreeWithCost?_mapOwner mapping injective owner table environment elseBody]
termination_by sizeOf body

/-- Both stores and the exact independent cost are retained; no unrelated
final store is licensed by the store-free executable equality. -/
theorem typedLetReturnTreeEvaluatesWithCost_mapOwner_iff
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (injective : Function.Injective mapping)
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {body : Syntax.Block} {initialStore finalStore : Core.Store} {value : Core.Value} {cost : Nat} :
    TypedLetReturnTreeEvaluatesWithCost (mapping owner)
        (LocalNameTable.mapIds (ownerLocalIdMap mapping) table)
        (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) environment) initialStore body value finalStore cost ↔
      TypedLetReturnTreeEvaluatesWithCost owner table environment initialStore body value finalStore cost := by
  rw [typedLetReturnTreeEvaluatesWithCost_iff_evaluate, typedLetReturnTreeEvaluatesWithCost_iff_evaluate,
    evaluateTypedLetReturnTreeWithCost?_mapOwner mapping injective]

theorem typedLetReturnTreeEvaluates_mapOwner_iff
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (injective : Function.Injective mapping)
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {body : Syntax.Block} {initialStore finalStore : Core.Store} {value : Core.Value} :
    TypedLetReturnTreeEvaluates (mapping owner)
        (LocalNameTable.mapIds (ownerLocalIdMap mapping) table)
        (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) environment) initialStore body value finalStore ↔
      TypedLetReturnTreeEvaluates owner table environment initialStore body value finalStore := by
  rw [typedLetReturnTreeEvaluates_iff_exists_cost, typedLetReturnTreeEvaluates_iff_exists_cost]
  exact exists_congr fun _ => typedLetReturnTreeEvaluatesWithCost_mapOwner_iff mapping injective

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.TypedLetReturnTreeRunner`
-/

/-! A separate recursive body runner checks the actual static projection and
executes the exact Core with the original ordered values. No function entry is
prepared or extended; branch-local bindings remain inside the checked body. -/

set_option autoImplicit false

namespace Solcore.Frontend.LocalInputs

def checkTypedLetReturnTree? (inputs : LocalInputs) (types : TypeNameTable)
    (owner : Resolved.DeclarationId) (body : Syntax.Block) : Option (Core.Expr × Core.Ty) :=
  elaborateTypedLetReturnTree? types owner inputs.toTypeInputs body

def runTypedLetReturnTree? (inputs : LocalInputs) (types : TypeNameTable)
    (owner : Resolved.DeclarationId) (fuel : Nat) (body : Syntax.Block)
    (store : Core.Store) : Option (Core.Ty × Core.StatefulRunResult) := do
  let (core, type) ← inputs.checkTypedLetReturnTree? types owner body
  return (type, Core.runStateful fuel (Core.State.initial core inputs.environment.values store))

end Solcore.Frontend.LocalInputs

/-!
## Consolidated module: `Solcore.Frontend.TypedLetReturnTreeTypeExtensionProperties`
-/

/-! Preserve annotation meanings throughout recursive bodies without changing
source, owner, inputs or exact Core. Both arms retain their original scope. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem TypedLetReturnTreeElaborates.extend_types
    {old new : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : TypedLetReturnTreeElaborates old owner inputs body core type)
    (extension : TypeNameTable.Extends old new) :
    TypedLetReturnTreeElaborates new owner inputs body core type := by
  induction elaboration with
  | single child => exact .single child
  | block _ ih => exact .block ih
  | binding meaning unused resolution lowered typing _ ih =>
      exact .binding (meaning.extend_types extension) unused resolution lowered typing ih
  | inferred unused resolution lowered typing _ ih =>
      exact .inferred unused resolution lowered typing ih
  | discard resolution lowered typing _ ih => exact .discard resolution lowered typing ih
  | conditional resolution lowered typing _ _ thenIH elseIH =>
      exact .conditional resolution lowered typing thenIH elseIH

theorem TypedLetReturnTreeHasType.extend_types
    {old new : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {type : Core.Ty}
    (typing : TypedLetReturnTreeHasType old owner inputs body type)
    (extension : TypeNameTable.Extends old new) :
    TypedLetReturnTreeHasType new owner inputs body type := by
  induction typing with
  | single child => exact .single child
  | block _ ih => exact .block ih
  | binding meaning unused initializer _ ih =>
      exact .binding (meaning.extend_types extension) unused initializer ih
  | inferred unused initializer _ ih => exact .inferred unused initializer ih
  | discard expression _ ih => exact .discard expression ih
  | conditional condition _ _ thenIH elseIH =>
      exact .conditional condition thenIH elseIH

theorem elaborateTypedLetReturnTree?_some_of_extends
    {old new : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (extension : TypeNameTable.Extends old new)
    (accepted : elaborateTypedLetReturnTree? old owner inputs body = some (core, type)) :
    elaborateTypedLetReturnTree? new owner inputs body = some (core, type) :=
  ((elaborateTypedLetReturnTree?_elaborates accepted).extend_types extension).complete

/-- Mutual first-match preservation retains every optional result, including
rejection. One-way extension alone can repair an unknown annotation in either arm. -/
theorem elaborateTypedLetReturnTree?_eq_of_mutual_extends
    {old new : TypeNameTable} (forward : TypeNameTable.Extends old new)
    (backward : TypeNameTable.Extends new old) (owner : Resolved.DeclarationId)
    (inputs : LocalTypeInputs) (body : Syntax.Block) :
    elaborateTypedLetReturnTree? old owner inputs body =
      elaborateTypedLetReturnTree? new owner inputs body := by
  cases oldResult : elaborateTypedLetReturnTree? old owner inputs body with
  | none =>
      cases newResult : elaborateTypedLetReturnTree? new owner inputs body with
      | none => rfl
      | some pair =>
          rcases pair with ⟨core, type⟩
          have preserved := elaborateTypedLetReturnTree?_some_of_extends backward newResult
          rw [oldResult] at preserved
          cases preserved
  | some pair =>
      rcases pair with ⟨core, type⟩
      exact (elaborateTypedLetReturnTree?_some_of_extends forward oldResult).symm

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.TypedLetReturnTreeRunnerTypeExtensionProperties`
-/

/-! Meaning extension preserves successful complete recursive-body results.
Mutual extension retains rejection too; actual inputs, fuel and store stay fixed. -/

set_option autoImplicit false

namespace Solcore.Frontend.LocalInputs

theorem checkTypedLetReturnTree?_some_of_extends {old new : TypeNameTable}
    {inputs : LocalInputs} {owner : Resolved.DeclarationId} {body : Syntax.Block}
    {core : Core.Expr} {type : Core.Ty} (extension : TypeNameTable.Extends old new)
    (accepted : inputs.checkTypedLetReturnTree? old owner body = some (core, type)) :
    inputs.checkTypedLetReturnTree? new owner body = some (core, type) :=
  elaborateTypedLetReturnTree?_some_of_extends extension accepted

theorem checkTypedLetReturnTree?_eq_of_mutual_extends (inputs : LocalInputs)
    {old new : TypeNameTable} (forward : TypeNameTable.Extends old new)
    (backward : TypeNameTable.Extends new old) (owner : Resolved.DeclarationId)
    (body : Syntax.Block) :
    inputs.checkTypedLetReturnTree? old owner body = inputs.checkTypedLetReturnTree? new owner body :=
  elaborateTypedLetReturnTree?_eq_of_mutual_extends forward backward owner inputs.toTypeInputs body

/-- Preserve the full successful pair, including a genuine suspended state at
insufficient fuel. No extra typing or sufficient-fuel premise is introduced. -/
theorem runTypedLetReturnTree?_some_of_extends {old new : TypeNameTable}
    {inputs : LocalInputs} {owner : Resolved.DeclarationId} {body : Syntax.Block}
    {fuel : Nat} {store : Core.Store} {type : Core.Ty} {result : Core.StatefulRunResult}
    (extension : TypeNameTable.Extends old new)
    (accepted : inputs.runTypedLetReturnTree? old owner fuel body store = some (type, result)) :
    inputs.runTypedLetReturnTree? new owner fuel body store = some (type, result) := by
  cases checked : inputs.checkTypedLetReturnTree? old owner body with
  | none => simp [runTypedLetReturnTree?, checked] at accepted
  | some pair =>
      obtain ⟨core, checkedType⟩ := pair
      have preserved := checkTypedLetReturnTree?_some_of_extends extension checked
      simpa only [runTypedLetReturnTree?, checked, preserved] using accepted

theorem runTypedLetReturnTree?_eq_of_mutual_extends (inputs : LocalInputs)
    {old new : TypeNameTable} (forward : TypeNameTable.Extends old new)
    (backward : TypeNameTable.Extends new old) (owner : Resolved.DeclarationId)
    (fuel : Nat) (body : Syntax.Block) (store : Core.Store) :
    inputs.runTypedLetReturnTree? old owner fuel body store =
      inputs.runTypedLetReturnTree? new owner fuel body store := by
  simp only [runTypedLetReturnTree?, checkTypedLetReturnTree?_eq_of_mutual_extends
    inputs forward backward owner body]

end Solcore.Frontend.LocalInputs

/-!
## Consolidated module: `Solcore.Frontend.LocalFragmentProperties`
-/

/-! Exact frontend provenance retains every child of the local Core fragment.
These structural consequences use lowering evidence, not evaluation or a
replacement expression of the same type. No runtime entry imports are needed. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem elaborateLocalExpression?_localFragment
    {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateLocalExpression? table context source = some (core, type)) :
    Core.Expr.LocalFragment core := by
  obtain ⟨_, _, lowered, _⟩ := elaborateLocalExpression?_sound accepted
  exact lowered.localFragment

theorem ReturnBodyElaborates.localFragment
    {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : ReturnBodyElaborates table context body core type) :
    Core.Expr.LocalFragment core := by
  cases elaboration with
  | bare => exact .unit
  | expression _ lowered _ => exact lowered.localFragment

theorem TerminalReturnTreeElaborates.localFragment
    {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : TerminalReturnTreeElaborates table context body core type) :
    Core.Expr.LocalFragment core := by
  induction elaboration with
  | single child => exact child.localFragment
  | conditional _ lowered _ _ _ thenIH elseIH =>
      exact .ifE lowered.localFragment thenIH elseIH

theorem TypedLetReturnTreeElaborates.localFragment
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : TypedLetReturnTreeElaborates types owner inputs body core type) :
    Core.Expr.LocalFragment core := by
  induction elaboration with
  | single child => exact child.localFragment
  | binding _ _ _ lowered _ _ ih | inferred _ _ lowered _ _ ih =>
      exact .letE lowered.localFragment ih
  | discard _ lowered _ _ ih =>
      exact .letE lowered.localFragment (ih.weakenAt 0)
  | block _ ih => exact ih
  | conditional _ lowered _ _ _ thenIH elseIH =>
      exact .ifE lowered.localFragment thenIH elseIH

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.TypedLetReturnTreeProperties`
-/

/-! Independent whole typing fixes recursive lets and both ordered branches.
The original input types need no runtime values or extra name-uniqueness premise. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem TypedLetReturnTreeElaborates.hasType
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : TypedLetReturnTreeElaborates types owner inputs body core type) :
    TypedLetReturnTreeHasType types owner inputs body type := by
  induction elaboration with
  | single child => exact .single child.hasType
  | block _ ih => exact .block ih
  | binding meaning unused resolution _ typing _ ih =>
      exact .binding meaning unused (resolution.reflects_type typing) ih
  | inferred unused resolution _ typing _ ih =>
      exact .inferred unused (resolution.reflects_type typing) ih
  | discard resolution _ typing _ ih => exact .discard (resolution.reflects_type typing) ih
  | conditional resolution _ typing _ _ thenIH elseIH =>
      exact .conditional (resolution.reflects_type typing) thenIH elseIH

theorem TypedLetReturnTreeHasType.elaborates_exact
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {type : Core.Ty}
    (typing : TypedLetReturnTreeHasType types owner inputs body type) :
    ∃ core, TypedLetReturnTreeElaborates types owner inputs body core type := by
  induction typing with
  | single child =>
      obtain ⟨core, elaboration⟩ := child.elaborates_exact
      exact ⟨core, .single elaboration⟩
  | block _ ih =>
      obtain ⟨core, elaboration⟩ := ih
      exact ⟨core, .block elaboration⟩
  | binding meaning unused initializerTyping _ ih =>
      obtain ⟨resolved, resolution, typed⟩ := initializerTyping.resolves
      obtain ⟨initializerCore, lowered, _⟩ := typed.lowers
      obtain ⟨tailCore, tailElaboration⟩ := ih
      exact ⟨.letE initializerCore tailCore, .binding meaning unused resolution
        (by simpa only [LocalTypeInputs.context_ids] using lowered) typed tailElaboration⟩
  | inferred unused initializerTyping _ ih =>
      obtain ⟨resolved, resolution, typed⟩ := initializerTyping.resolves
      obtain ⟨initializerCore, lowered, _⟩ := typed.lowers
      obtain ⟨tailCore, tailElaboration⟩ := ih
      exact ⟨.letE initializerCore tailCore, .inferred unused resolution
        (by simpa only [LocalTypeInputs.context_ids] using lowered) typed tailElaboration⟩
  | discard expressionTyping _ ih =>
      obtain ⟨resolved, resolution, typed⟩ := expressionTyping.resolves
      obtain ⟨expressionCore, lowered, _⟩ := typed.lowers
      obtain ⟨tailCore, tailElaboration⟩ := ih
      exact ⟨.letE expressionCore (tailCore.weakenAt 0), .discard resolution
        (by simpa only [LocalTypeInputs.context_ids] using lowered) typed tailElaboration⟩
  | conditional conditionTyping _ _ thenIH elseIH =>
      obtain ⟨resolved, resolution, typed⟩ := conditionTyping.resolves
      obtain ⟨conditionCore, lowered, _⟩ := typed.lowers
      obtain ⟨thenCore, thenElaboration⟩ := thenIH
      obtain ⟨elseCore, elseElaboration⟩ := elseIH
      exact ⟨.ifE conditionCore thenCore elseCore, .conditional resolution
        (by simpa only [LocalTypeInputs.context_ids] using lowered) typed thenElaboration elseElaboration⟩

theorem typedLetReturnTreeHasType_iff_elaborates_exact
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {type : Core.Ty} :
    TypedLetReturnTreeHasType types owner inputs body type ↔
      ∃ core, TypedLetReturnTreeElaborates types owner inputs body core type :=
  ⟨TypedLetReturnTreeHasType.elaborates_exact, fun ⟨_, elaboration⟩ => elaboration.hasType⟩

theorem TypedLetReturnTreeHasType.elaborates
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {type : Core.Ty}
    (typing : TypedLetReturnTreeHasType types owner inputs body type) :
    ∃ core, elaborateTypedLetReturnTree? types owner inputs body = some (core, type) := by
  obtain ⟨core, elaboration⟩ := typing.elaborates_exact
  exact ⟨core, elaboration.complete⟩

theorem elaborateTypedLetReturnTree?_sound
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTypedLetReturnTree? types owner inputs body = some (core, type)) :
    TypedLetReturnTreeHasType types owner inputs body type :=
  (elaborateTypedLetReturnTree?_elaborates accepted).hasType

theorem typedLetReturnTreeHasType_iff_elaborates
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {type : Core.Ty} :
    TypedLetReturnTreeHasType types owner inputs body type ↔
      ∃ core, elaborateTypedLetReturnTree? types owner inputs body = some (core, type) :=
  ⟨TypedLetReturnTreeHasType.elaborates, fun ⟨_, accepted⟩ => elaborateTypedLetReturnTree?_sound accepted⟩

theorem elaborateTypedLetReturnTree?_core_hasType
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTypedLetReturnTree? types owner inputs body = some (core, type)) :
    Core.HasType (Resolved.LocalScope.values inputs.context) core type := by
  have elaboration := elaborateTypedLetReturnTree?_elaborates accepted
  clear accepted
  induction elaboration with
  | single child => exact elaborateReturnBody?_core_hasType child.complete
  | block _ ih => exact ih
  | binding _ _ _ lowered typing _ ih | inferred _ _ lowered typing _ ih =>
      apply Core.HasType.letE
      · rw [← LocalTypeInputs.context_ids] at lowered
        exact lowered.preserves_type typing
      · simpa only [LocalTypeInputs.bindFresh_context, Resolved.LocalScope.values,
          List.map_cons, Prod.snd] using ih
  | discard _ lowered typing tail ih =>
      rw [← LocalTypeInputs.context_ids] at lowered
      exact .letE (lowered.preserves_type typing) (ih.weakenAt_zero_localFragment tail.localFragment _)
  | conditional _ lowered typing _ _ thenIH elseIH =>
      rw [← LocalTypeInputs.context_ids] at lowered
      exact .ifE (lowered.preserves_type typing) thenIH elseIH

/-- Exact source provenance determines both the Core structure and its type;
equal result types alone do not identify another program. -/
theorem TypedLetReturnTreeElaborates.result_unique
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {leftCore rightCore : Core.Expr} {leftType rightType : Core.Ty}
    (left : TypedLetReturnTreeElaborates types owner inputs body leftCore leftType)
    (right : TypedLetReturnTreeElaborates types owner inputs body rightCore rightType) :
    leftCore = rightCore ∧ leftType = rightType :=
  Prod.mk.inj (Option.some.inj (left.complete.symm.trans right.complete))

theorem TypedLetReturnTreeHasType.type_unique
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {left right : Core.Ty}
    (first : TypedLetReturnTreeHasType types owner inputs body left)
    (second : TypedLetReturnTreeHasType types owner inputs body right) : left = right := by
  obtain ⟨_, firstElaboration⟩ := first.elaborates_exact
  obtain ⟨_, secondElaboration⟩ := second.elaborates_exact
  exact (firstElaboration.result_unique secondElaboration).2

theorem elaborateTypedLetReturnTree?_eq_none_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} : elaborateTypedLetReturnTree? types owner inputs body = none ↔
      ¬ ∃ type, TypedLetReturnTreeHasType types owner inputs body type := by
  constructor
  · intro rejected ⟨type, typing⟩
    obtain ⟨core, accepted⟩ := typing.elaborates
    rw [rejected] at accepted
    cases accepted
  · intro missing
    cases result : elaborateTypedLetReturnTree? types owner inputs body with
    | none => rfl
    | some pair => exact False.elim (missing ⟨pair.2, elaborateTypedLetReturnTree?_sound result⟩)

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.TypedLetReturnTreeEmbeddingProperties`
-/

/-! Every old tree and outer-prefix success retains its exact Core and type.
New branch-local bindings mean old checker failures are not generally preserved. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem TerminalReturnTreeHasType.typedLetReturnTree
    {inputs : LocalTypeInputs} {body : Syntax.Block} {type : Core.Ty}
    (typing : TerminalReturnTreeHasType inputs.names inputs.context body type)
    (types : TypeNameTable) (owner : Resolved.DeclarationId) :
    TypedLetReturnTreeHasType types owner inputs body type := by
  induction typing with
  | single child => exact .single child
  | conditional condition _ _ thenIH elseIH => exact .conditional condition thenIH elseIH

theorem TerminalReturnTreeElaborates.typedLetReturnTree
    {inputs : LocalTypeInputs} {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : TerminalReturnTreeElaborates inputs.names inputs.context body core type)
    (types : TypeNameTable) (owner : Resolved.DeclarationId) :
    TypedLetReturnTreeElaborates types owner inputs body core type := by
  induction elaboration with
  | single child => exact .single child
  | conditional resolution lowered typing _ _ thenIH elseIH =>
      exact .conditional resolution (by simpa only [LocalTypeInputs.context_ids] using lowered)
        typing thenIH elseIH

theorem TypedLetReturnBodyHasType.returnTree
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {type : Core.Ty}
    (typing : TypedLetReturnBodyHasType types owner inputs body type) :
    TypedLetReturnTreeHasType types owner inputs body type := by
  induction typing with
  | terminal child => exact child.typedLetReturnTree types owner
  | binding meaning unused initializerTyping _ ih => exact .binding meaning.structural unused initializerTyping ih

theorem TypedLetReturnBodyElaborates.returnTree
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : TypedLetReturnBodyElaborates types owner inputs body core type) :
    TypedLetReturnTreeElaborates types owner inputs body core type := by
  induction elaboration with
  | terminal child => exact child.typedLetReturnTree types owner
  | binding meaning unused resolution lowered typing _ ih =>
      exact .binding meaning.structural unused resolution lowered typing ih

theorem elaborateTypedLetReturnTree?_some_of_terminalReturnTree
    {inputs : LocalTypeInputs} {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (accepted : elaborateTerminalReturnTree? inputs.names inputs.context body = some (core, type)) :
    elaborateTypedLetReturnTree? types owner inputs body = some (core, type) :=
  ((elaborateTerminalReturnTree?_elaborates accepted).typedLetReturnTree types owner).complete

theorem elaborateTypedLetReturnTree?_some_of_typedLetReturnBody
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTypedLetReturnBody? types owner inputs body = some (core, type)) :
    elaborateTypedLetReturnTree? types owner inputs body = some (core, type) :=
  (elaborateTypedLetReturnBody?_elaborates accepted).returnTree.complete

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.TypedLetReturnTreeExecutionProperties`
-/

/-! Whole checked trees follow old-scope initializers and the selected arm.
Aligned IDs suffice for correspondence, without runtime typing. Exact-cost
paths retain the original continuation without executing its pending frames. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem elaborateTypedLetReturnTree?_evaluates_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {environment : Resolved.Environment} {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTypedLetReturnTree? types owner inputs body = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids inputs.context)
    {initialStore finalStore : Core.Store} {value : Core.Value} :
    TypedLetReturnTreeEvaluates owner inputs.names environment initialStore body value finalStore ↔
      Core.Evaluates (Resolved.LocalScope.values environment) initialStore core value finalStore := by
  have elaboration := elaborateTypedLetReturnTree?_elaborates accepted
  clear accepted
  induction elaboration generalizing environment initialStore finalStore value with
  | single child =>
      constructor
      · intro evaluation
        cases evaluation with
        | single evaluated => exact (elaborateReturnBody?_evaluates_iff child.complete sameIds).mp evaluated
        | block _ => cases child
        | binding _ _ => cases child
        | inferred _ _ => cases child
        | discard _ _ => cases child
        | ifTrue _ _ => cases child
        | ifFalse _ _ => cases child
      · intro evaluated
        exact .single ((elaborateReturnBody?_evaluates_iff child.complete sameIds).mpr evaluated)
  | block _ ih =>
      constructor
      · intro evaluation
        cases evaluation with
        | single child => cases child
        | block evaluated => exact (ih sameIds).mp evaluated
      · intro evaluated
        exact .block ((ih sameIds).mpr evaluated)
  | @binding inputs _ _ name _ _ _ declaredType _ _ _ _ _ _ resolution lowered typing _ ih =>
      have initializerAccepted := elaborateLocalExpression?_complete resolution
        (by simpa only [LocalTypeInputs.context_ids] using lowered) typing
      constructor
      · intro evaluation
        cases evaluation with
        | single child => cases child
        | binding initializer tail =>
            rename_i middleStore boundValue
            refine .letE ((elaborateLocalExpression?_evaluates_iff initializerAccepted sameIds).mp initializer) ?_
            apply (ih (environment := (Resolved.freshLocalId owner inputs.ids, boundValue) :: environment) ?_).mp
            · simpa only [LocalTypeInputs.bindFresh_names, LocalTypeInputs.names_ids] using tail
            · simpa only [LocalTypeInputs.bindFresh_context, Resolved.LocalScope.ids, List.map_cons]
                using congrArg (List.cons _) sameIds
      · intro evaluation
        cases evaluation with
        | letE initializer tail =>
            rename_i bodyStore boundValue
            apply TypedLetReturnTreeEvaluates.binding
              ((elaborateLocalExpression?_evaluates_iff initializerAccepted sameIds).mpr initializer)
            have tailEvaluation :=
              (ih (environment := (Resolved.freshLocalId owner inputs.ids, boundValue) :: environment) ?_).mpr tail
            · simpa only [LocalTypeInputs.bindFresh_names, LocalTypeInputs.names_ids] using tailEvaluation
            · simpa only [LocalTypeInputs.bindFresh_context, Resolved.LocalScope.ids, List.map_cons]
                using congrArg (List.cons _) sameIds
  | @inferred inputs _ _ name _ _ inferredType _ _ _ _ _ resolution lowered typing _ ih =>
      have initializerAccepted := elaborateLocalExpression?_complete resolution
        (by simpa only [LocalTypeInputs.context_ids] using lowered) typing
      constructor
      · intro evaluation
        cases evaluation with
        | single child => cases child
        | inferred initializer tail =>
            rename_i middleStore boundValue
            refine .letE ((elaborateLocalExpression?_evaluates_iff initializerAccepted sameIds).mp initializer) ?_
            apply (ih (environment := (Resolved.freshLocalId owner inputs.ids, boundValue) :: environment) ?_).mp
            · simpa only [LocalTypeInputs.bindFresh_names, LocalTypeInputs.names_ids] using tail
            · simpa only [LocalTypeInputs.bindFresh_context, Resolved.LocalScope.ids, List.map_cons]
                using congrArg (List.cons _) sameIds
      · intro evaluation
        cases evaluation with
        | letE initializer tail =>
            rename_i bodyStore boundValue
            apply TypedLetReturnTreeEvaluates.inferred
              ((elaborateLocalExpression?_evaluates_iff initializerAccepted sameIds).mpr initializer)
            have tailEvaluation :=
              (ih (environment := (Resolved.freshLocalId owner inputs.ids, boundValue) :: environment) ?_).mpr tail
            · simpa only [LocalTypeInputs.bindFresh_names, LocalTypeInputs.names_ids] using tailEvaluation
            · simpa only [LocalTypeInputs.bindFresh_context, Resolved.LocalScope.ids, List.map_cons]
                using congrArg (List.cons _) sameIds
  | discard resolution lowered typing tailElaboration ih =>
      have expressionAccepted := elaborateLocalExpression?_complete resolution
        (by simpa only [LocalTypeInputs.context_ids] using lowered) typing
      constructor
      · intro evaluation
        cases evaluation with
        | single child => cases child
        | discard expression tail =>
            rename_i middleStore discardedValue
            exact .letE ((elaborateLocalExpression?_evaluates_iff expressionAccepted sameIds).mp expression)
              (((ih sameIds).mp tail).weakenAt_zero_localFragment tailElaboration.localFragment discardedValue)
      · intro evaluation
        cases evaluation with
        | letE expression tail =>
            exact .discard ((elaborateLocalExpression?_evaluates_iff expressionAccepted sameIds).mpr expression)
              ((ih sameIds).mpr (tail.reflect_weakenAt_zero_localFragment tailElaboration.localFragment))
  | conditional resolution lowered typing _ _ thenIH elseIH =>
      have conditionAccepted := elaborateLocalExpression?_complete resolution
        (by simpa only [LocalTypeInputs.context_ids] using lowered) typing
      constructor
      · intro evaluation
        cases evaluation with
        | single child => cases child
        | ifTrue condition branch =>
            exact .ifTrue ((elaborateLocalExpression?_evaluates_iff conditionAccepted sameIds).mp condition)
              ((thenIH sameIds).mp branch)
        | ifFalse condition branch =>
            exact .ifFalse ((elaborateLocalExpression?_evaluates_iff conditionAccepted sameIds).mp condition)
              ((elseIH sameIds).mp branch)
      · intro evaluation
        cases evaluation with
        | ifTrue condition branch =>
            exact .ifTrue ((elaborateLocalExpression?_evaluates_iff conditionAccepted sameIds).mpr condition)
              ((thenIH sameIds).mpr branch)
        | ifFalse condition branch =>
            exact .ifFalse ((elaborateLocalExpression?_evaluates_iff conditionAccepted sameIds).mpr condition)
              ((elseIH sameIds).mpr branch)

theorem TypedLetReturnTreeEvaluatesWithCost.checked_toStepsWithContinuation
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {environment : Resolved.Environment} {initialStore finalStore : Core.Store}
    {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : TypedLetReturnTreeEvaluatesWithCost owner inputs.names environment
      initialStore body value finalStore cost)
    {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTypedLetReturnTree? types owner inputs body = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids inputs.context)
    (continuation : List Core.Frame) :
    Core.Steps cost
      ⟨.eval core (Resolved.LocalScope.values environment), continuation, initialStore⟩
      ⟨.ret value, continuation, finalStore⟩ := by
  have elaboration := elaborateTypedLetReturnTree?_elaborates accepted
  clear accepted
  induction elaboration generalizing environment initialStore finalStore value cost continuation with
  | single child =>
      cases evaluation with
      | single evaluated => exact evaluated.checked_toStepsWithContinuation child.complete sameIds continuation
      | block _ => cases child
      | binding _ _ => cases child
      | inferred _ _ => cases child
      | discard _ _ => cases child
      | ifTrue _ _ => cases child
      | ifFalse _ _ => cases child
  | block _ ih =>
      cases evaluation with
      | single child => cases child
      | block evaluated => exact ih evaluated sameIds continuation
  | @binding inputs _ _ _ _ _ _ _ _ _ _ _ _ _ resolution lowered _ _ ih =>
      cases evaluation with
      | single child => cases child
      | binding initializer tail =>
          rename_i middleStore boundValue initializerCost tailCost
          have runtimeLowered := lowered
          rw [← LocalTypeInputs.context_ids, ← sameIds] at runtimeLowered
          apply CostStepComposition.letE (initializer.toStepsWithContinuation resolution runtimeLowered _)
          apply ih (environment := (Resolved.freshLocalId owner inputs.ids, boundValue) :: environment)
          · simpa only [LocalTypeInputs.bindFresh_names, LocalTypeInputs.names_ids] using tail
          · simpa only [LocalTypeInputs.bindFresh_context, Resolved.LocalScope.ids, List.map_cons]
              using congrArg (List.cons _) sameIds
  | @inferred inputs _ _ _ _ _ _ _ _ _ _ _ resolution lowered _ _ ih =>
      cases evaluation with
      | single child => cases child
      | inferred initializer tail =>
          rename_i middleStore boundValue initializerCost tailCost
          have runtimeLowered := lowered
          rw [← LocalTypeInputs.context_ids, ← sameIds] at runtimeLowered
          apply CostStepComposition.letE (initializer.toStepsWithContinuation resolution runtimeLowered _)
          apply ih (environment := (Resolved.freshLocalId owner inputs.ids, boundValue) :: environment)
          · simpa only [LocalTypeInputs.bindFresh_names, LocalTypeInputs.names_ids] using tail
          · simpa only [LocalTypeInputs.bindFresh_context, Resolved.LocalScope.ids, List.map_cons]
              using congrArg (List.cons _) sameIds
  | discard resolution lowered _ tailElaboration ih =>
      cases evaluation with
      | single child => cases child
      | discard expression tail =>
          rename_i middleStore discardedValue expressionCost tailCost
          have runtimeLowered := lowered
          rw [← LocalTypeInputs.context_ids, ← sameIds] at runtimeLowered
          have tailPath := ih tail sameIds []
          exact CostStepComposition.letE (expression.toStepsWithContinuation resolution runtimeLowered _)
            (tailPath.weakenAt_zero_localFragment tailElaboration.localFragment discardedValue continuation)
  | conditional resolution lowered _ _ _ thenIH elseIH =>
      have runtimeLowered := lowered
      rw [← LocalTypeInputs.context_ids, ← sameIds] at runtimeLowered
      cases evaluation with
      | single child => cases child
      | ifTrue condition branch =>
          exact CostStepComposition.ifTrue (condition.toStepsWithContinuation resolution runtimeLowered _)
            (thenIH branch sameIds continuation)
      | ifFalse condition branch =>
          exact CostStepComposition.ifFalse (condition.toStepsWithContinuation resolution runtimeLowered _)
            (elseIH branch sameIds continuation)

theorem TypedLetReturnTreeEvaluatesWithCost.checked_toSteps
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {environment : Resolved.Environment} {initialStore finalStore : Core.Store}
    {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : TypedLetReturnTreeEvaluatesWithCost owner inputs.names environment
      initialStore body value finalStore cost)
    {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTypedLetReturnTree? types owner inputs body = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids inputs.context) :
    Core.Steps cost (Core.State.initial core (Resolved.LocalScope.values environment) initialStore)
      (Core.State.final value finalStore) :=
  evaluation.checked_toStepsWithContinuation accepted sameIds []

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.TypedLetReturnTreeOwnerProperties`
-/

/-! Owner-only relabeling preserves independent recursive provenance and whole
checker results. Fresh tails and both original-scope siblings are transported
without inverse owner maps or inhabitants for static input types. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem TypedLetReturnTreeElaborates.mapOwner
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : TypedLetReturnTreeElaborates types owner inputs body core type)
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (injective : Function.Injective mapping) :
    TypedLetReturnTreeElaborates types (mapping owner)
      (inputs.mapIds (ownerLocalIdMap mapping)
        (ownerLocalIdMap_injective mapping injective)) body core type := by
  induction elaboration with
  | single child =>
      apply TypedLetReturnTreeElaborates.single
      simpa only [LocalTypeInputs.mapIds_names, LocalTypeInputs.mapIds_context] using
        (child.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective))
  | block _ ih => exact .block ih
  | @binding inputs blockSpan letSpan name annotation initializer rest declaredType returnType
      resolved initializerCore tailCore meaning unused resolution lowered typing _ ih =>
      refine .binding (initializerResolved := resolved.renameIds (ownerLocalIdMap mapping))
        meaning ?_ ?_ ?_ ?_ ?_
      · simpa only [LocalTypeInputs.mapIds_names, LocalNameTable.mapIds,
          List.map_map, Function.comp_def] using unused
      · simpa only [LocalTypeInputs.mapIds_names] using (resolution.mapIds (ownerLocalIdMap mapping))
      · simpa only [LocalTypeInputs.mapIds_ids] using
          (Resolved.lowers_renameIds_iff (ownerLocalIdMap mapping)
            (ownerLocalIdMap_injective mapping injective)).mpr lowered
      · simpa only [LocalTypeInputs.mapIds_context] using
          (Resolved.typing_renameIds_iff (ownerLocalIdMap mapping)
            (ownerLocalIdMap_injective mapping injective)).mpr typing
      · simpa only [LocalTypeInputs.bindFresh_mapOwner inputs owner mapping injective] using ih
  | @inferred inputs blockSpan letSpan name initializer rest initializerType returnType
      resolved initializerCore tailCore unused resolution lowered typing _ ih =>
      refine .inferred (inferredType := initializerType)
        (initializerResolved := resolved.renameIds (ownerLocalIdMap mapping))
        ?_ ?_ ?_ ?_ ?_
      · simpa only [LocalTypeInputs.mapIds_names, LocalNameTable.mapIds,
          List.map_map, Function.comp_def] using unused
      · simpa only [LocalTypeInputs.mapIds_names] using (resolution.mapIds (ownerLocalIdMap mapping))
      · simpa only [LocalTypeInputs.mapIds_ids] using
          (Resolved.lowers_renameIds_iff (ownerLocalIdMap mapping)
            (ownerLocalIdMap_injective mapping injective)).mpr lowered
      · simpa only [LocalTypeInputs.mapIds_context] using
          (Resolved.typing_renameIds_iff (ownerLocalIdMap mapping)
            (ownerLocalIdMap_injective mapping injective)).mpr typing
      · simpa only [LocalTypeInputs.bindFresh_mapOwner inputs owner mapping injective] using ih
  | @discard inputs blockSpan statementSpan expression rest discardedType returnType
      resolved expressionCore tailCore resolution lowered typing _ ih =>
      refine .discard (discardedType := discardedType)
        (resolved := resolved.renameIds (ownerLocalIdMap mapping)) ?_ ?_ ?_ ih
      · simpa only [LocalTypeInputs.mapIds_names] using (resolution.mapIds (ownerLocalIdMap mapping))
      · simpa only [LocalTypeInputs.mapIds_ids] using
          (Resolved.lowers_renameIds_iff (ownerLocalIdMap mapping)
            (ownerLocalIdMap_injective mapping injective)).mpr lowered
      · simpa only [LocalTypeInputs.mapIds_context] using
          (Resolved.typing_renameIds_iff (ownerLocalIdMap mapping)
            (ownerLocalIdMap_injective mapping injective)).mpr typing
  | @conditional inputs blockSpan ifSpan condition thenBody elseBody resolved
      conditionCore thenCore elseCore type resolution lowered typing _ _ thenIH elseIH =>
      refine .conditional (conditionResolved := resolved.renameIds (ownerLocalIdMap mapping))
        ?_ ?_ ?_ thenIH elseIH
      · simpa only [LocalTypeInputs.mapIds_names] using (resolution.mapIds (ownerLocalIdMap mapping))
      · simpa only [LocalTypeInputs.mapIds_ids] using
          (Resolved.lowers_renameIds_iff (ownerLocalIdMap mapping)
            (ownerLocalIdMap_injective mapping injective)).mpr lowered
      · simpa only [LocalTypeInputs.mapIds_context] using
          (Resolved.typing_renameIds_iff (ownerLocalIdMap mapping)
            (ownerLocalIdMap_injective mapping injective)).mpr typing

theorem TypedLetReturnTreeHasType.mapOwner
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {type : Core.Ty}
    (typing : TypedLetReturnTreeHasType types owner inputs body type)
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (injective : Function.Injective mapping) :
    TypedLetReturnTreeHasType types (mapping owner)
      (inputs.mapIds (ownerLocalIdMap mapping)
        (ownerLocalIdMap_injective mapping injective)) body type := by
  obtain ⟨core, elaboration⟩ := typing.elaborates_exact
  exact (elaboration.mapOwner mapping injective).hasType

/-- Recursion on the original syntax also preserves rejection for non-surjective
owner maps. Both conditional arms retain their own original input scope. -/
theorem elaborateTypedLetReturnTree?_mapOwner
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (injective : Function.Injective mapping) (types : TypeNameTable)
    (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs) (body : Syntax.Block) :
    elaborateTypedLetReturnTree? types (mapping owner)
        (inputs.mapIds (ownerLocalIdMap mapping)
          (ownerLocalIdMap_injective mapping injective)) body =
      elaborateTypedLetReturnTree? types owner inputs body := by
  cases body with
  | mk blockSpan statements =>
      cases statements with
      | nil => simp only [elaborateTypedLetReturnTree?]
      | cons statement rest =>
          cases statement with
          | mk statementSpan payload =>
              cases payload <;> try simp only [elaborateTypedLetReturnTree?]
              case returnStmt returned =>
                cases rest with
                | nil =>
                    simp only [elaborateTypedLetReturnTree?_single,
                      LocalTypeInputs.mapIds_names, LocalTypeInputs.mapIds_context,
                      elaborateReturnBody?_mapIds (ownerLocalIdMap mapping)
                        (ownerLocalIdMap_injective mapping injective)]
                | cons _ _ => simp only [elaborateTypedLetReturnTree?]
              case block statements =>
                cases rest with
                | nil => simpa only [elaborateTypedLetReturnTree?_block] using
                    elaborateTypedLetReturnTree?_mapOwner mapping injective types owner inputs ⟨statementSpan, statements⟩
                | cons _ _ => simp only [elaborateTypedLetReturnTree?]
              case letDecl name optionalType optionalInitializer =>
                cases optionalType with
                | none =>
                    cases optionalInitializer with
                    | none => simp only [elaborateTypedLetReturnTree?]
                    | some initializer =>
                        have tailSame (initializerType : Core.Ty) :=
                          elaborateTypedLetReturnTree?_mapOwner mapping injective types owner
                            (inputs.bindFresh owner name.value initializerType) ⟨blockSpan, rest⟩
                        rw [elaborateTypedLetReturnTree?, elaborateTypedLetReturnTree?]
                        simp only [LocalTypeInputs.mapIds_names, LocalTypeInputs.mapIds_context]
                        rw [elaborateLocalExpression?_mapIds (ownerLocalIdMap mapping)
                          (ownerLocalIdMap_injective mapping injective)]
                        simp only [LocalNameTable.mapIds, List.map_map, Function.comp_def,
                          ← LocalTypeInputs.bindFresh_mapOwner inputs owner mapping injective name.value,
                          tailSame]
                | some annotation =>
                    cases optionalInitializer with
                    | none => simp only [elaborateTypedLetReturnTree?]
                    | some initializer =>
                        have tailSame (declaredType : Core.Ty) :=
                          elaborateTypedLetReturnTree?_mapOwner mapping injective types owner
                            (inputs.bindFresh owner name.value declaredType) ⟨blockSpan, rest⟩
                        rw [elaborateTypedLetReturnTree?, elaborateTypedLetReturnTree?]
                        simp only [LocalTypeInputs.mapIds_names, LocalTypeInputs.mapIds_context]
                        rw [elaborateLocalExpression?_mapIds (ownerLocalIdMap mapping)
                          (ownerLocalIdMap_injective mapping injective)]
                        simp only [LocalNameTable.mapIds, List.map_map, Function.comp_def,
                          ← LocalTypeInputs.bindFresh_mapOwner inputs owner mapping injective name.value,
                          tailSame]
              case ifThen condition thenBody optionalElse =>
                cases rest with
                | cons _ _ => simp only [elaborateTypedLetReturnTree?]
                | nil =>
                    cases optionalElse with
                    | none => simp only [elaborateTypedLetReturnTree?]
                    | some elseBody =>
                        rw [elaborateTypedLetReturnTree?, elaborateTypedLetReturnTree?]
                        simp only [LocalTypeInputs.mapIds_names, LocalTypeInputs.mapIds_context]
                        rw [elaborateLocalExpression?_mapIds (ownerLocalIdMap mapping)
                          (ownerLocalIdMap_injective mapping injective),
                          elaborateTypedLetReturnTree?_mapOwner mapping injective types owner inputs thenBody,
                          elaborateTypedLetReturnTree?_mapOwner mapping injective types owner inputs elseBody]
              case expression source trailingSemicolon =>
                cases trailingSemicolon with
                | false => simp only [elaborateTypedLetReturnTree?]
                | true =>
                    rw [elaborateTypedLetReturnTree?, elaborateTypedLetReturnTree?]
                    simp only [LocalTypeInputs.mapIds_names, LocalTypeInputs.mapIds_context]
                    rw [elaborateLocalExpression?_mapIds (ownerLocalIdMap mapping)
                      (ownerLocalIdMap_injective mapping injective),
                      elaborateTypedLetReturnTree?_mapOwner mapping injective types owner inputs ⟨blockSpan, rest⟩]
termination_by sizeOf body

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.TypedLetReturnTreeRunnerEmbeddingProperties`
-/

/-! Singleton returns retain rejection and complete same-fuel results. Other
old profiles embed successful full results only: branch-local lets add success,
so arbitrary old and new optional results are not identified. -/

set_option autoImplicit false

namespace Solcore.Frontend.LocalInputs

theorem runTypedLetReturnTree?_single
    (inputs : LocalInputs) (types : TypeNameTable) (owner : Resolved.DeclarationId) (fuel : Nat)
    (returned : Option Syntax.Expr) (blockSpan returnSpan : Syntax.SourceSpan) (store : Core.Store) :
    inputs.runTypedLetReturnTree? types owner fuel ⟨blockSpan, [⟨returnSpan, .returnStmt returned⟩]⟩ store =
      inputs.runReturnBody? fuel ⟨blockSpan, [⟨returnSpan, .returnStmt returned⟩]⟩ store := by
  simp only [runTypedLetReturnTree?, checkTypedLetReturnTree?, runReturnBody?, checkReturnBody?,
    elaborateTypedLetReturnTree?_single, toTypeInputs_names, toTypeInputs_context]

theorem runTypedLetReturnTree?_some_of_terminalReturnTree
    {inputs : LocalInputs} {body : Syntax.Block} {fuel : Nat} {store : Core.Store}
    {type : Core.Ty} {result : Core.StatefulRunResult}
    (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (accepted : inputs.runTerminalReturnTree? fuel body store = some (type, result)) :
    inputs.runTypedLetReturnTree? types owner fuel body store = some (type, result) := by
  cases checked : inputs.checkTerminalReturnTree? body with
  | none => simp [runTerminalReturnTree?, checked] at accepted
  | some pair =>
      obtain ⟨core, checkedType⟩ := pair
      have oldChecked : elaborateTerminalReturnTree? inputs.toTypeInputs.names inputs.toTypeInputs.context body =
          some (core, checkedType) := by
        simpa only [checkTerminalReturnTree?, toTypeInputs_names, toTypeInputs_context] using checked
      have preserved : inputs.checkTypedLetReturnTree? types owner body = some (core, checkedType) :=
        elaborateTypedLetReturnTree?_some_of_terminalReturnTree types owner oldChecked
      simpa only [runTypedLetReturnTree?, runTerminalReturnTree?, checked, preserved] using accepted

theorem runTypedLetReturnTree?_some_of_typedLetReturnBody
    {inputs : LocalInputs} {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {body : Syntax.Block} {fuel : Nat} {store : Core.Store} {type : Core.Ty} {result : Core.StatefulRunResult}
    (accepted : inputs.runTypedLetReturnBody? types owner fuel body store = some (type, result)) :
    inputs.runTypedLetReturnTree? types owner fuel body store = some (type, result) := by
  cases checked : inputs.checkTypedLetReturnBody? types owner body with
  | none => simp [runTypedLetReturnBody?, checked] at accepted
  | some pair =>
      obtain ⟨core, checkedType⟩ := pair
      have preserved : inputs.checkTypedLetReturnTree? types owner body = some (core, checkedType) :=
        elaborateTypedLetReturnTree?_some_of_typedLetReturnBody checked
      simpa only [runTypedLetReturnTree?, runTypedLetReturnBody?, checked, preserved] using accepted

end Solcore.Frontend.LocalInputs

/-!
## Consolidated module: `Solcore.Frontend.TypedLetReturnTreeRunnerOwnerProperties`
-/

/-! Fixed-store owner relabeling preserves every optional result and actual
checkpoint. The original positional values are neither renamed nor reordered. -/

set_option autoImplicit false

namespace Solcore.Frontend.LocalInputs

theorem checkTypedLetReturnTree?_mapOwner (inputs : LocalInputs)
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (injective : Function.Injective mapping) (types : TypeNameTable)
    (owner : Resolved.DeclarationId) (body : Syntax.Block) :
    (inputs.mapIds (ownerLocalIdMap mapping)
        (ownerLocalIdMap_injective mapping injective)).checkTypedLetReturnTree? types (mapping owner) body =
      inputs.checkTypedLetReturnTree? types owner body := by
  simp only [checkTypedLetReturnTree?, toTypeInputs_mapIds,
    elaborateTypedLetReturnTree?_mapOwner mapping injective]

theorem runTypedLetReturnTree?_mapOwner (inputs : LocalInputs)
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (injective : Function.Injective mapping) (types : TypeNameTable)
    (owner : Resolved.DeclarationId) (fuel : Nat) (body : Syntax.Block) (store : Core.Store) :
    (inputs.mapIds (ownerLocalIdMap mapping)
        (ownerLocalIdMap_injective mapping injective)).runTypedLetReturnTree? types (mapping owner) fuel body store =
      inputs.runTypedLetReturnTree? types owner fuel body store := by
  simp only [runTypedLetReturnTree?, checkTypedLetReturnTree?_mapOwner inputs mapping injective,
    mapIds_environment, Resolved.LocalScope.values_mapIds]

end Solcore.Frontend.LocalInputs

/-!
## Consolidated module: `Solcore.Frontend.TypedLetReturnTreeRunnerProperties`
-/

/-! Whole recursive checking and independent costs determine exact thresholds.
Known paths need only aligned IDs. Actual typed inputs separately supply paths,
without manufacturing values for arbitrary static types. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem TypedLetReturnTreeEvaluatesWithCost.checked_runStateful_done_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {environment : Resolved.Environment} {initialStore finalStore : Core.Store}
    {body : Syntax.Block} {value : Core.Value} {cost fuel : Nat}
    (evaluation : TypedLetReturnTreeEvaluatesWithCost owner inputs.names environment initialStore body value finalStore cost)
    {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTypedLetReturnTree? types owner inputs body = some (core, type))
    (sameIds : environment.ids = inputs.context.ids) :
    Core.runStateful fuel (Core.State.initial core environment.values initialStore) = .done value finalStore ↔ cost ≤ fuel :=
  (evaluation.checked_toSteps accepted sameIds).runStateful_done_iff

theorem TypedLetReturnTreeEvaluatesWithCost.checked_runStateful_outOfFuel_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {environment : Resolved.Environment} {initialStore finalStore : Core.Store}
    {body : Syntax.Block} {value : Core.Value} {cost fuel : Nat}
    (evaluation : TypedLetReturnTreeEvaluatesWithCost owner inputs.names environment initialStore body value finalStore cost)
    {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTypedLetReturnTree? types owner inputs body = some (core, type))
    (sameIds : environment.ids = inputs.context.ids) :
    (∃ suspended, Core.runStateful fuel (Core.State.initial core environment.values initialStore) =
      .outOfFuel suspended) ↔ fuel < cost :=
  (evaluation.checked_toSteps accepted sameIds).runStateful_outOfFuel_iff

theorem elaborateTypedLetReturnTree?_run_done_iff_cost
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {environment : Resolved.Environment} {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTypedLetReturnTree? types owner inputs body = some (core, type))
    (sameIds : environment.ids = inputs.context.ids)
    {initialStore finalStore : Core.Store} {value : Core.Value} {fuel : Nat} :
    Core.runStateful fuel (Core.State.initial core environment.values initialStore) = .done value finalStore ↔
      ∃ cost, TypedLetReturnTreeEvaluatesWithCost owner inputs.names environment
        initialStore body value finalStore cost ∧ cost ≤ fuel := by
  constructor
  · intro completed
    have evaluation := (elaborateTypedLetReturnTree?_evaluates_iff accepted sameIds).mpr
      (Core.runStateful_evaluation_sound completed)
    obtain ⟨cost, costed⟩ := evaluation.exists_cost
    exact ⟨cost, costed, (costed.checked_runStateful_done_iff accepted sameIds).mp completed⟩
  · rintro ⟨cost, costed, enough⟩
    exact (costed.checked_runStateful_done_iff accepted sameIds).mpr enough

namespace LocalInputs

private theorem aligned (inputs : LocalInputs) : inputs.environment.ids = inputs.toTypeInputs.context.ids := by
  simpa only [toTypeInputs_context] using inputs.sameIds

private theorem actualTypes (inputs : LocalInputs) :
    Core.EnvironmentHasTypes inputs.environment.values inputs.toTypeInputs.context.values := by
  simpa only [toTypeInputs_context] using inputs.environmentTyped

theorem runTypedLetReturnTree?_eq_none_iff
    {inputs : LocalInputs} {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {body : Syntax.Block} {fuel : Nat} {store : Core.Store} :
    inputs.runTypedLetReturnTree? types owner fuel body store = none ↔
      inputs.checkTypedLetReturnTree? types owner body = none := by
  cases checked : inputs.checkTypedLetReturnTree? types owner body with
  | none => simp [runTypedLetReturnTree?, checked]
  | some pair => rcases pair with ⟨core, type⟩; simp [runTypedLetReturnTree?, checked]

theorem runTypedLetReturnTree?_eq_some_iff
    {inputs : LocalInputs} {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {body : Syntax.Block} {fuel : Nat} {store : Core.Store} {type : Core.Ty} {result : Core.StatefulRunResult} :
    inputs.runTypedLetReturnTree? types owner fuel body store = some (type, result) ↔
      ∃ core, inputs.checkTypedLetReturnTree? types owner body = some (core, type) ∧
        Core.runStateful fuel (Core.State.initial core inputs.environment.values store) = result := by
  simp only [runTypedLetReturnTree?, bind, Option.bind_eq_some_iff, pure]
  constructor
  · rintro ⟨⟨core, actualType⟩, checked, same⟩
    cases same
    exact ⟨core, checked, rfl⟩
  · rintro ⟨core, checked, resultEq⟩
    exact ⟨(core, type), checked, by simp only [resultEq]⟩

theorem runTypedLetReturnTree?_done_iff_typed_cost
    {inputs : LocalInputs} {types : TypeNameTable} {owner : Resolved.DeclarationId} {body : Syntax.Block}
    {initialStore finalStore : Core.Store} {type : Core.Ty} {value : Core.Value} {fuel : Nat} :
    inputs.runTypedLetReturnTree? types owner fuel body initialStore = some (type, .done value finalStore) ↔
      TypedLetReturnTreeHasType types owner inputs.toTypeInputs body type ∧
      ∃ cost, TypedLetReturnTreeEvaluatesWithCost owner inputs.names inputs.environment
        initialStore body value finalStore cost ∧ cost ≤ fuel := by
  constructor
  · intro completed
    obtain ⟨core, checked, execution⟩ := runTypedLetReturnTree?_eq_some_iff.mp completed
    refine ⟨elaborateTypedLetReturnTree?_sound checked, ?_⟩
    simpa only [toTypeInputs_names] using
      (elaborateTypedLetReturnTree?_run_done_iff_cost checked (aligned inputs)).mp execution
  · rintro ⟨typing, cost, costed, enough⟩
    obtain ⟨core, checked⟩ := typing.elaborates
    rw [← toTypeInputs_names inputs] at costed
    exact runTypedLetReturnTree?_eq_some_iff.mpr ⟨core, checked,
      (costed.checked_runStateful_done_iff checked (aligned inputs)).mpr enough⟩

/-- Values and exact thresholds come from actual typed inputs. A static type
or a raw path through rejected source is not sufficient for this wrapper. -/
theorem typedLetReturnTree_typed_cost_execution
    {inputs : LocalInputs} {types : TypeNameTable} {owner : Resolved.DeclarationId} {body : Syntax.Block} {type : Core.Ty}
    (typing : TypedLetReturnTreeHasType types owner inputs.toTypeInputs body type) (store : Core.Store) :
    ∃ value cost, TypedLetReturnTreeEvaluatesWithCost owner inputs.names inputs.environment
        store body value store cost ∧ Core.ValueHasType value type ∧ ∀ fuel,
      (inputs.runTypedLetReturnTree? types owner fuel body store = some (type, .done value store) ↔ cost ≤ fuel) ∧
      ((∃ suspended, inputs.runTypedLetReturnTree? types owner fuel body store =
        some (type, .outOfFuel suspended)) ↔ fuel < cost) := by
  obtain ⟨core, checked⟩ := typing.elaborates
  obtain ⟨value, evaluated, valueTyped⟩ := typing.evaluates (aligned inputs) (actualTypes inputs) store
  obtain ⟨cost, costed⟩ := evaluated.exists_cost
  refine ⟨value, cost, by simpa only [toTypeInputs_names] using costed, valueTyped, fun fuel => ?_⟩
  have boundaries := And.intro (costed.checked_runStateful_done_iff checked (aligned inputs) (fuel := fuel))
    (costed.checked_runStateful_outOfFuel_iff checked (aligned inputs) (fuel := fuel))
  simpa only [runTypedLetReturnTree?, checkTypedLetReturnTree?, checked, bind, Option.bind_some, pure,
    Option.some.injEq, Prod.mk.injEq, true_and] using boundaries

theorem runTypedLetReturnTree?_outOfFuel_iff_typed_cost
    {inputs : LocalInputs} {types : TypeNameTable} {owner : Resolved.DeclarationId} {body : Syntax.Block}
    {store : Core.Store} {type : Core.Ty} {fuel : Nat} :
    (∃ suspended, inputs.runTypedLetReturnTree? types owner fuel body store = some (type, .outOfFuel suspended)) ↔
      TypedLetReturnTreeHasType types owner inputs.toTypeInputs body type ∧
      ∃ value cost, TypedLetReturnTreeEvaluatesWithCost owner inputs.names inputs.environment
        store body value store cost ∧ fuel < cost := by
  constructor
  · rintro ⟨suspended, exhausted⟩
    obtain ⟨core, checked, _⟩ := runTypedLetReturnTree?_eq_some_iff.mp exhausted
    have typing := elaborateTypedLetReturnTree?_sound checked
    obtain ⟨value, cost, costed, _, boundaries⟩ :=
      typedLetReturnTree_typed_cost_execution (inputs := inputs) typing store
    exact ⟨typing, value, cost, costed, (boundaries fuel).2.mp ⟨suspended, exhausted⟩⟩
  · rintro ⟨typing, value, cost, costed, short⟩
    obtain ⟨core, checked⟩ := typing.elaborates
    rw [← toTypeInputs_names inputs] at costed
    obtain ⟨suspended, exhausted⟩ :=
      (costed.checked_runStateful_outOfFuel_iff checked (aligned inputs)).mpr short
    exact ⟨suspended, runTypedLetReturnTree?_eq_some_iff.mpr ⟨core, checked, exhausted⟩⟩

theorem runTypedLetReturnTree?_never_faults (inputs : LocalInputs) (types : TypeNameTable)
    (owner : Resolved.DeclarationId) (body : Syntax.Block) (fuel : Nat) (store : Core.Store)
    (type : Core.Ty) (error : Core.MachineFault) (faultState : Core.State) :
    inputs.runTypedLetReturnTree? types owner fuel body store ≠ some (type, .fault error faultState) := by
  intro fault
  obtain ⟨core, checked, _⟩ := runTypedLetReturnTree?_eq_some_iff.mp fault
  have typing := elaborateTypedLetReturnTree?_sound checked
  obtain ⟨value, cost, _, _, boundaries⟩ :=
    typedLetReturnTree_typed_cost_execution (inputs := inputs) typing store
  by_cases enough : cost ≤ fuel
  · have completed := (boundaries fuel).1.mpr enough
    rw [completed] at fault
    cases fault
  · obtain ⟨suspended, exhausted⟩ := (boundaries fuel).2.mpr (by omega)
    rw [exhausted] at fault
    cases fault

end LocalInputs
end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.TypedLetReturnTreeEvaluatorExecutionProperties`
-/

/-! Whole checking and aligned actual IDs separately connect direct recursive
results to the checked machine. Raw success is not source acceptance, and a
retained-continuation path ends before its pending frames execute. -/
set_option autoImplicit false
namespace Solcore.Frontend

theorem evaluateTypedLetReturnTreeWithCost?_checked_toStepsWithContinuation
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {environment : Resolved.Environment} {body : Syntax.Block} {value : Core.Value}
    {cost : Nat} {core : Core.Expr} {type : Core.Ty} {store : Core.Store}
    (evaluated : evaluateTypedLetReturnTreeWithCost? owner inputs.names environment body = some (value, cost))
    (accepted : elaborateTypedLetReturnTree? types owner inputs body = some (core, type))
    (sameIds : environment.ids = inputs.context.ids) (continuation : List Core.Frame) :
    Core.Steps cost ⟨.eval core environment.values, continuation, store⟩
      ⟨.ret value, continuation, store⟩ :=
  (evaluateTypedLetReturnTreeWithCost?_sound evaluated store).checked_toStepsWithContinuation accepted sameIds continuation

theorem evaluateTypedLetReturnTreeWithCost?_checked_runStateful_done_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {environment : Resolved.Environment} {body : Syntax.Block} {value : Core.Value}
    {cost fuel : Nat} {core : Core.Expr} {type : Core.Ty} {store : Core.Store}
    (evaluated : evaluateTypedLetReturnTreeWithCost? owner inputs.names environment body = some (value, cost))
    (accepted : elaborateTypedLetReturnTree? types owner inputs body = some (core, type))
    (sameIds : environment.ids = inputs.context.ids) :
    Core.runStateful fuel (Core.State.initial core environment.values store) = .done value store ↔ cost ≤ fuel :=
  (evaluateTypedLetReturnTreeWithCost?_sound evaluated store).checked_runStateful_done_iff accepted sameIds

theorem evaluateTypedLetReturnTreeWithCost?_checked_runStateful_outOfFuel_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {environment : Resolved.Environment} {body : Syntax.Block} {value : Core.Value}
    {cost fuel : Nat} {core : Core.Expr} {type : Core.Ty} {store : Core.Store}
    (evaluated : evaluateTypedLetReturnTreeWithCost? owner inputs.names environment body = some (value, cost))
    (accepted : elaborateTypedLetReturnTree? types owner inputs body = some (core, type))
    (sameIds : environment.ids = inputs.context.ids) :
    (∃ checkpoint, Core.runStateful fuel (Core.State.initial core environment.values store) = .outOfFuel checkpoint) ↔ fuel < cost :=
  (evaluateTypedLetReturnTreeWithCost?_sound evaluated store).checked_runStateful_outOfFuel_iff accepted sameIds

/-- Final-store equality remains explicit even though the direct evaluator has
no store parameter. Known checked completion needs no runtime typing premise. -/
theorem elaborateTypedLetReturnTree?_run_done_iff_evaluator
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {environment : Resolved.Environment} {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTypedLetReturnTree? types owner inputs body = some (core, type))
    (sameIds : environment.ids = inputs.context.ids)
    {initialStore finalStore : Core.Store} {value : Core.Value} {fuel : Nat} :
    Core.runStateful fuel (Core.State.initial core environment.values initialStore) = .done value finalStore ↔
      finalStore = initialStore ∧ ∃ cost,
        evaluateTypedLetReturnTreeWithCost? owner inputs.names environment body = some (value, cost) ∧ cost ≤ fuel := by
  rw [elaborateTypedLetReturnTree?_run_done_iff_cost accepted sameIds]
  constructor
  · rintro ⟨cost, evaluated, enough⟩
    exact ⟨evaluated.store_eq, cost, evaluateTypedLetReturnTreeWithCost?_complete evaluated, enough⟩
  · rintro ⟨rfl, cost, evaluated, enough⟩
    exact ⟨cost, evaluateTypedLetReturnTreeWithCost?_sound evaluated _, enough⟩

theorem elaborateTypedLetReturnTree?_typed_evaluator_exists
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {environment : Resolved.Environment} {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTypedLetReturnTree? types owner inputs body = some (core, type))
    (sameIds : environment.ids = inputs.context.ids)
    (environmentTyped : Core.EnvironmentHasTypes environment.values inputs.context.values) :
    ∃ value cost, evaluateTypedLetReturnTreeWithCost? owner inputs.names environment body = some (value, cost) ∧
      Core.ValueHasType value type := by
  obtain ⟨value, evaluated, typed⟩ :=
    (elaborateTypedLetReturnTree?_sound accepted).evaluates sameIds environmentTyped []
  obtain ⟨cost, costed⟩ := evaluated.exists_cost
  exact ⟨value, cost, evaluateTypedLetReturnTreeWithCost?_complete costed, typed⟩

namespace LocalInputs

theorem runTypedLetReturnTree?_done_iff_evaluator
    {inputs : LocalInputs} {types : TypeNameTable} {owner : Resolved.DeclarationId} {body : Syntax.Block}
    {initialStore finalStore : Core.Store} {type : Core.Ty} {value : Core.Value} {fuel : Nat} :
    inputs.runTypedLetReturnTree? types owner fuel body initialStore = some (type, .done value finalStore) ↔
      TypedLetReturnTreeHasType types owner inputs.toTypeInputs body type ∧ finalStore = initialStore ∧
      ∃ cost, evaluateTypedLetReturnTreeWithCost? owner inputs.names inputs.environment body = some (value, cost) ∧ cost ≤ fuel := by
  rw [runTypedLetReturnTree?_done_iff_typed_cost]
  constructor
  · rintro ⟨typing, cost, evaluated, enough⟩
    exact ⟨typing, evaluated.store_eq, cost, evaluateTypedLetReturnTreeWithCost?_complete evaluated, enough⟩
  · rintro ⟨typing, rfl, cost, evaluated, enough⟩
    exact ⟨typing, cost, evaluateTypedLetReturnTreeWithCost?_sound evaluated _, enough⟩

theorem runTypedLetReturnTree?_outOfFuel_iff_evaluator
    {inputs : LocalInputs} {types : TypeNameTable} {owner : Resolved.DeclarationId} {body : Syntax.Block}
    {store : Core.Store} {type : Core.Ty} {fuel : Nat} :
    (∃ checkpoint, inputs.runTypedLetReturnTree? types owner fuel body store = some (type, .outOfFuel checkpoint)) ↔
      TypedLetReturnTreeHasType types owner inputs.toTypeInputs body type ∧
      ∃ value cost, evaluateTypedLetReturnTreeWithCost? owner inputs.names inputs.environment body = some (value, cost) ∧ fuel < cost := by
  rw [runTypedLetReturnTree?_outOfFuel_iff_typed_cost]
  constructor
  · rintro ⟨typing, value, cost, evaluated, short⟩
    exact ⟨typing, value, cost, evaluateTypedLetReturnTreeWithCost?_complete evaluated, short⟩
  · rintro ⟨typing, value, cost, evaluated, short⟩
    exact ⟨typing, value, cost, evaluateTypedLetReturnTreeWithCost?_sound evaluated store, short⟩

theorem typedLetReturnTree_evaluator_execution
    {inputs : LocalInputs} {types : TypeNameTable} {owner : Resolved.DeclarationId} {body : Syntax.Block} {type : Core.Ty}
    (typing : TypedLetReturnTreeHasType types owner inputs.toTypeInputs body type) (store : Core.Store) :
    ∃ value cost, evaluateTypedLetReturnTreeWithCost? owner inputs.names inputs.environment body = some (value, cost) ∧
      Core.ValueHasType value type ∧ ∀ fuel,
        (inputs.runTypedLetReturnTree? types owner fuel body store = some (type, .done value store) ↔ cost ≤ fuel) ∧
        ((∃ checkpoint, inputs.runTypedLetReturnTree? types owner fuel body store = some (type, .outOfFuel checkpoint)) ↔ fuel < cost) := by
  obtain ⟨value, cost, evaluated, typed, boundaries⟩ := typedLetReturnTree_typed_cost_execution typing store
  exact ⟨value, cost, evaluateTypedLetReturnTreeWithCost?_complete evaluated, typed, boundaries⟩

end LocalInputs
end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.TypedLetReturnTreeFuelBoundProperties`
-/

/-! The source-only budget adds strict initializer work and takes the larger
recursive arm. A positive budget neither supplies acceptance nor runtime values;
the selected cost can be smaller than this sufficient-fuel upper bound. -/

set_option autoImplicit false

namespace Solcore.Frontend

def typedLetReturnTreeFuelBound (body : Syntax.Block) : Nat :=
  match body with
  | ⟨_, [⟨_, .returnStmt _⟩]⟩ => returnBodyFuelBound body
  | ⟨_, [⟨innerSpan, .block statements⟩]⟩ =>
      typedLetReturnTreeFuelBound ⟨innerSpan, statements⟩
  | ⟨blockSpan, ⟨_, .letDecl _ _ (some initializer)⟩ :: rest⟩ =>
      localExpressionFuelBound initializer + typedLetReturnTreeFuelBound ⟨blockSpan, rest⟩ + 2
  | ⟨blockSpan, ⟨_, .expression expression true⟩ :: rest⟩ =>
      localExpressionFuelBound expression + typedLetReturnTreeFuelBound ⟨blockSpan, rest⟩ + 2
  | ⟨_, [⟨_, .ifThen condition thenBody (some elseBody)⟩]⟩ =>
      localExpressionFuelBound condition +
        max (typedLetReturnTreeFuelBound thenBody) (typedLetReturnTreeFuelBound elseBody) + 2
  | _ => 0
termination_by sizeOf body

theorem TypedLetReturnTreeEvaluatesWithCost.cost_le_fuelBound
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : TypedLetReturnTreeEvaluatesWithCost owner table environment initialStore body value finalStore cost) :
    cost ≤ typedLetReturnTreeFuelBound body := by
  induction evaluation with
  | single child =>
      have bounded := child.cost_le_fuelBound
      cases child <;> simpa only [typedLetReturnTreeFuelBound] using bounded
  | block _ ih => simpa only [typedLetReturnTreeFuelBound] using ih
  | binding initializer _ ih | inferred initializer _ ih | discard initializer _ ih =>
      have initializerBound := initializer.cost_le_fuelBound
      simp only [typedLetReturnTreeFuelBound]
      omega
  | ifTrue condition _ ih | ifFalse condition _ ih =>
      have conditionBound := condition.cost_le_fuelBound
      simp only [typedLetReturnTreeFuelBound]
      omega

theorem elaborateTypedLetReturnTree?_run_done_of_fuelBound
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {environment : Resolved.Environment} {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTypedLetReturnTree? types owner inputs body = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids inputs.context)
    (environmentTyped : Core.EnvironmentHasTypes
      (Resolved.LocalScope.values environment) (Resolved.LocalScope.values inputs.context))
    (store : Core.Store) (fuel : Nat) (enough : typedLetReturnTreeFuelBound body ≤ fuel) :
    ∃ value, Core.ValueHasType value type ∧ Core.runStateful fuel
      (Core.State.initial core (Resolved.LocalScope.values environment) store) = .done value store := by
  obtain ⟨value, evaluated, valueTyped⟩ :=
    (elaborateTypedLetReturnTree?_sound accepted).evaluates sameIds environmentTyped store
  obtain ⟨cost, costed⟩ := evaluated.exists_cost
  exact ⟨value, valueTyped, (costed.checked_runStateful_done_iff accepted sameIds).mpr
    (Nat.le_trans costed.cost_le_fuelBound enough)⟩

theorem LocalInputs.runTypedLetReturnTree?_done_of_fuelBound
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalInputs}
    {body : Syntax.Block} {type : Core.Ty}
    (typing : TypedLetReturnTreeHasType types owner inputs.toTypeInputs body type)
    (store : Core.Store) (fuel : Nat) (enough : typedLetReturnTreeFuelBound body ≤ fuel) :
    ∃ value, Core.ValueHasType value type ∧
      inputs.runTypedLetReturnTree? types owner fuel body store = some (type, .done value store) := by
  obtain ⟨value, cost, costed, valueTyped, boundaries⟩ :=
    inputs.typedLetReturnTree_typed_cost_execution typing store
  exact ⟨value, valueTyped, (boundaries fuel).1.mpr (Nat.le_trans costed.cost_le_fuelBound enough)⟩

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.TypedLetReturnTreeResumptionProperties`
-/

/-! Genuine checkpoints retain selected branches, pending let frames and actual
captured values. Exact residual cost uses a closed final path, not an arbitrary
continuation endpoint or a reconstructed initial state. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem TypedLetReturnTreeEvaluatesWithCost.checked_residual_of_outOfFuel
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {environment : Resolved.Environment} {initialStore finalStore : Core.Store}
    {body : Syntax.Block} {value : Core.Value} {cost spent : Nat}
    (evaluation : TypedLetReturnTreeEvaluatesWithCost owner inputs.names environment
      initialStore body value finalStore cost)
    {core : Core.Expr} {type : Core.Ty} {checkpoint : Core.State}
    (accepted : elaborateTypedLetReturnTree? types owner inputs body = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids inputs.context)
    (exhausted : Core.runStateful spent (Core.State.initial core
      (Resolved.LocalScope.values environment) initialStore) = .outOfFuel checkpoint) :
    spent < cost ∧ Core.Steps (cost - spent) checkpoint (Core.State.final value finalStore) :=
  (evaluation.checked_toSteps accepted sameIds).residual_of_outOfFuel exhausted

theorem LocalInputs.runTypedLetReturnTree?_resume
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalInputs}
    {body : Syntax.Block} {spent : Nat} {store : Core.Store} {type : Core.Ty} {checkpoint : Core.State}
    (exhausted : inputs.runTypedLetReturnTree? types owner spent body store = some (type, .outOfFuel checkpoint))
    (additional : Nat) :
    inputs.runTypedLetReturnTree? types owner (spent + additional) body store =
      some (type, Core.runStateful additional checkpoint) := by
  obtain ⟨core, checked, execution⟩ := runTypedLetReturnTree?_eq_some_iff.mp exhausted
  exact runTypedLetReturnTree?_eq_some_iff.mpr ⟨core, checked, (Core.runStateful_resume execution additional).symm⟩

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.TypedLetReturnTreeStoreProperties`
-/

/-! Replay old-scope initializer values and selected recursive paths at any store.
Values and costs are fixed; completed and suspended observations retain their
own stores. This is not arbitrary-Core or pending-continuation store independence. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem TypedLetReturnTreeEvaluates.change_store
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value}
    (evaluation : TypedLetReturnTreeEvaluates owner table environment initialStore body value finalStore)
    (replacement : Core.Store) :
    TypedLetReturnTreeEvaluates owner table environment replacement body value replacement := by
  induction evaluation with
  | single child => exact .single (child.change_store replacement)
  | block _ ih => exact .block ih
  | binding initializer _ ih => exact .binding (initializer.change_store replacement) ih
  | inferred initializer _ ih => exact .inferred (initializer.change_store replacement) ih
  | discard expression _ ih => exact .discard (expression.change_store replacement) ih
  | ifTrue condition _ ih => exact .ifTrue (condition.change_store replacement) ih
  | ifFalse condition _ ih => exact .ifFalse (condition.change_store replacement) ih

theorem TypedLetReturnTreeEvaluatesWithCost.change_store
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : TypedLetReturnTreeEvaluatesWithCost owner table environment initialStore body value finalStore cost)
    (replacement : Core.Store) :
    TypedLetReturnTreeEvaluatesWithCost owner table environment replacement body value replacement cost := by
  induction evaluation with
  | single child => exact .single (child.change_store replacement)
  | block _ ih => exact .block ih
  | binding initializer _ ih => exact .binding (initializer.change_store replacement) ih
  | inferred initializer _ ih => exact .inferred (initializer.change_store replacement) ih
  | discard expression _ ih => exact .discard (expression.change_store replacement) ih
  | ifTrue condition _ ih => exact .ifTrue (condition.change_store replacement) ih
  | ifFalse condition _ ih => exact .ifFalse (condition.change_store replacement) ih

theorem typedLetReturnTreeEvaluates_store_iff
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore replacement : Core.Store} {body : Syntax.Block} {value : Core.Value} :
    TypedLetReturnTreeEvaluates owner table environment initialStore body value finalStore ↔
      finalStore = initialStore ∧
        TypedLetReturnTreeEvaluates owner table environment replacement body value replacement := by
  constructor
  · intro evaluation
    exact ⟨evaluation.store_eq, evaluation.change_store replacement⟩
  · rintro ⟨rfl, evaluation⟩
    exact evaluation.change_store _

theorem typedLetReturnTreeEvaluatesWithCost_store_iff
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore replacement : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat} :
    TypedLetReturnTreeEvaluatesWithCost owner table environment initialStore body value finalStore cost ↔
      finalStore = initialStore ∧
        TypedLetReturnTreeEvaluatesWithCost owner table environment replacement body value replacement cost := by
  constructor
  · intro evaluation
    exact ⟨evaluation.store_eq, evaluation.change_store replacement⟩
  · rintro ⟨rfl, evaluation⟩
    exact evaluation.change_store _

/-- Equal values at the same fuel, each with its own store; not equality of
complete results across stores. Whole checking remains part of each run. -/
theorem LocalInputs.runTypedLetReturnTree?_done_store_iff
    (inputs : LocalInputs) (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (fuel : Nat) (body : Syntax.Block) (leftStore rightStore : Core.Store)
    (type : Core.Ty) (value : Core.Value) :
    inputs.runTypedLetReturnTree? types owner fuel body leftStore = some (type, .done value leftStore) ↔
      inputs.runTypedLetReturnTree? types owner fuel body rightStore = some (type, .done value rightStore) := by
  rw [LocalInputs.runTypedLetReturnTree?_done_iff_typed_cost, LocalInputs.runTypedLetReturnTree?_done_iff_typed_cost]
  constructor
  · rintro ⟨typing, cost, evaluation, enough⟩
    exact ⟨typing, cost, evaluation.change_store rightStore, enough⟩
  · rintro ⟨typing, cost, evaluation, enough⟩
    exact ⟨typing, cost, evaluation.change_store leftStore, enough⟩

/-- Exhaustion presence agrees, but suspended states retain their distinct
stores and must be resumed separately without dropping pending let frames. -/
theorem LocalInputs.runTypedLetReturnTree?_outOfFuel_store_iff
    (inputs : LocalInputs) (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (fuel : Nat) (body : Syntax.Block) (leftStore rightStore : Core.Store) (type : Core.Ty) :
    (∃ checkpoint, inputs.runTypedLetReturnTree? types owner fuel body leftStore = some (type, .outOfFuel checkpoint)) ↔
      ∃ checkpoint, inputs.runTypedLetReturnTree? types owner fuel body rightStore = some (type, .outOfFuel checkpoint) := by
  rw [LocalInputs.runTypedLetReturnTree?_outOfFuel_iff_typed_cost, LocalInputs.runTypedLetReturnTree?_outOfFuel_iff_typed_cost]
  constructor
  · rintro ⟨typing, value, cost, evaluation, short⟩
    exact ⟨typing, value, cost, evaluation.change_store rightStore, short⟩
  · rintro ⟨typing, value, cost, evaluation, short⟩
    exact ⟨typing, value, cost, evaluation.change_store leftStore, short⟩

end Solcore.Frontend
