import Solcore.Frontend.StructuralType
import Solcore.Frontend.LocalTypeInputs
import Solcore.Frontend.WordMatch

/-! Shared mixed bodies parameterize only their child expression operations.
Checker, typing and exact elaboration remain independent interfaces. -/

set_option autoImplicit false

namespace Solcore.Frontend

def elaborateComputationReturnTree?
    (checkChild : LocalNameTable → Resolved.Context → Syntax.Expr → Option (Core.Expr × Core.Ty))
    (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (inputs : LocalTypeInputs) (body : Syntax.Block) : Option (Core.Expr × Core.Ty) :=
  match body with
  | ⟨_, [⟨_, .returnStmt none⟩]⟩ => some (.unit, .unit)
  | ⟨_, [⟨_, .returnStmt (some expression)⟩]⟩ =>
      checkChild inputs.names inputs.context expression
  | ⟨_, [⟨innerSpan, .block statements⟩]⟩ =>
      elaborateComputationReturnTree? checkChild types owner inputs ⟨innerSpan, statements⟩
  | ⟨blockSpan, ⟨_, .letDecl name (some annotation) (some initializer)⟩ :: rest⟩ =>
      if name.value ∉ inputs.names.map Prod.fst then do
        let declaredType ← interpretStructuralType? types annotation
        let (initializerCore, initializerType) ← checkChild inputs.names inputs.context initializer
        if initializerType = declaredType then do
          let (tailCore, returnType) ← elaborateComputationReturnTree? checkChild types owner
            (inputs.bindFresh owner name.value declaredType) ⟨blockSpan, rest⟩
          return (.letE initializerCore tailCore, returnType)
        else none
      else none
  | ⟨blockSpan, ⟨_, .letDecl name none (some initializer)⟩ :: rest⟩ =>
      if name.value ∉ inputs.names.map Prod.fst then do
        let (initializerCore, initializerType) ← checkChild inputs.names inputs.context initializer
        let (tailCore, returnType) ← elaborateComputationReturnTree? checkChild types owner
          (inputs.bindFresh owner name.value initializerType) ⟨blockSpan, rest⟩
        return (.letE initializerCore tailCore, returnType)
      else none
  | ⟨blockSpan, ⟨_, .expression expression true⟩ :: rest⟩ => do
      let (expressionCore, _) ← checkChild inputs.names inputs.context expression
      let (tailCore, returnType) ← elaborateComputationReturnTree? checkChild types owner inputs ⟨blockSpan, rest⟩
      return (.letE expressionCore (tailCore.weakenAt 0), returnType)
  | ⟨_, [⟨_, .ifThen condition thenBody (some elseBody)⟩]⟩ => do
      let (conditionCore, conditionType) ← checkChild inputs.names inputs.context condition
      if conditionType = .bool then do
        let (thenCore, thenType) ← elaborateComputationReturnTree? checkChild types owner inputs thenBody
        let (elseCore, elseType) ← elaborateComputationReturnTree? checkChild types owner inputs elseBody
        if thenType = elseType then return (.ifE conditionCore thenCore elseCore, thenType)
        else none
      else none
  | ⟨_, [⟨_, .matchWith ⟨_, ⟨scrutinee, []⟩⟩ ⟨_, ⟨cases, some defaultBody⟩⟩⟩]⟩ => do
      let (scrutineeCore, scrutineeType) ← checkChild inputs.names inputs.context scrutinee
      if scrutineeType = .word then do
        let (defaultCore, returnType) ← elaborateComputationReturnTree? checkChild types owner inputs defaultBody
        let entries ← cases.attach.mapM fun arm => do
          let tag ← match arm.val.value.pattern.value with
            | .literal literal => (interpretWordLiteral? literal).map some
            | .wildcard _ => some none
            | _ => none
          let (branchCore, branchType) ← elaborateComputationReturnTree? checkChild types owner inputs arm.val.value.body
          if branchType = returnType then return (arm.val, tag, branchCore)
          else none
        return (.letE scrutineeCore (entries.foldr
          (fun entry tail => match entry.2.1 with
            | none => entry.2.2.weakenAt 0
            | some word => .ifE (.binary .wordEq (.var 0) (.word word)) (entry.2.2.weakenAt 0) tail)
          (defaultCore.weakenAt 0)), returnType)
      else none
  | _ => none
termination_by sizeOf body
decreasing_by
  all_goals simp_wf
  all_goals try omega
  have member := List.sizeOf_lt_of_mem arm.property
  have child : sizeOf arm.val.value.body < sizeOf arm.val := by
    rcases arm.val with ⟨span, ⟨pattern, body⟩⟩
    simp
    omega
  omega

inductive ComputationReturnTreeHasType
    (ChildHasType : LocalNameTable → Resolved.Context → Syntax.Expr → Core.Ty → Prop)
    (types : TypeNameTable) (owner : Resolved.DeclarationId) :
    LocalTypeInputs → Syntax.Block → Core.Ty → Prop where
  | bare {inputs : LocalTypeInputs} {blockSpan returnSpan : Syntax.SourceSpan} :
      ComputationReturnTreeHasType ChildHasType types owner inputs
        ⟨blockSpan, [⟨returnSpan, .returnStmt none⟩]⟩ .unit
  | expression {inputs : LocalTypeInputs} {blockSpan returnSpan : Syntax.SourceSpan}
      {source : Syntax.Expr} {type : Core.Ty}
      (child : ChildHasType inputs.names inputs.context source type) :
      ComputationReturnTreeHasType ChildHasType types owner inputs
        ⟨blockSpan, [⟨returnSpan, .returnStmt (some source)⟩]⟩ type
  | block {inputs : LocalTypeInputs} {outerSpan innerSpan : Syntax.SourceSpan}
      {statements : List Syntax.Statement} {type : Core.Ty}
      (child : ComputationReturnTreeHasType ChildHasType types owner inputs ⟨innerSpan, statements⟩ type) :
      ComputationReturnTreeHasType ChildHasType types owner inputs
        ⟨outerSpan, [⟨innerSpan, .block statements⟩]⟩ type
  | binding {inputs : LocalTypeInputs} {blockSpan letSpan : Syntax.SourceSpan}
      {name : Syntax.Identifier} {annotation : Syntax.TypeExpr} {initializer : Syntax.Expr}
      {rest : List Syntax.Statement} {declaredType returnType : Core.Ty}
      (meaning : StructuralTypeDenotes types annotation declaredType)
      (unused : name.value ∉ inputs.names.map Prod.fst)
      (initializerTyping : ChildHasType inputs.names inputs.context initializer declaredType)
      (tailTyping : ComputationReturnTreeHasType ChildHasType types owner
        (inputs.bindFresh owner name.value declaredType) ⟨blockSpan, rest⟩ returnType) :
      ComputationReturnTreeHasType ChildHasType types owner inputs
        ⟨blockSpan, ⟨letSpan, .letDecl name (some annotation) (some initializer)⟩ :: rest⟩ returnType
  | inferred {inputs : LocalTypeInputs} {blockSpan letSpan : Syntax.SourceSpan}
      {name : Syntax.Identifier} {initializer : Syntax.Expr} {rest : List Syntax.Statement}
      {inferredType returnType : Core.Ty}
      (unused : name.value ∉ inputs.names.map Prod.fst)
      (initializerTyping : ChildHasType inputs.names inputs.context initializer inferredType)
      (tailTyping : ComputationReturnTreeHasType ChildHasType types owner
        (inputs.bindFresh owner name.value inferredType) ⟨blockSpan, rest⟩ returnType) :
      ComputationReturnTreeHasType ChildHasType types owner inputs
        ⟨blockSpan, ⟨letSpan, .letDecl name none (some initializer)⟩ :: rest⟩ returnType
  | discard {inputs : LocalTypeInputs} {blockSpan statementSpan : Syntax.SourceSpan}
      {expression : Syntax.Expr} {rest : List Syntax.Statement} {discardedType returnType : Core.Ty}
      (expressionTyping : ChildHasType inputs.names inputs.context expression discardedType)
      (tailTyping : ComputationReturnTreeHasType ChildHasType types owner inputs ⟨blockSpan, rest⟩ returnType) :
      ComputationReturnTreeHasType ChildHasType types owner inputs
        ⟨blockSpan, ⟨statementSpan, .expression expression true⟩ :: rest⟩ returnType
  | conditional {inputs : LocalTypeInputs} {blockSpan ifSpan : Syntax.SourceSpan}
      {condition : Syntax.Expr} {thenBody elseBody : Syntax.Block} {type : Core.Ty}
      (conditionTyping : ChildHasType inputs.names inputs.context condition .bool)
      (thenTyping : ComputationReturnTreeHasType ChildHasType types owner inputs thenBody type)
      (elseTyping : ComputationReturnTreeHasType ChildHasType types owner inputs elseBody type) :
      ComputationReturnTreeHasType ChildHasType types owner inputs
        ⟨blockSpan, [⟨ifSpan, .ifThen condition thenBody (some elseBody)⟩]⟩ type
  | wordMatch {inputs : LocalTypeInputs} {blockSpan matchSpan scrutineeSpan armsSpan : Syntax.SourceSpan}
      {scrutinee : Syntax.Expr} {cases : List Syntax.MatchCase} {defaultBody : Syntax.Block} {type : Core.Ty}
      (scrutineeTyping : ChildHasType inputs.names inputs.context scrutinee .word)
      (patterns : ∀ arm ∈ cases, ∃ tag : Option Core.Word, match tag with
        | none => ∃ marker, arm.value.pattern.value = .wildcard marker
        | some word => WordMatchPatternDenotes arm.value.pattern word)
      (branches : ∀ arm ∈ cases, ComputationReturnTreeHasType ChildHasType types owner inputs arm.value.body type)
      (defaultTyping : ComputationReturnTreeHasType ChildHasType types owner inputs defaultBody type) :
      ComputationReturnTreeHasType ChildHasType types owner inputs
        ⟨blockSpan, [⟨matchSpan, .matchWith ⟨scrutineeSpan, ⟨scrutinee, []⟩⟩ ⟨armsSpan, ⟨cases, some defaultBody⟩⟩⟩]⟩ type

inductive ComputationReturnTreeElaborates
    (ChildElab : LocalNameTable → Resolved.Context → Syntax.Expr → Core.Expr → Core.Ty → Prop)
    (types : TypeNameTable) (owner : Resolved.DeclarationId) :
    LocalTypeInputs → Syntax.Block → Core.Expr → Core.Ty → Prop where
  | bare {inputs : LocalTypeInputs} {blockSpan returnSpan : Syntax.SourceSpan} :
      ComputationReturnTreeElaborates ChildElab types owner inputs
        ⟨blockSpan, [⟨returnSpan, .returnStmt none⟩]⟩ .unit .unit
  | expression {inputs : LocalTypeInputs} {blockSpan returnSpan : Syntax.SourceSpan}
      {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
      (child : ChildElab inputs.names inputs.context source core type) :
      ComputationReturnTreeElaborates ChildElab types owner inputs
        ⟨blockSpan, [⟨returnSpan, .returnStmt (some source)⟩]⟩ core type
  | block {inputs : LocalTypeInputs} {outerSpan innerSpan : Syntax.SourceSpan}
      {statements : List Syntax.Statement} {core : Core.Expr} {type : Core.Ty}
      (child : ComputationReturnTreeElaborates ChildElab types owner inputs ⟨innerSpan, statements⟩ core type) :
      ComputationReturnTreeElaborates ChildElab types owner inputs
        ⟨outerSpan, [⟨innerSpan, .block statements⟩]⟩ core type
  | binding {inputs : LocalTypeInputs} {blockSpan letSpan : Syntax.SourceSpan}
      {name : Syntax.Identifier} {annotation : Syntax.TypeExpr} {initializer : Syntax.Expr}
      {rest : List Syntax.Statement} {declaredType returnType : Core.Ty} {initializerCore tailCore : Core.Expr}
      (meaning : StructuralTypeDenotes types annotation declaredType)
      (unused : name.value ∉ inputs.names.map Prod.fst)
      (initializerElaboration : ChildElab inputs.names inputs.context initializer initializerCore declaredType)
      (tailElaboration : ComputationReturnTreeElaborates ChildElab types owner
        (inputs.bindFresh owner name.value declaredType) ⟨blockSpan, rest⟩ tailCore returnType) :
      ComputationReturnTreeElaborates ChildElab types owner inputs
        ⟨blockSpan, ⟨letSpan, .letDecl name (some annotation) (some initializer)⟩ :: rest⟩
        (.letE initializerCore tailCore) returnType
  | inferred {inputs : LocalTypeInputs} {blockSpan letSpan : Syntax.SourceSpan}
      {name : Syntax.Identifier} {initializer : Syntax.Expr} {rest : List Syntax.Statement}
      {inferredType returnType : Core.Ty} {initializerCore tailCore : Core.Expr}
      (unused : name.value ∉ inputs.names.map Prod.fst)
      (initializerElaboration : ChildElab inputs.names inputs.context initializer initializerCore inferredType)
      (tailElaboration : ComputationReturnTreeElaborates ChildElab types owner
        (inputs.bindFresh owner name.value inferredType) ⟨blockSpan, rest⟩ tailCore returnType) :
      ComputationReturnTreeElaborates ChildElab types owner inputs
        ⟨blockSpan, ⟨letSpan, .letDecl name none (some initializer)⟩ :: rest⟩
        (.letE initializerCore tailCore) returnType
  | discard {inputs : LocalTypeInputs} {blockSpan statementSpan : Syntax.SourceSpan}
      {expression : Syntax.Expr} {rest : List Syntax.Statement} {discardedType returnType : Core.Ty}
      {expressionCore tailCore : Core.Expr}
      (expressionElaboration : ChildElab inputs.names inputs.context expression expressionCore discardedType)
      (tailElaboration : ComputationReturnTreeElaborates ChildElab types owner inputs ⟨blockSpan, rest⟩ tailCore returnType) :
      ComputationReturnTreeElaborates ChildElab types owner inputs
        ⟨blockSpan, ⟨statementSpan, .expression expression true⟩ :: rest⟩
        (.letE expressionCore (tailCore.weakenAt 0)) returnType
  | conditional {inputs : LocalTypeInputs} {blockSpan ifSpan : Syntax.SourceSpan}
      {condition : Syntax.Expr} {thenBody elseBody : Syntax.Block}
      {conditionCore thenCore elseCore : Core.Expr} {type : Core.Ty}
      (conditionElaboration : ChildElab inputs.names inputs.context condition conditionCore .bool)
      (thenElaboration : ComputationReturnTreeElaborates ChildElab types owner inputs thenBody thenCore type)
      (elseElaboration : ComputationReturnTreeElaborates ChildElab types owner inputs elseBody elseCore type) :
      ComputationReturnTreeElaborates ChildElab types owner inputs
        ⟨blockSpan, [⟨ifSpan, .ifThen condition thenBody (some elseBody)⟩]⟩
        (.ifE conditionCore thenCore elseCore) type
  | wordMatch {inputs : LocalTypeInputs} {blockSpan matchSpan scrutineeSpan armsSpan : Syntax.SourceSpan}
      {scrutinee : Syntax.Expr} {cases : List Syntax.MatchCase} {defaultBody : Syntax.Block}
      {scrutineeCore defaultCore : Core.Expr} {type : Core.Ty}
      {entries : List (Syntax.MatchCase × (Option Core.Word × Core.Expr))}
      (scrutineeElaboration : ChildElab inputs.names inputs.context scrutinee scrutineeCore .word)
      (ordered : entries.map Prod.fst = cases)
      (patterns : ∀ entry ∈ entries, match entry.2.1 with
        | none => ∃ marker, entry.1.value.pattern.value = .wildcard marker
        | some word => WordMatchPatternDenotes entry.1.value.pattern word)
      (branches : ∀ entry ∈ entries,
        ComputationReturnTreeElaborates ChildElab types owner inputs entry.1.value.body entry.2.2 type)
      (defaultElaboration : ComputationReturnTreeElaborates ChildElab types owner inputs defaultBody defaultCore type) :
      ComputationReturnTreeElaborates ChildElab types owner inputs
        ⟨blockSpan, [⟨matchSpan, .matchWith ⟨scrutineeSpan, ⟨scrutinee, []⟩⟩ ⟨armsSpan, ⟨cases, some defaultBody⟩⟩⟩]⟩
        (.letE scrutineeCore (entries.foldr
          (fun entry tail => match entry.2.1 with
            | none => entry.2.2.weakenAt 0
            | some word => .ifE (.binary .wordEq (.var 0) (.word word)) (entry.2.2.weakenAt 0) tail)
          (defaultCore.weakenAt 0))) type

end Solcore.Frontend
