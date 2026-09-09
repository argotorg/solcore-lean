import Solcore.Frontend.ComputationReturnTreeProperties

/-! Source-only protection is independent of branch execution or child checking.
Bare if scopes differ from explicit blocks and match arms in the pinned resolver. -/

set_option autoImplicit false
namespace Tests.FrontendComputationScopeBoundary
open Solcore Solcore.Frontend

theorem explicit_blocks_protect_every_outer_name
    (names : List String) (outerSpan innerSpan : Syntax.SourceSpan) (statements : List Syntax.Statement) :
    ComputationNamesProtected names ⟨outerSpan, [⟨innerSpan, .block statements⟩]⟩ ∧
    computationBlockPreservesNames names ⟨outerSpan, [⟨innerSpan, .block statements⟩]⟩ = true := by
  have protection : ComputationNamesProtected names ⟨outerSpan, [⟨innerSpan, .block statements⟩]⟩ := by
    intro name exposed
    cases exposed with | tail impossible => cases impossible
  exact ⟨protection, computationBlockPreservesNames_iff.mpr protection⟩

theorem match_arms_protect_every_outer_name
    (names : List String) (outerSpan matchSpan : Syntax.SourceSpan)
    (scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr) (arms : Syntax.MatchArms) :
    ComputationNamesProtected names ⟨outerSpan, [⟨matchSpan, .matchWith scrutinees arms⟩]⟩ ∧
    computationBlockPreservesNames names ⟨outerSpan, [⟨matchSpan, .matchWith scrutinees arms⟩]⟩ = true := by
  have protection : ComputationNamesProtected names ⟨outerSpan, [⟨matchSpan, .matchWith scrutinees arms⟩]⟩ := by
    intro name exposed
    cases exposed with | tail impossible => cases impossible
  exact ⟨protection, computationBlockPreservesNames_iff.mpr protection⟩

theorem exposed_then_shadow_rejects_independently_of_child_checking
    (checkChild : LocalNameTable → Resolved.Context → Syntax.Expr → Option (Core.Expr × Core.Ty))
    (ChildElab : LocalNameTable → Resolved.Context → Syntax.Expr → Core.Expr → Core.Ty → Prop)
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs)
    (blockSpan ifSpan : Syntax.SourceSpan) (condition : Syntax.Expr) (yes no : Syntax.Block)
    (name : String) (present : name ∈ inputs.names.map Prod.fst)
    (exposed : ExposesComputationLetName name yes) :
    elaborateComputationReturnTree? checkChild types owner inputs
      ⟨blockSpan, [⟨ifSpan, .ifThen condition yes (some no)⟩]⟩ = none ∧
    ¬ ∃ core type, ComputationReturnTreeElaborates ChildElab types owner inputs
      ⟨blockSpan, [⟨ifSpan, .ifThen condition yes (some no)⟩]⟩ core type := by
  have rejected := computationBlockPreservesNames_eq_false_iff.mpr ⟨name, present, exposed⟩
  constructor
  · rw [elaborateComputationReturnTree?]
    cases checkChild inputs.names inputs.context condition with
    | none => rfl
    | some pair => simp only [bind, Option.bind_some, rejected, Bool.false_eq_true, and_false, ↓reduceIte]
  · rintro ⟨core, type, elaboration⟩
    cases elaboration with
    | conditional child protection thenElab elseElab => exact protection name exposed present

theorem a_nested_unscoped_else_shadow_remains_exposed
    (names : List String) (name : Syntax.Identifier) (present : name.value ∈ names)
    (outerSpan ifSpan letSpan bodySpan : Syntax.SourceSpan) (condition : Syntax.Expr)
    (yes : Syntax.Block) (annotation : Option Syntax.TypeExpr) (initializer : Option Syntax.Expr)
    (rest : List Syntax.Statement) :
    ExposesComputationLetName name.value
      ⟨outerSpan, [⟨ifSpan, .ifThen condition yes
        (some ⟨bodySpan, ⟨letSpan, .letDecl name annotation initializer⟩ :: rest⟩)⟩]⟩ ∧
    computationBlockPreservesNames names
      ⟨outerSpan, [⟨ifSpan, .ifThen condition yes
        (some ⟨bodySpan, ⟨letSpan, .letDecl name annotation initializer⟩ :: rest⟩)⟩]⟩ = false := by
  have exposed : ExposesComputationLetName name.value
      ⟨outerSpan, [⟨ifSpan, .ifThen condition yes
        (some ⟨bodySpan, ⟨letSpan, .letDecl name annotation initializer⟩ :: rest⟩)⟩]⟩ :=
    .elseBranch (.binding rfl)
  exact ⟨exposed, computationBlockPreservesNames_eq_false_iff.mpr ⟨name.value, present, exposed⟩⟩

theorem statement_tails_do_not_hide_exposed_shadow
    (names : List String) (name : String) (present : name ∈ names)
    (span : Syntax.SourceSpan) (statement : Syntax.Statement) (rest : List Syntax.Statement)
    (exposed : ExposesComputationLetName name ⟨span, rest⟩) :
    computationBlockPreservesNames names ⟨span, statement :: rest⟩ = false :=
  computationBlockPreservesNames_eq_false_iff.mpr ⟨name, present, .tail exposed⟩

end Tests.FrontendComputationScopeBoundary
