import Solcore.Syntax.Parser.GenericParametersTotalityProperties
import Solcore.Syntax.Parser.ImplBodyTotalityProperties
import Solcore.Syntax.Parser.ImplHeadTotalityProperties
import Solcore.Syntax.Parser.TypeFuelTotalityProperties
import Solcore.Syntax.Parser.WhereClauseTotalityProperties

/-! Valid-input totality for complete canonical implementation declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace ImplInternals

/--
Compose a total parser with a defensive refinement known to succeed for every
value actually produced by that parser.
-/
private theorem bind_refinement_invariantFreeOnValid
    {alpha beta gamma : Type} {first : Parser alpha}
    {refine : alpha → Parser beta} {next : beta → Parser gamma}
    (firstValid : first.ValidFor (fun _ _ => True))
    (firstFree : Parser.InvariantFreeOnValid first)
    (refineOk : ∀ {input after : State} {value : alpha},
      first input = .ok value after →
        ∃ refined, refine value after = .ok refined after)
    (nextFree : ∀ refined, Parser.InvariantFreeOnValid (next refined)) :
    Parser.InvariantFreeOnValid (do
      let value ← first
      let refined ← refine value
      next refined) := by
  intro input inputValid
  rcases firstFree input inputValid with
    ⟨value, after, firstResult⟩ |
    ⟨failure, rejected, firstResult⟩
  · have firstReply := firstValid input inputValid
    rw [firstResult] at firstReply
    rcases refineOk firstResult with ⟨refined, refineResult⟩
    rcases nextFree refined after firstReply.2.1 with
      ⟨result, final, nextResult⟩ |
      ⟨failure, final, nextResult⟩
    · exact Or.inl ⟨result, final, by
        simp only [bind, firstResult, refineResult, nextResult]⟩
    · exact Or.inr ⟨failure, final, by
        simp only [bind, firstResult, refineResult, nextResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [bind, firstResult]⟩

/-- The declaration suffix is total after either optional-default outcome. -/
theorem implDeclAfterDefault_invariantFreeOnValid
    (defaultMarker : Option SourceSpan) :
    Parser.InvariantFreeOnValid (implDeclAfterDefault defaultMarker) := by
  unfold implDeclAfterDefault
  apply Parser.bind_invariantFreeOnValid
    (contextual_validFor .impl .topItem)
    (contextual_ordinary .impl .topItem).invariantFreeOnValid
  intro marker
  apply Parser.bind_invariantFreeOnValid optionalGenericParameters_validFor
    optionalGenericParameters_invariantFreeOnValid
  intro genericParameters
  apply Parser.bind_invariantFreeOnValid
    (identifier_validFor .topItem)
    (identifier_ordinary .topItem).invariantFreeOnValid
  intro traitName
  apply bind_refinement_invariantFreeOnValid
    ((delimited_validFor TypeExpr.ValidFor .less .greater false typeExpr
      .typeExpr .topLevel typeExpr_validFor
      typeExpr_preservesTokensOnSuccess).mono (fun _ _ _ => trivial))
    (fun input inputValid =>
      delimited_ordinary .less .greater false typeExpr .typeExpr .topLevel
        typeExpr_elementTotalityContract input inputValid)
    requireImplArguments_ok_of_delimited_false_ok
  intro headArguments
  apply Parser.bind_invariantFreeOnValid whereClause_validFor
    whereClause_invariantFreeOnValid
  intro parsedWhereClause
  apply Parser.bind_invariantFreeOnValid
    (implBody_validFor CoreStatement.ValidFor
      (block_canonical_validFor .allow)
      (block_canonical_preservesTokenWindow .allow))
    implBody_invariantFreeOnValid
  intro body
  let startSpan := defaultMarker.getD marker.span
  exact Parser.pure_invariantFreeOnValid ({
    span := SourceSpan.cover startSpan body.span
    value := {
      defaultMarker
      genericParameters
      traitName
      headArguments
      whereClause := parsedWhereClause
      bodySpan := body.span
      methods := body.methods
    }
  } : ImplDecl)

theorem implDeclAfterDefault_ordinary
    (defaultMarker : Option SourceSpan)
    (input : State) (inputValid : input.ValidFor) :
    (∃ declaration next,
      implDeclAfterDefault defaultMarker input = .ok declaration next) ∨
      (∃ failure next,
        implDeclAfterDefault defaultMarker input = .reject failure next) :=
  implDeclAfterDefault_invariantFreeOnValid defaultMarker input inputValid

theorem implDeclAfterDefault_ne_invariant
    (defaultMarker : Option SourceSpan)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    implDeclAfterDefault defaultMarker input ≠ .invariant error :=
  (implDeclAfterDefault_invariantFreeOnValid defaultMarker).ne_invariant
    input inputValid error

end ImplInternals

open ImplInternals

/-- A complete optional-default implementation is total on valid input. -/
theorem implDecl_invariantFreeOnValid :
    Parser.InvariantFreeOnValid implDecl := by
  unfold implDecl
  apply Parser.bind_invariantFreeOnValid implDefaultMarker_validFor
    implDefaultMarker_invariantFreeOnValid
  intro defaultMarker
  exact implDeclAfterDefault_invariantFreeOnValid defaultMarker

theorem implDecl_ordinary (input : State) (inputValid : input.ValidFor) :
    (∃ declaration next, implDecl input = .ok declaration next) ∨
      (∃ failure next, implDecl input = .reject failure next) :=
  implDecl_invariantFreeOnValid input inputValid

theorem implDecl_ne_invariant
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    implDecl input ≠ .invariant error :=
  implDecl_invariantFreeOnValid.ne_invariant input inputValid error

end Solcore.Syntax.Parser
