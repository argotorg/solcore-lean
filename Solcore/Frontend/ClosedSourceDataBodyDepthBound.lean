import Solcore.Frontend.ClosedSourceDataDepthBound

/- Source-search upper depths for gated original bodies and all written match
branches. This is independent of match comparison counts and Core step costs.
Unhandled root forms receive zero; the separate syntax gate remains essential. -/
set_option autoImplicit false
namespace Solcore.Frontend

mutual

/-- Counts every body-search level, retaining the original reconstructed tails
and considering both conditional branches and every written match body. -/
def closedSourceDataBodyDepthBound (body : Syntax.Block) : Nat :=
  match body with
  | ⟨_, [⟨_, .returnStmt none⟩]⟩ => 1
  | ⟨_, [⟨_, .returnStmt (some child)⟩]⟩ => closedSourceDataDepthBound child + 1
  | ⟨_, [⟨innerSpan, .block statements⟩]⟩ =>
      closedSourceDataBodyDepthBound ⟨innerSpan, statements⟩ + 1
  | ⟨blockSpan, ⟨_, .letDecl _ _ (some initializer)⟩ :: rest⟩ =>
      max (closedSourceDataDepthBound initializer)
        (closedSourceDataBodyDepthBound ⟨blockSpan, rest⟩) + 1
  | ⟨blockSpan, ⟨_, .expression child true⟩ :: rest⟩ =>
      max (closedSourceDataDepthBound child)
        (closedSourceDataBodyDepthBound ⟨blockSpan, rest⟩) + 1
  | ⟨_, [⟨_, .ifThen condition thenBody (some elseBody)⟩]⟩ =>
      max (closedSourceDataDepthBound condition)
        (max (closedSourceDataBodyDepthBound thenBody) (closedSourceDataBodyDepthBound elseBody)) + 1
  | ⟨_, [⟨_, .matchWith ⟨_, ⟨scrutinee, []⟩⟩ ⟨_, ⟨cases, defaultBody⟩⟩⟩]⟩ =>
      max (closedSourceDataDepthBound scrutinee)
        (closedSourceDataMatchDepthBound cases defaultBody) + 1
  | _ => 0
termination_by sizeOf body

/-- Maximum body depth of every written arm and optional fallback. Traversing
the arm list itself consumes no recursive evaluator depth. -/
def closedSourceDataMatchDepthBound (cases : List Syntax.MatchCase)
    (defaultBody : Option Syntax.Block) : Nat :=
  match cases with
  | [] => match defaultBody with
      | none => 0
      | some body => closedSourceDataBodyDepthBound body
  | first :: rest =>
      have bodySmaller : sizeOf first.value.body < sizeOf first := by
        rcases first with ⟨_,⟨_,_⟩⟩
        simp only [Syntax.Located.mk.sizeOf_spec, Syntax.MatchCaseValue.mk.sizeOf_spec]
        omega
      max (closedSourceDataBodyDepthBound first.value.body)
        (closedSourceDataMatchDepthBound rest defaultBody)
termination_by sizeOf cases + sizeOf defaultBody

end

end Solcore.Frontend
