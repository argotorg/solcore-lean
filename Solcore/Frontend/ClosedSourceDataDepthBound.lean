import Solcore.Syntax.Term

/- A source-only upper depth for the recursive data-expression gate.
It is not Core transition cost or a search bound for source closures/calls.
Unsupported shapes receive zero; the syntax gate is a separate premise. -/
set_option autoImplicit false
namespace Solcore.Frontend

/-- Pays one recursive source-search level per written data node, including
groups and each right-associated tuple tail. Both potential branches are counted
through a maximum, independently of runtime inputs, lexical rows or stores. -/
def closedSourceDataDepthBound (source : Syntax.Expr) : Nat :=
  match source with
  | ⟨_,.identifier _⟩ => 1
  | ⟨_,.literal _⟩ => 1
  | ⟨_,.group inner⟩ => closedSourceDataDepthBound inner + 1
  | ⟨_,.tuple ⟨_,[]⟩⟩ => 1
  | ⟨_,.tuple ⟨_,[left,right]⟩⟩ =>
      max (closedSourceDataDepthBound left) (closedSourceDataDepthBound right) + 1
  | ⟨span,.tuple ⟨tupleSpan,first::second::third::rest⟩⟩ =>
      max (closedSourceDataDepthBound first)
        (closedSourceDataDepthBound ⟨span,.tuple ⟨tupleSpan,second::third::rest⟩⟩) + 1
  | ⟨_,.unary _ child⟩ => closedSourceDataDepthBound child + 1
  | ⟨_,.binary left _ right⟩ =>
      max (closedSourceDataDepthBound left) (closedSourceDataDepthBound right) + 1
  | ⟨_,.conditional condition _ thenBranch _ elseBranch⟩ =>
      max (closedSourceDataDepthBound condition)
        (max (closedSourceDataDepthBound thenBranch) (closedSourceDataDepthBound elseBranch)) + 1
  | _ => 0
termination_by sizeOf source

end Solcore.Frontend
