import Solcore.Surface.Multi.UnguardedDerivation

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar Solcore.Workspace

mutual

/-- Proof-relevant recognition for one checked EBNF expression.  Unlike the
semantic carrier, it retains the exact interval of every recursive child. -/
inductive EbnfRecognizes
    (file : WorkspaceFile) (tokens : List Token) :
    EbnfExpr → Boundary tokens → Boundary tokens → Prop where
  | terminal
      (terminal : TerminalSymbol)
      (matched : MatchedTerminal file tokens terminal) :
      EbnfRecognizes file tokens (.atom (.terminal terminal))
        matched.cursor.beforeBoundary matched.cursor.afterBoundary
  | nonterminal
      (rule : GrammarRuleId) (start finish : Boundary tokens)
      (body : EbnfRecognizes file tokens (m2cV1.rhs rule) start finish) :
      EbnfRecognizes file tokens (.atom (.nonterminal rule)) start finish
  | sequence
      (children : List EbnfExpr) (start finish : Boundary tokens)
      (body : EbnfRecognizesList file tokens children start finish) :
      EbnfRecognizes file tokens (.sequence children) start finish
  | group
      (child : EbnfExpr) (start finish : Boundary tokens)
      (body : EbnfRecognizes file tokens child start finish) :
      EbnfRecognizes file tokens (.group child) start finish
  | choice
      (branches : List EbnfExpr) (branch : Fin branches.length)
      (start finish : Boundary tokens)
      (body : EbnfRecognizes file tokens (branches.get branch) start finish) :
      EbnfRecognizes file tokens (.choice branches) start finish
  | optionalNone
      (child : EbnfExpr) (cursor : Boundary tokens) :
      EbnfRecognizes file tokens (.optional child) cursor cursor
  | optionalSome
      (child : EbnfExpr) (start finish : Boundary tokens)
      (body : EbnfRecognizes file tokens child start finish) :
      EbnfRecognizes file tokens (.optional child) start finish
  | starNil
      (child : EbnfExpr) (cursor : Boundary tokens) :
      EbnfRecognizes file tokens (.star child) cursor cursor
  | starCons
      (child : EbnfExpr) (start middle finish : Boundary tokens)
      (head : EbnfRecognizes file tokens child start middle)
      (tail : EbnfRecognizes file tokens (.star child) middle finish) :
      EbnfRecognizes file tokens (.star child) start finish
  | plusOne
      (child : EbnfExpr) (start finish : Boundary tokens)
      (head : EbnfRecognizes file tokens child start finish) :
      EbnfRecognizes file tokens (.plus child) start finish
  | plusCons
      (child : EbnfExpr) (start middle finish : Boundary tokens)
      (head : EbnfRecognizes file tokens child start middle)
      (tail : EbnfRecognizes file tokens (.plus child) middle finish) :
      EbnfRecognizes file tokens (.plus child) start finish
  | list0Nil
      (element : EbnfExpr) (cursor : Boundary tokens) :
      EbnfRecognizes file tokens (.list0 element) cursor cursor
  | list0Cons
      (element : EbnfExpr) (start middle finish : Boundary tokens)
      (head : EbnfRecognizes file tokens element start middle)
      (tail : EbnfCommaTailRecognizes file tokens element middle finish) :
      EbnfRecognizes file tokens (.list0 element) start finish
  | list1
      (element : EbnfExpr) (start middle finish : Boundary tokens)
      (head : EbnfRecognizes file tokens element start middle)
      (tail : EbnfCommaTailRecognizes file tokens element middle finish) :
      EbnfRecognizes file tokens (.list1 element) start finish

/-- Recognition of a displayed EBNF sequence. -/
inductive EbnfRecognizesList
    (file : WorkspaceFile) (tokens : List Token) :
    List EbnfExpr → Boundary tokens → Boundary tokens → Prop where
  | nil (cursor : Boundary tokens) :
      EbnfRecognizesList file tokens [] cursor cursor
  | cons
      (expression : EbnfExpr) (rest : List EbnfExpr)
      (start middle finish : Boundary tokens)
      (head : EbnfRecognizes file tokens expression start middle)
      (tail : EbnfRecognizesList file tokens rest middle finish) :
      EbnfRecognizesList file tokens (expression :: rest) start finish

/-- Recognition of the comma-prefixed tail shared by list0 and list1. -/
inductive EbnfCommaTailRecognizes
    (file : WorkspaceFile) (tokens : List Token) :
    EbnfExpr → Boundary tokens → Boundary tokens → Prop where
  | nil (element : EbnfExpr) (cursor : Boundary tokens) :
      EbnfCommaTailRecognizes file tokens element cursor cursor
  | cons
      (element : EbnfExpr) (start afterComma middle finish : Boundary tokens)
      (comma : MatchedTerminal file tokens (.symbol .comma))
      (commaStart : comma.cursor.beforeBoundary = start)
      (commaFinish : comma.cursor.afterBoundary = afterComma)
      (head : EbnfRecognizes file tokens element afterComma middle)
      (tail : EbnfCommaTailRecognizes file tokens element middle finish) :
      EbnfCommaTailRecognizes file tokens element start finish

end

namespace EbnfRecognizes

/-- Transport expression recognition along exact index equalities. -/
theorem transport
    {file : WorkspaceFile} {tokens : List Token}
    {left right : EbnfExpr}
    {leftStart leftFinish rightStart rightFinish : Boundary tokens}
    (expression : left = right) (start : leftStart = rightStart)
    (finish : leftFinish = rightFinish)
    (recognized : EbnfRecognizes file tokens left leftStart leftFinish) :
    EbnfRecognizes file tokens right rightStart rightFinish := by
  subst right
  subst rightStart
  subst rightFinish
  exact recognized

end EbnfRecognizes

end Solcore.Surface.Multi
