import Solcore.Resolved.Expr

set_option autoImplicit false

namespace Solcore.Resolved

/-- Type-independent local scope validity. Every syntactic branch must be
scoped. A binder extends only its body, and repeated identities are permitted. -/
inductive WellScoped : List LocalId → Expr → Prop where
  | unit {scope} : WellScoped scope .unit
  | bool {scope value} : WellScoped scope (.bool value)
  | word {scope value} : WellScoped scope (.word value)
  | var {scope id} : id ∈ scope → WellScoped scope (.var id)
  | pair {scope left right} :
      WellScoped scope left → WellScoped scope right →
      WellScoped scope (.pair left right)
  | unary {scope op operand} :
      WellScoped scope operand → WellScoped scope (.unary op operand)
  | binary {scope op left right} :
      WellScoped scope left → WellScoped scope right →
      WellScoped scope (.binary op left right)
  | wordLt {scope left right} :
      WellScoped scope left → WellScoped scope right → WellScoped scope (.wordLt left right)
  | letE {scope binder value body} :
      WellScoped scope value → WellScoped (binder :: scope) body →
      WellScoped scope (.letE binder value body)
  | ifE {scope condition thenBranch elseBranch} :
      WellScoped scope condition → WellScoped scope thenBranch →
      WellScoped scope elseBranch →
      WellScoped scope (.ifE condition thenBranch elseBranch)

end Solcore.Resolved
