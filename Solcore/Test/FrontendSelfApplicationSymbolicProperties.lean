import Solcore.Frontend.SelfApplicationCallNonreturnProperties

/- Original creations and successful input references precede non-return laws.
Typed parameters remain inert syntax; no typing or live host/cell claim is made. -/
set_option autoImplicit false
namespace Tests.SelfApplicationSymbolic
open Solcore Solcore.Frontend
private abbrev E := ClosedSourceExpressionEvaluates
private abbrev B := ClosedSourceBodyEvaluates
private def ref (s : Syntax.SourceSpan) (p : Syntax.Identifier) : Syntax.Expr := ⟨s,.identifier p⟩
private def app (s t : Syntax.SourceSpan) (f x : Syntax.Expr) : Syntax.Expr := ⟨s,.call f ⟨t,[x]⟩⟩
private def loopBody (s t : Syntax.SourceSpan) (p : Syntax.Identifier) : Syntax.Block :=
  ⟨s,[⟨s,.returnStmt (some (app s t (ref s p) (ref t p)))⟩]⟩
private def identityBody (s t : Syntax.SourceSpan) (p : Syntax.Identifier) : Syntax.Block :=
  ⟨s,[⟨s,.returnStmt (some (ref t p))⟩]⟩
private def lambda (s : Syntax.SourceSpan) (p : Syntax.Identifier)
    (pa ra : Option Syntax.TypeExpr) (body : Syntax.Block) : Syntax.Expr :=
  ⟨s,.lambda s ⟨s,[⟨s,match pa with | none => .inferred p | some a => .typed none p a⟩]⟩ ra body⟩
private theorem shape (s : Syntax.SourceSpan) (p : Syntax.Identifier)
    (pa ra : Option Syntax.TypeExpr) (body : Syntax.Block) :
    SourceUnaryLambdaShape (lambda s p pa ra body) p body := by
  cases pa <;> constructor
private def freshNames (owner : Resolved.DeclarationId) (names : LocalNameTable) (p : Syntax.Identifier) :=
  (p.value,Resolved.freshLocalId owner (names.map Prod.snd))::names
private def freshCaptured (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (value : RuntimeValue) :=
  (Resolved.freshLocalId owner (names.map Prod.snd),value)::captured
private theorem created_run {source p body} (sh : SourceUnaryLambdaShape source p body)
    (owner : Resolved.DeclarationId) (names : LocalNameTable) (captured : Resolved.LocalScope RuntimeValue)
    (store : List RuntimeValue) (n : Nat) :
    evaluateClosedSourceExpression? (n+1) owner names captured store source =
      some (.sourceClosure source owner names captured,store) := by
  cases sh <;> simp only [evaluateClosedSourceExpression?,sourceUnaryLambdaShape?,bind,Option.bind_some,pure]

/-- Saved self-inputs succeed independently, including arbitrary finite mixed lexical rows. -/
theorem saved_self_application_has_successful_inputs
    (s t : Syntax.SourceSpan) (p f x : Syntax.Identifier) (pa ra : Option Syntax.TypeExpr)
    (co so : Resolved.DeclarationId) (cn sn : LocalNameTable) (cc sc : Resolved.LocalScope RuntimeValue)
    (creationStore store : List RuntimeValue) (fid xid : Resolved.LocalId)
    (fn : LocalNameTable.Lookup cn f.value fid)
    (fv : Resolved.LocalScope.Lookup cc fid (.sourceClosure (lambda s p pa ra (loopBody s t p)) so sn sc))
    (xn : LocalNameTable.Lookup cn x.value xid)
    (xv : Resolved.LocalScope.Lookup cc xid (.sourceClosure (lambda s p pa ra (loopBody s t p)) so sn sc)) :
    let source := lambda s p pa ra (loopBody s t p)
    let saved := RuntimeValue.sourceClosure source so sn sc
    E so sn sc creationStore source saved creationStore ∧
    E co cn cc store (ref s f) saved store ∧ E co cn cc store (ref t x) saved store ∧
    (∀ n, evaluateClosedSourceExpression? (n+1) co cn cc store (ref s f) = some (saved,store) ∧
      evaluateClosedSourceExpression? (n+1) co cn cc store (ref t x) = some (saved,store)) ∧
    (∀ n, evaluateClosedSourceBody? (n+3) so (freshNames so sn p) (freshCaptured so sn sc saved) store (loopBody s t p) =
      evaluateClosedSourceBody? (n+1) so (freshNames so sn p) (freshCaptured so sn sc saved) store (loopBody s t p)) ∧
    (∀ budget, evaluateClosedSourceBody? budget so (freshNames so sn p) (freshCaptured so sn sc saved) store (loopBody s t p) = none) ∧
    (∀ value final, ¬ B so (freshNames so sn p) (freshCaptured so sn sc saved) store (loopBody s t p) value final) ∧
    (∀ budget, evaluateClosedSourceExpression? budget co cn cc store (app s t (ref s f) (ref t x)) = none) ∧
    (∀ value final, ¬ E co cn cc store (app s t (ref s f) (ref t x)) value final) := by
  let source := lambda s p pa ra (loopBody s t p)
  have sh : SourceUnaryLambdaShape source p (loopBody s t p) := shape s p pa ra _
  have created : E so sn sc creationStore source (.sourceClosure source so sn sc) creationStore := .creation sh
  have picked : E co cn cc store (ref s f) (.sourceClosure source so sn sc) store := .reference fn fv
  have supplied : E co cn cc store (ref t x) (.sourceClosure source so sn sc) store := .reference xn xv
  have children (n : Nat) :
      evaluateClosedSourceExpression? (n+1) co cn cc store (ref s f) = some (.sourceClosure source so sn sc,store) ∧
      evaluateClosedSourceExpression? (n+1) co cn cc store (ref t x) = some (.sourceClosure source so sn sc,store) := by
    constructor <;> simp only [ref,evaluateClosedSourceExpression?,LocalNameTable.lookup?_iff.mpr fn,
      LocalNameTable.lookup?_iff.mpr xn,Resolved.LocalScope.lookup?_iff.mpr fv,
      Resolved.LocalScope.lookup?_iff.mpr xv,bind,Option.bind_some,pure,source]
  have self : SourceSelfApplicationBody (loopBody s t p) p := .returning rfl rfl
  refine ⟨created,picked,supplied,children,?_,?_,?_,?_,?_⟩
  · exact selfApplicationBody_depth_reentry sh self so sn sc store
  · exact selfApplicationBody_none sh self so sn sc store
  · exact selfApplicationBody_no_original sh self so sn sc store
  · exact savedSelfApplication_none sh self so sn sc co cn cc store s t s t f x fid xid fn fv xn xv
  · exact savedSelfApplication_no_original sh self so sn sc co cn cc store s t s t f x fid xid fn fv xn xv

/-- Distinct source occurrences and parameter spellings require no closure identity assumption. -/
theorem separately_created_self_callers_do_not_return
    (s t u v : Syntax.SourceSpan) (p q : Syntax.Identifier) (lpa lra rpa rra : Option Syntax.TypeExpr)
    (owner : Resolved.DeclarationId) (names : LocalNameTable) (captured : Resolved.LocalScope RuntimeValue)
    (store : List RuntimeValue) :
    let left := lambda s p lpa lra (loopBody s t p)
    let right := lambda u q rpa rra (loopBody u v q)
    let saved := RuntimeValue.sourceClosure right owner names captured
    E owner names captured store left (.sourceClosure left owner names captured) store ∧
    E owner names captured store right saved store ∧
    (∀ n, evaluateClosedSourceExpression? (n+1) owner names captured store left = some (.sourceClosure left owner names captured,store) ∧
      evaluateClosedSourceExpression? (n+1) owner names captured store right = some (saved,store)) ∧
    E owner (freshNames owner names p) (freshCaptured owner names captured saved) store (ref s p) saved store ∧
    E owner (freshNames owner names p) (freshCaptured owner names captured saved) store (ref t p) saved store ∧
    (∀ n, evaluateClosedSourceBody? (n+3) owner (freshNames owner names p) (freshCaptured owner names captured saved) store (loopBody s t p) =
      evaluateClosedSourceBody? (n+1) owner (freshNames owner names q) (freshCaptured owner names captured saved) store (loopBody u v q)) ∧
    (∀ budget, evaluateClosedSourceBody? budget owner (freshNames owner names p) (freshCaptured owner names captured saved) store (loopBody s t p) = none) ∧
    (∀ budget, evaluateClosedSourceExpression? budget owner names captured store (app s t left right) = none) ∧
    (∀ value final, ¬ E owner names captured store (app s t left right) value final) := by
  let left := lambda s p lpa lra (loopBody s t p)
  let right := lambda u q rpa rra (loopBody u v q)
  have ls : SourceUnaryLambdaShape left p (loopBody s t p) := shape s p lpa lra _
  have rs : SourceUnaryLambdaShape right q (loopBody u v q) := shape u q rpa rra _
  have madeLeft : E owner names captured store left (.sourceClosure left owner names captured) store := .creation ls
  have madeRight : E owner names captured store right (.sourceClosure right owner names captured) store := .creation rs
  have children (n : Nat) := And.intro (created_run ls owner names captured store n) (created_run rs owner names captured store n)
  have picked : E owner (freshNames owner names p) (freshCaptured owner names captured (.sourceClosure right owner names captured))
      store (ref s p) (.sourceClosure right owner names captured) store := .reference .head .head
  have supplied : E owner (freshNames owner names p) (freshCaptured owner names captured (.sourceClosure right owner names captured))
      store (ref t p) (.sourceClosure right owner names captured) store := .reference .head .head
  have li : SourceSelfApplicationBody (loopBody s t p) p := .returning rfl rfl
  have ri : SourceSelfApplicationBody (loopBody u v q) q := .returning rfl rfl
  refine ⟨madeLeft,madeRight,children,picked,supplied,?_,?_,?_,?_⟩
  · exact selfApplicationBody_calls_bound_closure rs li owner owner names names captured captured store
  · exact selfApplicationBody_boundSelf_none rs ri li owner owner names names captured captured store
  · exact directSelfApplication_none ls li rs ri owner names captured store s t
  · exact directSelfApplication_no_original ls li rs ri owner names captured store s t

/-- Returning the looping closure is successful; skipping its self-call also succeeds. -/
theorem identity_and_short_circuit_contrast
    (s t : Syntax.SourceSpan) (p q flag : Syntax.Identifier) (pa ra : Option Syntax.TypeExpr)
    (owner : Resolved.DeclarationId) (names : LocalNameTable) (captured : Resolved.LocalScope RuntimeValue)
    (store : List RuntimeValue) (flagId : Resolved.LocalId)
    (named : LocalNameTable.Lookup names flag.value flagId)
    (found : Resolved.LocalScope.Lookup captured flagId (.bool false)) :
    let identity := lambda s p pa ra (identityBody s t p)
    let loop := lambda t q pa ra (loopBody t s q)
    let saved := RuntimeValue.sourceClosure loop owner names captured
    let nonreturn := app s t loop loop
    let skipped : Syntax.Expr := ⟨s,.binary (ref s flag) ⟨t,.logicalAnd⟩ nonreturn⟩
    ¬ SourceSelfApplicationBody (identityBody s t p) p ∧
    E owner names captured store (app s t identity loop) saved store ∧
    evaluateClosedSourceExpression? 2 owner names captured store (app s t identity loop) = none ∧
    evaluateClosedSourceExpression? 3 owner names captured store (app s t identity loop) = some (saved,store) ∧
    E owner names captured store skipped (.bool false) store ∧
    evaluateClosedSourceExpression? 1 owner names captured store skipped = none ∧
    evaluateClosedSourceExpression? 2 owner names captured store skipped = some (.bool false,store) ∧
    (∀ budget, evaluateClosedSourceExpression? budget owner names captured store nonreturn = none) := by
  let identity := lambda s p pa ra (identityBody s t p)
  let loop := lambda t q pa ra (loopBody t s q)
  have is : SourceUnaryLambdaShape identity p (identityBody s t p) := shape s p pa ra _
  have ls : SourceUnaryLambdaShape loop q (loopBody t s q) := shape t q pa ra _
  have madeIdentity : E owner names captured store identity (.sourceClosure identity owner names captured) store := .creation is
  have madeLoop : E owner names captured store loop (.sourceClosure loop owner names captured) store := .creation ls
  have returned : B owner (freshNames owner names p)
      (freshCaptured owner names captured (.sourceClosure loop owner names captured)) store
      (identityBody s t p) (.sourceClosure loop owner names captured) store := .expression (.reference .head .head)
  have identityOriginal : E owner names captured store (app s t identity loop) (.sourceClosure loop owner names captured) store :=
    .call is madeIdentity madeLoop returned
  have left : E owner names captured store (ref s flag) (.bool false) store := .reference named found
  have skipped : E owner names captured store ⟨s,.binary (ref s flag) ⟨t,.logicalAnd⟩ (app s t loop loop)⟩ (.bool false) store :=
    .andFalse left
  have identityRuns : evaluateClosedSourceExpression? 2 owner names captured store (app s t identity loop) = none ∧
      evaluateClosedSourceExpression? 3 owner names captured store (app s t identity loop) = some (.sourceClosure loop owner names captured,store) := by
    cases pa <;> simp [app,identity,loop,lambda,identityBody,ref,evaluateClosedSourceExpression?,evaluateClosedSourceBody?,
      sourceUnaryLambdaShape?,LocalNameTable.lookup?,Resolved.LocalScope.lookup?]
  have skippedRuns :
      evaluateClosedSourceExpression? 1 owner names captured store ⟨s,.binary (ref s flag) ⟨t,.logicalAnd⟩ (app s t loop loop)⟩ = none ∧
      evaluateClosedSourceExpression? 2 owner names captured store ⟨s,.binary (ref s flag) ⟨t,.logicalAnd⟩ (app s t loop loop)⟩ = some (.bool false,store) := by
    simp [ref,evaluateClosedSourceExpression?,LocalNameTable.lookup?_iff.mpr named,Resolved.LocalScope.lookup?_iff.mpr found]
  have notSelf : ¬ SourceSelfApplicationBody (identityBody s t p) p := by intro impossible; cases impossible
  have self : SourceSelfApplicationBody (loopBody t s q) q := .returning rfl rfl
  exact ⟨notSelf,identityOriginal,identityRuns.1,identityRuns.2,skipped,skippedRuns.1,skippedRuns.2,
    directSelfApplication_none ls self ls self owner names captured store s t⟩

end Tests.SelfApplicationSymbolic
