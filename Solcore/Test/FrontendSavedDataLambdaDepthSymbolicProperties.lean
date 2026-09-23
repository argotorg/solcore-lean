import Solcore.Frontend.SavedDataLambdaDepth

/- Independent original creation, first pickup, caller argument and saved fresh
body witnesses precede depth laws. Creation and invocation stores are separate.
The fixed caller f(x) does not bound arbitrarily nested saved runtime syntax;
all results are whole mixed values/stores, not Core costs or runtime typings. -/
set_option autoImplicit false
namespace Tests.SavedDataLambdaDepthSymbolic
open Solcore Solcore.Frontend
private abbrev E := ClosedSourceExpressionEvaluates
private def ref (s : Syntax.SourceSpan) (name : Syntax.Identifier) : Syntax.Expr := ⟨s,.identifier name⟩
private def nestedStatement (s : Syntax.SourceSpan) (name : Syntax.Identifier) : Nat → Syntax.Statement
  | 0 => ⟨s,.returnStmt (some (ref s name))⟩
  | n+1 => ⟨s,.block [nestedStatement s name n]⟩
private def nested (s : Syntax.SourceSpan) (name : Syntax.Identifier) (n : Nat) : Syntax.Block :=
  ⟨s,[nestedStatement s name n]⟩
private def lambda (s : Syntax.SourceSpan) (name : Syntax.Identifier)
    (pa annotation : Option Syntax.TypeExpr) (body : Syntax.Block) : Syntax.Expr :=
  ⟨s,.lambda s ⟨s,[⟨s,match pa with
    | none => .inferred name | some t => .typed none name t⟩]⟩ annotation body⟩
private def call (s : Syntax.SourceSpan) (callee argument : Syntax.Identifier) : Syntax.Expr :=
  ⟨s,.call (ref s callee) ⟨s,[ref s argument]⟩⟩
private theorem shape (s : Syntax.SourceSpan) (name : Syntax.Identifier)
    (pa annotation : Option Syntax.TypeExpr) (body : Syntax.Block) :
    SourceUnaryLambdaShape (lambda s name pa annotation body) name body := by
  cases pa with | none => exact .inferred | some t => exact .typed
private theorem nested_original {s name n owner names captured store id value}
    (named : LocalNameTable.Lookup names name.value id)
    (found : Resolved.LocalScope.Lookup captured id value) :
    ClosedSourceBodyEvaluates owner names captured store (nested s name n) value store := by
  induction n with | zero => exact .expression (.reference named found) | succ n ih => exact .block ih
private theorem reference_run (s : Syntax.SourceSpan) (name : Syntax.Identifier) (budget : Nat)
    (owner : Resolved.DeclarationId) (names : LocalNameTable) (captured : Resolved.LocalScope RuntimeValue)
    (store : List RuntimeValue) (id : Resolved.LocalId) (value : RuntimeValue)
    (named : LocalNameTable.Lookup names name.value id) (found : Resolved.LocalScope.Lookup captured id value) :
    evaluateClosedSourceExpression? (budget+1) owner names captured store (ref s name) = some (value,store) := by
  simp [ref,evaluateClosedSourceExpression?,LocalNameTable.lookup?_iff.mpr named,Resolved.LocalScope.lookup?_iff.mpr found]
private theorem nested_run (s : Syntax.SourceSpan) (name : Syntax.Identifier) (n budget : Nat)
    (owner : Resolved.DeclarationId) (names : LocalNameTable) (captured : Resolved.LocalScope RuntimeValue)
    (store : List RuntimeValue) (id : Resolved.LocalId) (value : RuntimeValue)
    (named : LocalNameTable.Lookup names name.value id) (found : Resolved.LocalScope.Lookup captured id value) :
    evaluateClosedSourceBody? budget owner names captured store (nested s name n) =
      if n+2 ≤ budget then some (value,store) else none := by
  induction n generalizing budget with
  | zero =>
      cases budget with
      | zero => simp [evaluateClosedSourceBody?]
      | succ budget =>
          cases budget with
          | zero => simp [nested,nestedStatement,evaluateClosedSourceBody?,evaluateClosedSourceExpression?]
          | succ budget =>
              simpa only [nested,nestedStatement,evaluateClosedSourceBody?,Nat.zero_add,Nat.reduceAdd,
                show 2 ≤ budget+1+1 by omega,↓reduceIte] using
                reference_run s name budget owner names captured store id value named found
  | succ n ih =>
      cases budget with
      | zero => simp [evaluateClosedSourceBody?]
      | succ budget =>
          have arithmetic : (n+1+2 ≤ budget+1) ↔ n+2 ≤ budget := by omega
          simpa only [nested,nestedStatement,evaluateClosedSourceBody?,arithmetic] using ih budget
private theorem nested_gate (s : Syntax.SourceSpan) (name : Syntax.Identifier) (n : Nat) :
    ClosedSourceDataBody (nested s name n) := by
  induction n with | zero => exact .expression .reference | succ n ih => exact .block ih
private theorem nested_depth (s : Syntax.SourceSpan) (name : Syntax.Identifier) (n : Nat) :
    closedSourceDataBodyDepthBound (nested s name n) = n+2 := by
  induction n with
  | zero => simp [nested,nestedStatement,ref,closedSourceDataBodyDepthBound,closedSourceDataDepthBound]
  | succ n ih => simpa only [nested,nestedStatement,closedSourceDataBodyDepthBound,Nat.add_right_comm] using congrArg (·+1) ih
private theorem sharp_run (s : Syntax.SourceSpan) (parameter callee argument : Syntax.Identifier)
    (pa annotation : Option Syntax.TypeExpr) (n budget : Nat)
    (callerOwner savedOwner : Resolved.DeclarationId) (callerNames savedNames : LocalNameTable)
    (callerCaptured savedCaptured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    (calleeId argumentId : Resolved.LocalId) (value : RuntimeValue)
    (named : LocalNameTable.Lookup callerNames callee.value calleeId)
    (found : Resolved.LocalScope.Lookup callerCaptured calleeId
      (.sourceClosure (lambda s parameter pa annotation (nested s parameter n)) savedOwner savedNames savedCaptured))
    (argumentNamed : LocalNameTable.Lookup callerNames argument.value argumentId)
    (argumentFound : Resolved.LocalScope.Lookup callerCaptured argumentId value) :
    evaluateClosedSourceExpression? budget callerOwner callerNames callerCaptured store (call s callee argument) =
      if n+3 ≤ budget then some (value,store) else none := by
  cases budget with
  | zero => simp [evaluateClosedSourceExpression?]
  | succ budget =>
      cases budget with
      | zero => simp [call,evaluateClosedSourceExpression?]
      | succ budget =>
          have picked := reference_run s callee budget callerOwner callerNames callerCaptured store _ _ named found
          have actualArg := reference_run s argument budget callerOwner callerNames callerCaptured store _ _ argumentNamed argumentFound
          have returned := nested_run s parameter n (budget+1) savedOwner
            ((parameter.value,Resolved.freshLocalId savedOwner (savedNames.map Prod.snd))::savedNames)
            ((Resolved.freshLocalId savedOwner (savedNames.map Prod.snd),value)::savedCaptured) store
            (Resolved.freshLocalId savedOwner (savedNames.map Prod.snd)) value .head .head
          have arithmetic : (n+3 ≤ budget+1+1) ↔ n+2 ≤ budget+1 := by omega
          simpa only [call,evaluateClosedSourceExpression?,picked,actualArg,
            sourceUnaryLambdaShape?_iff.mpr (shape s parameter pa annotation (nested s parameter n)),
            arithmetic,bind,Option.bind_some] using returned

/-- Caller argument lookup and saved fresh-body lookup remain separate, as do
creation and invocation stores. An arbitrary saved nest has sharp depth n+3. -/
theorem saved_body_nesting_has_sharp_depth
    (s : Syntax.SourceSpan) (parameter callee argument : Syntax.Identifier)
    (pa annotation : Option Syntax.TypeExpr) (n extra : Nat)
    (callerOwner savedOwner : Resolved.DeclarationId) (callerNames savedNames : LocalNameTable)
    (callerCaptured savedCaptured : Resolved.LocalScope RuntimeValue)
    (creationStore invocationStore : List RuntimeValue) (calleeId argumentId : Resolved.LocalId) (value : RuntimeValue)
    (named : LocalNameTable.Lookup callerNames callee.value calleeId)
    (found : Resolved.LocalScope.Lookup callerCaptured calleeId
      (.sourceClosure (lambda s parameter pa annotation (nested s parameter n)) savedOwner savedNames savedCaptured))
    (argumentNamed : LocalNameTable.Lookup callerNames argument.value argumentId)
    (argumentFound : Resolved.LocalScope.Lookup callerCaptured argumentId value) :
    let body := nested s parameter n
    let source := lambda s parameter pa annotation body
    let application := call s callee argument
    E savedOwner savedNames savedCaptured creationStore source (.sourceClosure source savedOwner savedNames savedCaptured) creationStore ∧
    E callerOwner callerNames callerCaptured invocationStore (ref s callee)
      (.sourceClosure source savedOwner savedNames savedCaptured) invocationStore ∧
    E callerOwner callerNames callerCaptured invocationStore (ref s argument) value invocationStore ∧
    E callerOwner callerNames callerCaptured invocationStore application value invocationStore ∧
    (∀ budget, evaluateClosedSourceExpression? budget callerOwner callerNames callerCaptured invocationStore application =
      if n+3 ≤ budget then some (value,invocationStore) else none) ∧
    savedDataLambdaDepthBound (ref s argument) body = n+3 ∧
    evaluateClosedSourceExpression? (n+3+extra) callerOwner callerNames callerCaptured invocationStore application =
      some (value,invocationStore) ∧
    evaluateClosedSourceExpression? (n+3+extra) callerOwner callerNames callerCaptured invocationStore application =
      evaluateClosedSourceExpression? (savedDataLambdaDepthBound (ref s argument) body)
        callerOwner callerNames callerCaptured invocationStore application ∧
    (∀ actual final, evaluateClosedSourceExpression? (n+3+extra) callerOwner callerNames callerCaptured invocationStore application =
      some (actual,final) ↔ actual=value ∧ final=invocationStore) ∧
    evaluateClosedSourceExpression? (savedDataLambdaDepthBound (ref s argument) body)
      callerOwner callerNames callerCaptured invocationStore application ≠ none ∧
    ¬ (∀ budget, evaluateClosedSourceExpression? budget callerOwner callerNames callerCaptured invocationStore application = none) := by
  intro body source application
  have shaped := shape s parameter pa annotation body
  have creation : E savedOwner savedNames savedCaptured creationStore source
      (.sourceClosure source savedOwner savedNames savedCaptured) creationStore := .creation shaped
  have picked : E callerOwner callerNames callerCaptured invocationStore (ref s callee)
      (.sourceClosure source savedOwner savedNames savedCaptured) invocationStore := .reference named found
  have actualArg : E callerOwner callerNames callerCaptured invocationStore (ref s argument) value invocationStore :=
    .reference argumentNamed argumentFound
  have original : E callerOwner callerNames callerCaptured invocationStore application value invocationStore :=
    .call shaped picked actualArg (nested_original .head .head)
  have ran := fun budget => sharp_run s parameter callee argument pa annotation n budget callerOwner savedOwner
    callerNames savedNames callerCaptured savedCaptured invocationStore calleeId argumentId value named found argumentNamed argumentFound
  have ag : ClosedSourceDataExpression (ref s argument) := .reference
  have bg := nested_gate s parameter n
  have bound : savedDataLambdaDepthBound (ref s argument) body = n+3 := by
    simp only [savedDataLambdaDepthBound,ref,closedSourceDataDepthBound,body,nested_depth]; omega
  have enough : savedDataLambdaDepthBound (ref s argument) body ≤ n+3+extra := by omega
  have nonempty : evaluateClosedSourceExpression? (savedDataLambdaDepthBound (ref s argument) body)
      callerOwner callerNames callerCaptured invocationStore application ≠ none := by
    intro absent
    exact ((savedDataLambda_evaluate_depth_none_iff shaped ag bg named found (Nat.le_refl _)).mp absent) _ _ original
  have notAll : ¬ (∀ budget, evaluateClosedSourceExpression? budget callerOwner callerNames callerCaptured invocationStore application = none) := by
    intro absent
    exact nonempty ((savedDataLambda_evaluate_depth_none_iff_all_budgets shaped ag bg named found).mpr absent)
  refine ⟨creation,picked,actualArg,original,ran,bound,
    savedDataLambda_evaluates_at_depthBound shaped ag bg named found original enough,
    savedDataLambda_evaluate_depth_stable shaped ag bg named found enough,?_,nonempty,notAll⟩
  intro actual final
  have raw : evaluateClosedSourceExpression? (n+3+extra) callerOwner callerNames callerCaptured invocationStore application =
      some (actual,final) ↔ E callerOwner callerNames callerCaptured invocationStore application actual final :=
    savedDataLambda_evaluate_at_depthBound_iff shaped ag bg named found enough
  exact raw.trans ⟨fun other => other.deterministic original,by rintro ⟨rfl,rfl⟩; exact original⟩

/-- A fixed f(x) AST defeats every caller-syntax-only candidate bound when the
saved body may vary. Only the saved datum changes with n, not caller syntax. -/
theorem no_caller_syntax_only_bound
    (s : Syntax.SourceSpan) (parameter : Syntax.Identifier) (pa annotation : Option Syntax.TypeExpr)
    (callerOwner savedOwner : Resolved.DeclarationId) (savedNames : LocalNameTable)
    (savedCaptured : Resolved.LocalScope RuntimeValue) (creationStore invocationStore : List RuntimeValue)
    (value : RuntimeValue) (candidate : Syntax.Expr → Nat) :
    let callee : Syntax.Identifier := ⟨s,"f"⟩
    let argument : Syntax.Identifier := ⟨s,"x"⟩
    let fid : Resolved.LocalId := ⟨callerOwner,0⟩
    let aid : Resolved.LocalId := ⟨callerOwner,1⟩
    let callerNames := [("f",fid),("x",aid),("f",aid),("x",fid)]
    let application := call s callee argument
    ∃ n,
      let source := lambda s parameter pa annotation (nested s parameter n)
      let saved := RuntimeValue.sourceClosure source savedOwner savedNames savedCaptured
      let captured := [(fid,saved),(fid,.unit),(aid,value),(aid,.bool false)]
      E savedOwner savedNames savedCaptured creationStore source saved creationStore ∧
      E callerOwner callerNames captured invocationStore (ref s callee) saved invocationStore ∧
      E callerOwner callerNames captured invocationStore application value invocationStore ∧
      evaluateClosedSourceExpression? (candidate application) callerOwner callerNames captured invocationStore application = none ∧
      evaluateClosedSourceExpression? (n+3) callerOwner callerNames captured invocationStore application = some (value,invocationStore) := by
  intro callee argument fid aid callerNames application
  refine ⟨candidate application,?_⟩
  intro source saved captured
  have shaped := shape s parameter pa annotation (nested s parameter (candidate application))
  have named : LocalNameTable.Lookup callerNames callee.value fid := .head
  have found : Resolved.LocalScope.Lookup captured fid saved := .head
  have an : LocalNameTable.Lookup callerNames argument.value aid := .tail (by change "f" ≠ "x"; decide) .head
  have af : Resolved.LocalScope.Lookup captured aid value :=
    .tail (by dsimp only [aid,fid]; intro impossible; cases impossible)
      (.tail (by dsimp only [aid,fid]; intro impossible; cases impossible) .head)
  have creation : E savedOwner savedNames savedCaptured creationStore source saved creationStore := .creation shaped
  have picked : E callerOwner callerNames captured invocationStore (ref s callee) saved invocationStore := .reference named found
  have original : E callerOwner callerNames captured invocationStore application value invocationStore :=
    .call shaped picked (.reference an af) (nested_original .head .head)
  have ran := fun budget => sharp_run s parameter callee argument pa annotation (candidate application) budget
    callerOwner savedOwner callerNames savedNames captured savedCaptured invocationStore fid aid value named found an af
  refine ⟨creation,picked,original,?_,?_⟩
  · simpa only [show ¬ candidate application+3 ≤ candidate application by omega,↓reduceIte] using ran (candidate application)
  · simpa only [Nat.le_refl,↓reduceIte] using ran (candidate application+3)

end Tests.SavedDataLambdaDepthSymbolic
